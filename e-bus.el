;;; ebus.el --- Pure Elisp implementation of D-Bus -*- lexical-binding: t -*-

;; Author: Will Dey
;; Maintainer: Will Dey
;; Version: 1.0.0
;; Package-Requires: ((rec-mode "1.9.0"))
;; Homepage: homepage
;; Keywords: keywords


;; This file is not part of GNU Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; commentary

;; Relevant for passing file descriptors (needed for BlueZ, for example): https://lists.gnu.org/archive/html/emacs-devel/2016-09/msg00266.html
;; Maybe make a "file descriptor owner" subprocess which gets passed file descriptor for connection and owns

;; Only support AUTH EXTERNAL through Unix domain sockets

;; Try to let Emacs dbus library handle responses via library when possible and keep original struct bytes intact for forwarding

(require 'bindat)
(require 'pcase)
(require 'seq)
(require 'gv)
(require 'cl-lib)
(require 'semantic/wisent)

(defgroup ebus
  :group 'dbus)

;; Assume that if a client can connect to `ebus-socket', they have the appropriate permissions and are already authenticated
(defcustom ebus-socket (getenv "DBUS_SESSION_BUS_ADDRESS")
  "")

(defcustom ebus-log-buffer "*E-Bus*"
  ""
  :type 'string)

(defvar ebus-client-prefix " *E-Bus client*")

(defcustom ebus-authentication-failure-limit 20
  "")

(defcustom ebus-use-threads (featurep 'threads)
  ""
  :type 'boolean)

(define-error 'ebus-error "E-Bus received invalid message from client")


;;; Marshaling

;;;; Basic types
(bindat-defmacro ebus-boolean (le)
  `(struct
    :pack-var b
    (uint 32 ,le :pack-val (if b 1 0))
    :unpack-val (pcase b
		  (0 nil)
		  (1 t)
		  (_ (signal 'ebus-error
			     (format-message "Invalid boolean value `%S' provided" b))))))

;; From https://github.com/skeeto/bitpack, which is in the public domain: 
(defun ebus--unpack-double (bytes)
  (let* ((negp (= #x80 (logand (aref bytes 0) #x80)))
         (exp (logand (logior (ash (aref bytes 0) 4) (ash (aref bytes 1) -4)) #x7ff))
         (mantissa (logior #x10000000000000
                           (ash (logand #xf (aref bytes 1)) 48)
                           (ash (aref bytes 2) 40)
                           (ash (aref bytes 3) 32)
                           (ash (aref bytes 4) 24)
                           (ash (aref bytes 5) 16)
                           (ash (aref bytes 6)  8)
                           (aref bytes 7)))
         (result (if (= #x7ff exp)
                     (if (= #x10000000000000 mantissa) 1.0e+INF 0.0e+NaN)
                   (ldexp (ldexp mantissa -53) (- exp 1022)))))
    (if negp (- result) result)))

(defun ebus--pack-double (double)
  (let* ((split (frexp (abs double)))
         (fract (car split))
         (exp   (cdr split))
         (negp (< (copysign 1.0 double) 0.0))
	 biased-exp mantissa)
    (cond ((isnan double)
           (setq biased-exp #x7ff
                 mantissa #xc000000000000))
          ((> fract 1.0) ; infinity
           (setq biased-exp #x7ff
                 mantissa 0))
          ((= fract 0.0)  ; zero
           (setq biased-exp 0
                 mantissa 0))
          (t
	   (setq biased-exp (+ exp 1022)
                 mantissa (truncate (ldexp fract 53)))))
    (unibyte-string
     (if negp
	 (logior #x80 (ash biased-exp -4))
       (ash biased-exp -4))
     (logior (% (ash mantissa -48) 16)
	     (% (ash biased-exp 4) 256))
     (% (ash mantissa -40) 256)
     (% (ash mantissa -32) 256)
     (% (ash mantissa -24) 256)
     (% (ash mantissa -16) 256)
     (% (ash mantissa  -8) 256)
     (% mantissa 256))))

(bindat-defmacro ebus-double (&optional le)
  (let ((le-sym (make-symbol "le")))
    `(let ((,le-sym ,le))
       (struct
	:pack-var double
	(d str ,len-sym
	   :pack-val
	   (let ((d (ebus--pack-double double)))
	     (if ,le-sym (nreverse d) d)))
	:unpack-val
	(ebus--unpack-double
	 (if ,le-sym (nreverse d) d))))))

(defconst ebus-object-path-regex
  (rx string-start
      (or ?/ ; Root path.
	  (+ ?/
	     (+ (any (?A . ?Z)
		     (?a . ?z)
		     (?0 . ?9)
		     ?_))))
      string-start)
  "Regular expression matching valid D-Bus object paths.")
(defconst ebus-object-bindat-spec
  (bindat-type
    :pack-var o
    (o strz :pack-val o)
    :unpack-val
    (if (string-match-p o)
	o
      (signal 'ebus-error
	      (format-message "Invalid object path `%s' provided"
			      o)))))

(defvar ebus-le nil)
(defconst ebus-signature-grammar
  (wisent-compiled-grammar
   (nil
    nil
    (basic ((?y) `(u8))
	   ((?b) `(ebus-boolean ,ebus-le))
	   ((?n) `(sint 16      ,ebus-le))
	   ((?q) `(uint 16      ,ebus-le))
	   ((?i) `(sint 32      ,ebus-le))
	   ((?u) `(uint 32      ,ebus-le))
	   ((?x) `(sint 64      ,ebus-le))
	   ((?t) `(uint 64      ,ebus-le))
	   ((?d) `(ebus-double  ,ebus-le))
	   ((?h) `(uint 32      ,ebus-le))
	   ((?s) `(strz))
	   ((?o) `(type ebus-object-bindat-spec))
	   ((?g) `(type ebus-signature-bindat-spec)))
    (type ((basic))
	  ((array))
	  ((struct))
	  ((variant))
	  ((dict)))
    (types ((type)
	    (list $1))
	   ((type types)
	    (cons $1 $2)))
    (array ((?a type)
	    `(ebus-array ,$2 ,ebus-le)))
    (struct ((?\( types ?\))
	     (cons 'struct
		   (seq-map-indexed
		    (lambda (type i)
		      (cons (intern (format "field%d" i)) type))
		    $2))))
    (variant ((?v) `(type ebus-variant-bindat-spec)))
    (dict ((?a ?\{ basic type ?\})
	   `(ebus-dict ,$2 ,$3 ,ebus-le))))
   (types)))
(defun ebus-signature-to-bindat (signature &optional le)
  "SIGNATURE is a D-Bus signature of one or more complete types.

Returns a Bindat type expression."
  (let ((tokens (string-to-list signature))
	(ebus-le le))
    (wisent-parse
     ebus-signature-grammar
     (lambda ()
       (list (or (pop tokens)
		 wisent-eoi-term))))))
(bindat-defmacro ebus-signature-bindat-spec (le)
  `(struct
    (s strz)
    :unpack-val (ebus-signature-to-bindat s ,le)))

;;;; Containers
(defun ebus-alignment (&rest type)
  "TYPE is a Bindat type expression"
  (pcase type
    ((seq (or 'struct
	      (pred consp)))
     ;; Struct:
     8)
    ((seq 'uint bitlen)
     (/ bitlen 8))
    ((seq 'ebus-double)
     8)
    (_ 1)))

(bindat-defmacro ebus-aligned (type le)
  )

(bindat-defmacro ebus-array (type le)
  `(struct
    :pack-var a
    (length uint 32 ,le
	    :pack-val (length a))
    (_      align (ebus-alignment ,type))
    (a      vec length ,type
	    :pack-val (seq-into a 'vector))
    :unpack-val a))

(defconst ebus-variant-bindat-spec
  (bindat-type
    :pack-var v
    (signature type ebus-signature-bindat-spec)
    (_         align (ebus-alignment signature))
    (v         signature
	       :pack-val (bindat-pack signature v))
    :unpack-val v))

(bindat-defmacro ebus-dict (key value &optional le)
  `(struct
    (a ebus-array
       (struct
	:pack-var entry
	(key   ,@key   :pack-val (car entry))
	(value ,@value :pack-val (cdr entry))
	:unpack-val (cons key value))
       ,le)
    :unpack-val (seq-into a 'list)))


;;; Message protocol

(defconst ebus-header-fields
  [invalid
   path
   interface
   member
   error-name
   reply-serial
   destination
   sender
   signature
   unix-fds])

(defconst ebus-message-bindat-spec
  (bindat-type
    (endianness   u8)
    (le           unit
		  (setq ebus-le (pcase endianness
				  (?l t)
				  (?B nil)
				  (_ (signal 'ebus-error
					     (format-message "Invalid endianness marker `%c'"
							     endianness))))))
    (message-type u8)
    (flags        u8)
    (version      u8)
    (length       uint 32 le)
    (serial       uint 32 le)
    ;; TODO replace with ebus-dict
    (fields       ebus-dict
		  (struct
		   :pack-var key
		   (code u8
			 :pack-val
			 (let ((index (seq-position ebus-header-fields key #'eq)))
			   (if (and number (> number 0))
			       index
			     (error "`%S' is not a D-Bus header field" key))))
		   :unpack-val
		   (pcase code
		     (0                      (signal 'ebus-error "Field with name `invalid' in message header"))
		     ((pred (<= (length a))) (signal 'ebus-error (format-message "Unknown field code %d in message header" code)))
		     (_                      (aref ebus-header-fields code))))
		  (type ebus-variant-bindat-spec)
		  le)
    (_            align 8)
    (body         bits length)))

(defvar bindat-idx)
(defvar bindat-raw)
(defun ebus--next-bindat (type)
  "TYPE is a Bindat type value"
  (condition-case nil
      ;; Manually use Bindat internals for parsing in order to move point to end of struct:
      (let* ((bindat-idx 0)
	     (bindat-raw (buffer-substring-no-properties
			  (point)
			  (point-max)))
	     (unpacked (bindat--unpack-group type))
	     (combined (cons (cons 'original
				   (buffer-substring-no-properties
				    (point)
				    (+ (point) bindat-idx)))
			     unpacked)))
	(forward-char bindat-idx)
	combined)
    (args-out-of-range
     (throw 'incomplete nil))))


;;; Authentication protocol

(defun ebus--next-line ()
  (condition-case nil
      (buffer-substring-no-properties
       (point)
       (progn
	 (search-forward "\r\n")
	 (match-beginning 0)))
    (search-failed
     (throw 'incomplete nil))))

(defun ebus--send (client string)
  (when (buffer-live-p (process-buffer client))
    (with-current-buffer (process-buffer client)
      (insert string)
      (process-send-string client string))))

(define-error 'ebus-auth "E-Bus client failed authentication" 'ebus-error)
(defun ebus--filter (client string)
  (catch 'incomplete
    (let* ((name (process-name client))
	   (client-buffer-name (concat " " name)))
      (condition-case e
	  (save-current-buffer
	    (let ((client-buffer (get-buffer client-buffer-name)))
	      (if client-buffer
		  (set-buffer client-buffer)
		;; New connection.
		;; Check if first byte is \0:
		(unless (string-prefix-p "\0" string)
		  ;; Drop connection if not:
		  (signal 'ebus-error "Did not start connection with null byte"))
		(setf string (substring string 1)
		      client-buffer (get-buffer-create client-buffer-name)
		      (process-buffer client) client-buffer)
		(set-buffer client-buffer)
		(set-buffer-multibyte nil)))
	    (save-excursion
	      (insert string))
	    (condition-case nil
		(pcase (process-get client :state)
		  ('Authenticated
		   (ebus--dispatch
		    process
		    (ebus--next-bindat ebus-message-bindat-spec)))
		  ('WaitingForAuth
		   (pcase (ebus--next-line)
		     ("AUTH"
		      (signal 'ebus-auth "No authentication mechanism selected"))
		     ((pred (string-prefix-p "AUTH EXTERNAL"))
		      ;; We have no way of verifying external credentials because Emacs discards ancillary data in message, so just assume that if client was able to connect to the socket, they have the appropriate Unix permissions and are already authenticated:
		      (process-put client :state 'WaitingForBegin)
		      (ebus--send client "OK\r\n"))
		     ((pred (string-prefix-p "AUTH"))
		      (signal 'ebus-auth "Unsupported authentication mechanism"))
		     ("BEGIN"
		      (signal 'ebus-error "Client tried to begin messaging before finishing authentication"))
		     ("ERROR"
		      (signal 'ebus-auth "Client experienced an error"))
		     (_
		      (ebus--send client "ERROR\r\n"))))
		  ('WaitingForBegin
		   (pcase (ebus--next-line)
		     ("BEGIN"
		      (process-put :state 'Authenticated))
		     ("CANCEL"
		      (signal 'ebus-auth "Authentication canceled"))
		     (_ ; Including NEGOTIATE_UNIX_FD because Emacs will discard them.
		      (ebus--send client "ERROR\r\n")))))
	      (ebus-auth
	       (process-put client :state 'WaitingForAuth)
	       (ebus--send client "REJECTED EXTERNAL\r\n")
	       (when (> (cl-incf (process-get client :rejected))
			ebus-authentication-failure-limit)
		 (signal 'ebus-error
			 (format-message "Client was rejected %d times"
					 (process-get client :rejected)))))))
	(ebus-error
	 (delete-process client)
	 (display-warning 'ebus (format-message "%s: %s; dropping connection"
						name (cdr e))))))))


;;; Message bus

(defun ebus--dispatch (client message)
  )

(defun ebus--sentinel (client event)
  (when (and (process-live-p client)
	     (or (eq (process-thread client) main-thread)
		 (thread-live-p nil)
		 (not (thread-live-p (process-thread client)))))
    (set-process-thread client
			(make-thread #'ebus-receive
				     (process-name client)))))

(defun ebus-log (server client message)
  (when (buffer-live-p (process-buffer server))
    (with-current-buffer (process-buffer server)
      (let ((moving (= (point) (process-mark server))))
	(save-excursion
	  ;; Insert the text, advancing the process marker.
	  (goto-char (process-mark server))
	  (insert (process-name client) ": ")
	  (insert message)
	  (set-marker (process-mark proc) (point)))
	(if moving
	    (goto-char (process-mark proc)))))))

;;;###autoload
(defun ebus (&optional on)
  (with-file-modes ?\700
    (make-network-process
     :name "E-Bus"
     :buffer ebus-log-buffer
     :filter ebus--filter
     :server t
     :family 'local
     :service ebus-socket
     :plist '(:state WaitingForAuth))))

(define-minor-mode ebus-mode
  :global t
  (ebus ebus-mode))

;;; e-bus.el ends here
