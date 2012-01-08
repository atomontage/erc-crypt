;;; erc-crypt.el --- Pre-shared Key Encryption for ERC

;; Copyright (C) 2011 xristos@sdf.lonestar.org
;; All rights reserved

;; Version: 0.5 - 2011-12-22
;; Author: xristos@sdf.lonestar.org
;; Keywords: application
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;;
;;   * Redistributions of source code must retain the above copyright
;;     notice, this list of conditions and the following disclaimer.
;;
;;   * Redistributions in binary form must reproduce the above
;;     copyright notice, this list of conditions and the following
;;     disclaimer in the documentation and/or other materials
;;     provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:
;;
;; Minor mode for ERC that enables the use of PSK encryption.
;;
;; An external `openssl' binary is used for the actual encryption,
;; communication with Emacs happening via `call-process-region'.
;;
;;; Usage:
;;
;; Move erc-crypt.el to a directory in your load-path
;;
;; (require 'erc-crypt)
;;
;; M-x erc-crypt-enable  ; Enable encryption for the current ERC buffer
;; M-x erc-crypt-disable ; Disable encryption for the current ERC buffer
;; M-x erc-crypt-set-key ; Set/change key for the current ERC buffer
;;
;;; Note:
;;
;; I am not a cryptographer && crypto bugs may lurk -> Use at your own risk!
;;
;;; Code:

(require 'cl)
(require 'erc)
(require 'sha1)

(define-minor-mode erc-crypt-mode
  "Toggle CBC symmetric encryption."
  nil " CRYPT" nil
  (if erc-crypt-mode
      ;; enabled
      (progn
        (add-hook 'erc-send-pre-hook 'erc-crypt-maybe-send nil t)
        (add-hook 'erc-send-modify-hook 'erc-crypt-maybe-send-fixup nil t)
        (add-hook 'erc-insert-modify-hook 'erc-crypt-maybe-insert nil t))
    ;; disabled
    (progn
      (remove-hook 'erc-send-pre-hook 'erc-crypt-maybe-send t)
      (remove-hook 'erc-send-modify-hook 'erc-crypt-maybe-send-fixup t)
      (remove-hook 'erc-insert-modify-hook 'erc-crypt-maybe-insert t))))

(defvar erc-crypt-openssl-path "openssl"
  "Path to openssl binary.")

(defvar erc-crypt-cipher "bf-cbc"
  "Cipher to use.  Default is Blowfish CBC.")

(defvar erc-crypt-indicator "☿"
  "String that is used to visually indicate encrypted messages.")

(defvar erc-crypt-success-color "PaleGreen"
  "Color that is used to indicate success.")

(defvar erc-crypt-failure-color "#ffff55"
  "Color that is used to indicate failure.")

(defvar erc-crypt-prefix "LVX"
  "String that is used as a prefix in all encrypted messages sent/received.")

(defvar erc-crypt-postfix "IAO"
  "String that is used as a postfix in all encrypted messages sent/received.")

(defvar erc-crypt-message nil
  "Holds last message sent (before it gets encrypted).
This becomes buffer-local whenever it is set.")

(make-variable-buffer-local 'erc-crypt-message)

(defvar erc-crypt-key nil
  "Key to use for encryption.
This is actually the SHA1 hash of the string that the user provides as a key.
This becomes buffer-local whenever it is set.")

(make-variable-buffer-local 'erc-crypt-key)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro* erc-crypt-with-message ((message) &rest body)
  "Macro that deals with narrowed regions as implemented by
`erc-send-modify-hook' and `erc-insert-modify-hook'.

It searches for and extracts an encrypted message (if present),
then binds MESSAGE to it, deletes the encrypted string from the
buffer and executes BODY.  Finally, ERC text properties are restored."
  (declare (indent defun))
  (let ((start (gensym)))
    `(when erc-crypt-mode
       (goto-char (point-min))
       (let ((,start nil))
         (when (re-search-forward (concat erc-crypt-prefix ".+" erc-crypt-postfix) nil t)
           (let ((,message (buffer-substring (+ (match-beginning 0) (length erc-crypt-prefix))
                                             (- (match-end 0) (length erc-crypt-postfix))))
                 (,start (match-beginning 0)))
             (delete-region (match-beginning 0) (match-end 0))
             (goto-char ,start)
             ,@body)
           (erc-restore-text-properties))))))

(defun erc-crypt-time-millis ()
  "Return current time (time since Unix epoch) in milliseconds."
  (destructuring-bind (sec-h sec-l micro) (current-time)
    (+ (* (+ (* sec-h (expt 2 16))
             sec-l)
          1000)
       (/ micro 1000))))

(defun erc-crypt-generate-iv ()
  "Generate a suitable IV that will be used for message encryption.
Return IV as a 128bit hex string."
  (substring (sha1 (mapconcat
                    (lambda (x) (format "%d" x))
                    (list (erc-crypt-time-millis)
                          (random t)
                          (random t))
                    ""))
             0 32))

(defun* erc-crypt-encrypt (string)
  "Encrypt STRING with `erc-crypt-key'.
An IV generated dynamically by `erc-crypt-generate-iv' is used for encryption.
Return the BASE64 encoded concatenation of IV and CIPHERTEXT which should be
BASE64 encoded as well.

If `erc-crypt-key' is NIL, the user will be asked interactively to provide a key.
Return NIL on error."
  (unless erc-crypt-key
    (setq erc-crypt-key (sha1 (read-passwd "Key: ")))
    (message "New key set"))
  (condition-case ex
      (let ((iv (erc-crypt-generate-iv))
            (key erc-crypt-key))
        (multiple-value-bind (status result)
            (with-temp-buffer
              (insert-string string)
              (values (call-process-region
                       (point-min) (point-max)
                       erc-crypt-openssl-path t t nil
                       "enc" "-a" (concat "-" erc-crypt-cipher)
                       "-iv" iv "-K" key "-nosalt")
                      (buffer-string)))
          (unless (= status 0)
            (message "Non-zero return code from openssl (encrypt)")
            (return-from erc-crypt-encrypt nil))
          (base64-encode-string (concat iv result) t)))
    ('error
     (message "Process error during encryption: %s" ex)
     nil)))

(defun* erc-crypt-decrypt (string)
  "Decrypt STRING with `erc-crypt-key'.
STRING should be BASE64 encoded and contain in order, the IV as a 16 byte hex string
and the CIPHERTEXT, which should be BASE64 encoded as well.

If `erc-crypt-key' is NIL, return NIL. See `erc-crypt-set-key'.
Return NIL on all errors."
  (unless erc-crypt-key
    (message "No key set, could not decrypt")
    (return-from erc-crypt-decrypt nil))
  (condition-case ex
      (let* ((str (base64-decode-string string))
             (iv (substring str 0 32))
             (key erc-crypt-key)
             (ciphertext (substring str 32)))
        (multiple-value-bind (status result)
            (with-temp-buffer
              (insert-string ciphertext)
              (values (call-process-region
                       (point-min) (point-max)
                       erc-crypt-openssl-path t t nil
                       "enc" "-d" "-a" (concat "-" erc-crypt-cipher)
                       "-iv" iv "-K" key "-nosalt")
                      (buffer-string)))
          (unless (= status 0)
            (message "Non-zero return code from openssl (decrypt)")
            (return-from erc-crypt-decrypt nil))
          result))
      ('error
       (message "Process error during decryption: %s" ex)
       nil)))


(defun erc-crypt-maybe-send (string)
  "Function that runs as a hook in `erc-send-pre-hook' and encrypts STRING.
STRING should contain input from user.
On all errors, do not send STRING to the server."
  (when (and erc-crypt-mode
             ;; Skip ERC commands
             (not (string-equal "/" (substring string 0 1))))
    (let ((encrypted (erc-crypt-encrypt (encode-coding-string string 'utf-8 t))))
      (if encrypted
          (setq erc-crypt-message str
                str (concat erc-crypt-prefix encrypted erc-crypt-postfix))
          (progn
            (message "Message will not be sent")
            (setq erc-send-this nil))))))

(defun erc-crypt-maybe-send-fixup ()
  "Function that restores the encrypted message back to its plaintext form.
This happens inside `erc-send-modify-hook'."
  (erc-crypt-with-message (msg)
    (insert erc-crypt-message)
    (goto-char (point-min))
    (insert (concat (propertize erc-crypt-indicator 'face
                                `(:foreground ,erc-crypt-success-color))
                    " "))))

(defun erc-crypt-maybe-insert ()
  "Function that decrypts encrypted messages sent by the remote end.
This happens inside `erc-insert-modify-hook'."
  (erc-crypt-with-message (msg)
    (let ((decrypted (erc-crypt-decrypt msg)))
      (if decrypted
          (progn
            (insert (decode-coding-string decrypted 'utf-8 t))
            (goto-char (point-min))
            (insert (concat (propertize erc-crypt-indicator
                                      'face `(:foreground ,erc-crypt-success-color))
                          " ")))
        (progn
          (insert msg)
          (goto-char (point-min))
          (insert (concat (propertize erc-crypt-indicator
                                    'face `(:foreground ,erc-crypt-failure-color))
                        " ")))))))

;;
;; Interactive
;; 

(defun erc-crypt-enable ()
  "Enable erc-crypt-mode for the current buffer."
  (interactive)
  (assert (eq major-mode 'erc-mode))
  (erc-crypt-mode t))

(defun erc-crypt-disable ()
  "Disable erc-crypt-mode for the current buffer."
  (interactive)
  (assert (eq major-mode 'erc-mode))
  (erc-crypt-mode -1))

(defun erc-crypt-set-key (key)
  "Sets `erc-crypt-key' for the current buffer.
The value used is the SHA1 hash of KEY."
  (interactive
   (list (read-passwd "Key: ")))
  (if erc-crypt-key
      (message "Key changed")
    (message "New key set"))
  (setq erc-crypt-key (sha1 key)))

(provide 'erc-crypt)

;;; erc-crypt.el ends here
