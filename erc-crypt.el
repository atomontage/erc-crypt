;;; erc-crypt.el --- Symmetric Encryption for ERC

;; Copyright (C) 2011-2020 xristos@sdf.org
;; All rights reserved

;; Version: 1.9 - 2020-04-10
;; Author: xristos <xristos@sdf.org>
;; URL: https://github.com/atomontage/erc-crypt
;; Package-Requires: ((cl-lib "0.5"))
;; Keywords: comm

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
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;; ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
;; LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;; CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;; SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;; CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;; ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;; POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:
;;
;; Minor mode for ERC that provides PSK encryption.
;;
;; An external `openssl' binary is used for the actual encryption,
;; communicating with Emacs via `call-process-region'.
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
;;; Features:
;;
;; - Uses external OpenSSL binary for encrypt/decrypt
;; - Visual in-buffer indicator for errors and encrypted messages
;;   sent/received
;; - Auto splits ciphertext in order to get around IRC message limits.
;;   Original formatting is preserved, no information is lost.
;; - Messages are padded to constant size
;;
;;
;;; TODO:
;;
;; + Move to GnuPG for symmetric encryption
;;   (and customizable key derivation from passphrase)
;;
;; + Use OpenSSL for DH key generation
;;
;; + Fully automated authenticated DH key exchange
;;
;;
;;; Notes:
;;
;; erc-crypt should be seen as a proof-of-concept and serve as HOWTO-code
;; in terms of developing similar minor modes for ERC.
;;
;; Do NOT use this if you need STRONG cryptography!

;;; Code:

(require 'erc)
(require 'erc-fill)
(require 'sha1)
(require 'cl-lib)

;; erc-fill doesn't play nice with erc-crypt.el
(defvar erc-crypt-fill-function nil)

(make-variable-buffer-local 'erc-crypt-fill-function)
(make-variable-buffer-local 'erc-fill-function)

(defvar erc-crypt-openssl-path "openssl"
  "Path to openssl binary.")

(defvar erc-crypt-cipher "aes-256-cbc"
  "Cipher to use. Default is AES CBC.")

(defvar erc-crypt-indicator "☿"
  "String indicator for (in-buffer) encrypted messages.")

(defvar erc-crypt-success-color "PaleGreen"
  "Color to indicate success.")

(defvar erc-crypt-failure-color "#ffff55"
  "Color to indicate failure.")

(defvar erc-crypt-prefix "LVX"
  "String prefixed to all encrypted messages sent/received.")

(defvar erc-crypt-postfix "IAO"
  "String postfixed to all encrypted messages sent/received.")

(defvar erc-crypt-max-length 150
  "Maximum message length. If input message exceeds it, message is
broken up using `erc-crypt-split-message'. This is used to work around
IRC protocol message limits.")

(defvar erc-crypt-message nil
  "Last message sent (before encryption).")

(make-variable-buffer-local 'erc-crypt-message)

(defvar erc-crypt-key nil
  "Key to use for encryption.
If auto-set, it is the SHA1 hash of the string interactively provided in
`erc-crypt-encrypt'.")

(make-variable-buffer-local 'erc-crypt-key)

(defvar erc-crypt--left-over nil
  "List that contains message fragments.
Processed by `erc-crypt-post-send' inside `erc-send-completed-hook'.")

(make-variable-buffer-local 'erc-crypt--left-over)

(defvar erc-crypt--insert-queue nil
  "List that contains message fragments, before insertion.
Managed by `erc-crypt-maybe-insert'.")

(make-variable-buffer-local 'erc-crypt--insert-queue)

(define-minor-mode erc-crypt-mode
  "Toggle symmetric encryption."
  nil " CRYPT" nil
  (if erc-crypt-mode
      ;; Enabled
      (progn
        (add-hook 'erc-send-pre-hook       #'erc-crypt-maybe-send nil t)
        (add-hook 'erc-send-modify-hook    #'erc-crypt-maybe-send-fixup nil t)
        (add-hook 'erc-send-completed-hook #'erc-crypt-post-send nil t)
        (add-hook 'erc-insert-pre-hook     #'erc-crypt-pre-insert nil t)
        (add-hook 'erc-insert-modify-hook  #'erc-crypt-maybe-insert nil t)

        ;; Reset buffer locals
        (setq erc-crypt--left-over    nil
              erc-crypt--insert-queue nil
              erc-crypt-fill-function erc-fill-function
              erc-fill-function       nil))

    ;; Disabled
    (progn
      (remove-hook 'erc-send-pre-hook       #'erc-crypt-maybe-send t)
      (remove-hook 'erc-send-modify-hook    #'erc-crypt-maybe-send-fixup t)
      (remove-hook 'erc-send-completed-hook #'erc-crypt-post-send t)
      (remove-hook 'erc-insert-pre-hook     #'erc-crypt-pre-insert t)
      (remove-hook 'erc-insert-modify-hook  #'erc-crypt-maybe-insert t)
      (setq erc-fill-function erc-crypt-fill-function
            erc-crypt-fill-function nil))))


;;;
;;; Internals
;;;


(defun erc-crypt--message (format-string &rest args)
  "Call `message' with FORMAT-STRING and ARGS."
  (let ((message-truncate-lines t))
    (message "erc-crypt: %s" (apply #'format format-string args))))


(cl-defmacro erc-crypt--with-message ((message) &rest body)
  "Deal with narrowed regions as implemented by
`erc-send-modify-hook' and `erc-insert-modify-hook'.

Search for and extract an encrypted message (if present),
then bind MESSAGE to it, delete the encrypted string from buffer
and execute BODY. Finally, restore ERC text properties."
  (declare (indent defun))
  (let ((start (cl-gensym)))
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

(defun erc-crypt--time-millis ()
  "Return current time (time since Unix epoch) in milliseconds."
  (cl-destructuring-bind (sec-h sec-l micro &optional _) (current-time)
    (+ (* (+ (* sec-h (expt 2 16))
             sec-l)
          1000)
       (/ micro 1000))))

(defun erc-crypt--generate-iv ()
  "Generate a suitable IV to be used for message encryption.
Return IV as a 128bit hex string."
  (substring (sha1 (mapconcat
                    #'int-to-string
                    (list (erc-crypt--time-millis)
                          (random t)
                          (random t))
                    ""))
             0 32))


(defun erc-crypt--pad (list)
  "Pad message or fragments in LIST to `erc-crypt-max-length' bytes.
Return a list of padded message or list of fragments.

Resulting messages are of the form MMMMMMMMXXXPS.

MMM are original message bytes.
XXX are bytes used for padding.
P is a single byte that is equal to the number of X (padding bytes)
S is a single byte that is equal to 1 when the message is a fragment,
0 if not or if final fragment."
  (cl-labels ((do-pad (string split-tag)
                      (let* ((len (length string))
                             (diff (- erc-crypt-max-length len))
                             (pad (cl-loop repeat diff
                                           collect (string (random 255)) into ret
                                           finally return (cl-reduce #'concat ret))))
                        (concat string pad (string diff) (string split-tag)))))
    (cond ((listp (cl-rest list))
           ;; Message is split in parts
           (cl-loop for msg in list
                    for count from 0
                    with len = (length list)
                    if (= count (1- len))
                    collect (do-pad msg 0)
                    else
                    collect (do-pad msg 1)))
          (t (list (do-pad list 0))))))


(defun erc-crypt--split (string)
  "Split STRING into substrings that are at most `erc-crypt-max-length' bytes long.
Splitting does not take into account word boundaries or whitespace.

Return list of substrings."
  (cl-loop with len = (length string)
           for start = 0 then (+ start erc-crypt-max-length)
           while (< start len)
           collect (substring string start (min len (+ start erc-crypt-max-length)))))


;;;
;;; Public API
;;;


(cl-defun erc-crypt-encrypt (string)
  "Encrypt STRING with `erc-crypt-key'.
An IV generated dynamically by `erc-crypt--generate-iv' is used for encryption.

If `erc-crypt-key' is NIL, ask for a key interactively.

Return BASE64 encoded concatenation of IV and CIPHERTEXT which should be
BASE64 encoded as well. Return NIL on all errors."
  (unless erc-crypt-key
    (setq erc-crypt-key (sha1 (read-passwd "Key: ")))
    (erc-crypt--message "New key set"))
  (condition-case ex
      (let ((iv (erc-crypt--generate-iv))
            (key erc-crypt-key))
        (cl-multiple-value-bind (status result)
            (with-temp-buffer
              (insert (base64-encode-string string))
              (list (call-process-region
                     (point-min) (point-max)
                     erc-crypt-openssl-path t '(t nil) nil
                     "enc" "-a" (concat "-" erc-crypt-cipher)
                     "-iv" iv "-K" key "-nosalt")
                    (buffer-string)))
          (unless (= status 0)
            (erc-crypt--message "Output: %s" result)
            (erc-crypt--message "Non-zero return code %s from openssl (encrypt)" status)
            (cl-return-from erc-crypt-encrypt nil))
          (base64-encode-string (concat iv result) t)))
    ('error
     (erc-crypt--message "%s (process error/erc-crypt-encrypt)"
                         (error-message-string ex))
     nil)))

(cl-defun erc-crypt-decrypt (string)
  "Decrypt STRING with `erc-crypt-key'.
STRING must be BASE64 encoded and contain in order, the IV as a 16 byte hex string
and the CIPHERTEXT, which must be BASE64 encoded as well.

If `erc-crypt-key' is NIL, return NIL. See `erc-crypt-set-key'.
Return NIL on all errors."
  (unless erc-crypt-key
    (erc-crypt--message "No key set, could not decrypt")
    (cl-return-from erc-crypt-decrypt nil))
  (condition-case ex
      (let* ((str (base64-decode-string string))
             (iv (substring str 0 32))
             (key erc-crypt-key)
             (ciphertext (substring str 32)))
        (cl-multiple-value-bind (status result)
            (with-temp-buffer
              (insert ciphertext)
              (list (call-process-region
                     (point-min) (point-max)
                     erc-crypt-openssl-path t '(t nil) nil
                     "enc" "-d" "-a" (concat "-" erc-crypt-cipher)
                     "-iv" iv "-K" key "-nosalt")
                    (buffer-string)))
          (unless (= status 0)
            (erc-crypt--message "Non-zero return code %s from openssl (erc-crypt-decrypt)" status)
            (cl-return-from erc-crypt-decrypt nil))
          (base64-decode-string result)))
    ('error
     (erc-crypt--message "%s (process error/erc-crypt-decrypt)"
                         (error-message-string ex))
     nil)))



(defun erc-crypt-maybe-send (string)
  "Encrypt STRING and send to receiver. Runs as a hook in `erc-send-pre-hook'.
STRING should contain user input. In order to get around IRC protocol
message size limits, STRING is split into fragments and padded to a
constant size, `erc-crypt-max-length', by calling `erc-crypt-split-message'.
The resulting padded fragments are encrypted and sent separately,
the original message reconstructed at the receiver end, with the original
formatting preserved intact.

On errors, do not send STRING to the server."
  (when (and erc-crypt-mode
             ;; Skip ERC commands
             (not (string= "/" (substring string 0 1))))
    (let* ((encoded (encode-coding-string string 'utf-8 t))
           (split (erc-crypt-split-message encoded))
           (encrypted (mapcar #'erc-crypt-encrypt split)))
      (cond ((cl-some #'null encrypted)
             (erc-crypt--message "Message will not be sent")
             (setq erc-send-this nil))
            (t
             ;; str is dynamically bound
             (defvar str)
             (setq erc-crypt-message str
                   str (concat erc-crypt-prefix (cl-first encrypted) erc-crypt-postfix)
                   erc-crypt--left-over (cl-rest encrypted)))))))


(defun erc-crypt-maybe-send-fixup ()
  "Restore encrypted message back to its plaintext form.
This happens inside `erc-send-modify-hook'."
  (erc-crypt--with-message (msg)
    (insert erc-crypt-message)
    (goto-char (point-min))
    (insert (concat (propertize erc-crypt-indicator 'face
                                (list :foreground erc-crypt-success-color))
                    " "))))

(defun erc-crypt-pre-insert (string)
  "Decrypt STRING and insert it into `erc-crypt--insert-queue'.
If decrypted message is a fragment, `erc-insert-this' is set to NIL.
This will avoid displaying message and will not trigger `erc-insert-modify-hook'."
  (when (string-match (concat erc-crypt-prefix "\\(.+\\)" erc-crypt-postfix) string)
    (let* ((msg (match-string 1 string))
           (decrypted (erc-crypt-decrypt msg)))
      (if decrypted
          (let* ((len (length decrypted))
                 (split (aref decrypted (1- len)))
                 (pad (aref decrypted (- len 2)))
                 (decrypted (substring decrypted 0 (- len 2 pad))))
            (push (cons decrypted split) erc-crypt--insert-queue)
            (if (= split 1) (setq erc-insert-this nil)))
        ;; Error
        (push (cons :error :error) erc-crypt--insert-queue)))))

(defun erc-crypt-maybe-insert ()
  "Display decrypted messages and do fragment reconstruction.
This happens inside `erc-insert-modify-hook'."
  (cl-labels ((insert-msg (msg)
                          (insert (decode-coding-string msg 'utf-8 :nocopy))
                          (goto-char (point-min))
                          (insert (concat (propertize erc-crypt-indicator
                                                      'face
                                                      (list :foreground
                                                            erc-crypt-success-color))
                                          " "))
                          (setq erc-crypt--insert-queue nil)))
    (erc-crypt--with-message (msg)
      (let* ((len (length erc-crypt--insert-queue))
             (cons (cl-first erc-crypt--insert-queue))
             (msg (car cons))
             (tag (cdr cons)))
        (cond ((eql msg :error)
               ;; Insert queued fragments
               (insert (concat "(decrypt error) "
                               (decode-coding-string
                                (mapconcat #'identity
                                           (mapcar #'car
                                                   (nreverse (cl-rest erc-crypt--insert-queue)))
                                           "")
                                'utf-8 :nocopy)))
               (goto-char (point-min))
               (insert (concat (propertize erc-crypt-indicator
                                           'face (list :foreground erc-crypt-failure-color))
                               " "))
               (setq erc-crypt--insert-queue nil))
              ((and (= len 1) (= tag 0))
               ;; Normal message
               (insert-msg msg))
              ((and (= len 1) (= tag 1))
               ;; Do nothing
               t)
              ((= tag 0)
               ;; Final fragment
               (insert-msg (mapconcat #'identity (mapcar #'car
                                                         (nreverse erc-crypt--insert-queue))
                                      ""))))))))

(defun erc-crypt-post-send (string)
  "Send message fragments placed in `erc-crypt--left-over' to remote end."
  (unwind-protect
      (cl-loop for m in erc-crypt--left-over do
            (erc-message "PRIVMSG"
                         (concat (erc-default-target) " "
                                 (concat erc-crypt-prefix m erc-crypt-postfix))))
    (setq erc-crypt--left-over nil)))



(defun erc-crypt-split-message (string)
  (let* ((len (length string)))
    (cond ((<= len erc-crypt-max-length)
           ;; Pad to maximum size if needed
           (erc-crypt--pad (list string)))
          (t
           (erc-crypt--pad (erc-crypt--split string))))))


;;;
;;; Interactive
;;;


(defun erc-crypt-enable ()
  "Enable `erc-crypt-mode' for the current buffer."
  (interactive)
  (cl-assert (eq major-mode 'erc-mode) t)
  (erc-crypt-mode t))

(defun erc-crypt-disable ()
  "Disable `erc-crypt-mode' for the current buffer."
  (interactive)
  (cl-assert (eq major-mode 'erc-mode) t)
  (erc-crypt-mode -1))

(defun erc-crypt-set-key (key)
  "Set `erc-crypt-key' for the current buffer.
The value used is the SHA1 hash of KEY."
  (interactive
   (list (read-passwd "Key: ")))
  (if erc-crypt-key
      (erc-crypt--message "Key changed")
    (erc-crypt--message "New key set"))
  (setq erc-crypt-key (sha1 key)))

(provide 'erc-crypt)
;;; erc-crypt.el ends here
