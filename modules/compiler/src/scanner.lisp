;;;; scanner.lisp
;;;; =========

(in-package :ousia)

(defun closing-bracket (c)
  (code-char
    (match (char-code c)
      (40 41)
      (91 93)
      (123 125)
      (_ (error "`~C´ is not an opening bracket." c)))))
(defun opening-bracket (c)
  (code-char
    (match (char-code c)
      (41 40)
      (93 91)
      (125 123)
      (_ (error "`~C` is not a closing bracket." c)))))

(defun whitespace-char-p (c)
  (search
    (string c)
    (format nil " ~C~C" #\RETURN #\LINEFEED)))
(defun bracket-char-p (c)
  (search
    (string c)
    "{[()]}"))
(defun symbol-char-p (c)
  (search
    (string c)
    "+-*/;,.:<>=!?|%&@"))

;;; The tokenizer

(defun create-token (c index)
  (setf (get 'token :index) index)
  (cond ((alpha-char-p c)
         (setf (get 'token :type) :word)
         (setf (get 'token :lexeme) (cons c nil)))
        ((symbol-char-p c)
         (setf (get 'token :type) :symbol)
         (setf (get 'token :lexeme) (cons c nil)))
        ((whitespace-char-p c)
         (setf (get 'token :type) :whitespace)
         (setf (get 'token :lexeme) (cons c nil)))
        ((bracket-char-p c)
         (setf (get 'token :type) :bracket)
         (setf (get 'token :char-code) (char-code c)))
        ((char-equal c #\$)
         (setf (get 'token :type) :atom))
        ((char-equal c #\0)
         (setf (get 'token :type) :number-with-base))
        ((digit-char-p c)
         (setf (get 'token :type) :number)
         (setf (get 'token :lexeme) (cons c nil)))))

;(defconstant type-conditions
;  (list :word alpha-char-p
;    :atom alpha-char-p
;    :symbol symbol-char-p
;    :whitespace whitespace-char-p
;    :number digit-char-p))

(defun update-token (c)
  (if (match (get 'token :type)
        ((or :word :atom) (alpha-char-p c))
        (:symbol (symbol-char-p c))
        (:whitespace (whitespace-char-p c))
        (:bracket nil)
        (:number (digit-char-p c)))
      (setf (get 'token :lexeme) (cons c (get 'token :lexeme)))
      nil))

(defun scan (str)
  (if (string= "" str) (return-from scan nil))
  (setf (symbol-plist 'token) nil)
  (setf tokens nil)
  (loop for c across str
        do (if (symbol-plist 'token)
               (progn
                 (setf token-snapshot (symbol-plist 'token))
                 (if (not (update-token c))
                     (progn
                       (setf (get 'token :lexeme)
                         (reverse (coerce (get 'token :lexeme) 'string)))
                       (setf tokens (cons token-snapshot tokens))
                       (setf (symbol-plist 'token) nil)
                       (create-token c 0))))
               (create-token c 0)))
  (reverse (cons (symbol-plist 'token) tokens)))

;;; Line counting utilities and co.

(defun trailing-whitespace (string)
  (loop for line in (lines string)
        for i from 1
        if (and line (char-equal (nth 0 line) #\SPACE))
          collect i))

(defun flat-lines (string)
  (setf flag-cr nil)
  (loop for c across string
        if (char-equal c #\RETURN)
          do (setf flag-cr t)
          collect :newline
        else
          do (setf flag-cr nil)
          if (char-equal c #\LINEFEED)
            if (not flag-cr)
              collect :newline
            end
          else
            collect c))

(defun lines (string)
  (cl-utilities:split-sequence :newline (flat-lines string)))
