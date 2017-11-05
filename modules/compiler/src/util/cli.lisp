;;;; cli.lisp
;;;; ========
;;;; A number of generic utilities related to formatting, terminal interaction,
;;;; output writing, and such.

(in-package :ousia)

(defun cli-args ()
  (or #+SBCL sb-ext:*posix-argv*
      #+CLISP (ext:argv)
      #+ABCL ext:*command-line-argument-list*
      #+CLOZURE (ccl::command-line-arguments)
      #+GCL si:*command-args*
      #+ECL (loop for i from 0 below (si:argc) collect (si:argv i))
      #+CMU extensions:*command-line-strings*
      #+ALLEGRO (sys:command-line-arguments)
      #+LISPWORKS sys:*line-arguments-list*
      nil))

(defun decorate (str ansi-code)
  (concatenate 'string
    (format nil "~c[~dm" #\ESC ansi-code)
    str))

(defun style (str &rest decorators)
  (loop for x in decorators
        do (setf str (decorate str (match x
          (:red 31)
          (:green 32)
          (:yellow 33)
          (:blue 34)
          (:magenta 35)
          (:bold 1)
          (:italic 3)
          (:underline 4)
          (:blink 5)
          (:reverse 7)
          (otherwise (error "~S is not a valid decorator" x))))))
  (concatenate 'string
    str
    (format nil "~c[0m" #\ESC)))
