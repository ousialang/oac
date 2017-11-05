(in-package :ousia)

(defun main ()
  (format t "The Ousia programming language" (fetch-ousia-version))
  (format t "~&~S~&" (cli-args)))
