(defpackage :ousia
  (:use :cl :alexandria :trivia)
  (:export
    :flat-lines
    :style
    :main
    :lines
    :scan
    :trailing-whitespace
    :entry-point :batch))

(in-package :ousia)

(defun fetch-ousia-version ()
  (let ((system (asdf:find-system :ousia nil)))
    (when (and system (slot-boundp system 'asdf:version))
      (asdf:component-version system))))
