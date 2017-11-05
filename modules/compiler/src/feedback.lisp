(in-package :ousia)

(defclass feedback ()
  ((level
     :accessor feedback-level
     :initarg :level)
   (title
     :accessor feedback-title
     :initarg :title)
   (body
     :accessor feedback-body
     :initarg :body)))

;(defmethod write ()
;  (format t (cond ((> feedback-level 2) (style feedback-title (feedback) :red :bold)))))
