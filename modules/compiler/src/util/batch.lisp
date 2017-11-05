(in-package :ousia)

(defun batch (seq n)
  "Split a list into n-sized chunks. The last chunk can be smaller."
  (if (<= n 0) (return-from batch nil))
  (let (size (length seq))
    (if (<= size n)
        seq
        (progn
          (setf i 0)
          (setf j n)
          (append
            (loop while (>= size j)
                  collect (subseq seq i j)
                  do (setf i j)
                  do (setf j (+ j n)))
            (subseq seq i))))))
