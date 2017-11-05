(asdf:defsystem :ousia
  :description "The OUSIA compiler"
  :version "0.1.0"
  :author "Filippo Costa"
  :mailto "filippocosta.italy@gmail.com"
  :license "BSD 3-clause"
  :depends-on
   (:cl-utilities
    :alexandria
    :apply-argv
    :trivia)
  :serial t
  :pathname "src/"
  :components
   ((:file "package")
    (:file "util/batch")
    (:file "util/cli")
    (:file "feedback")
    (:file "scanner")
    (:file "main")))

(defsystem :ousia.test
  :depends-on (:ousia :prove)
  :serial t
  :pathname "test/"
  :components
    ((:file "package")))
