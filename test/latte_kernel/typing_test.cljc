
(ns latte-kernel.typing-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.typing :refer :all]))

(deftest test-type-of-term
  (is (= (type-of-term {} [] '□)
         '[:ko {:msg "Kind has not type" :term □}])))

(deftest test-type-of-type
  (is (= (type-of-term {} [] '✳)
         '[:ok □])))

(deftest test-type-of-var
  (is (= (type-of-term {} '[[bool ✳] [x bool]] 'x)
         '[:ok bool]))

  (is (= (type-of-term {} '[[x bool]] 'x)
         '[:ko {:msg "Cannot calculate type of variable.",
                :term x,
                :from {:msg "No such variable in type context", :term bool}}]))
  
  (is (= (type-of-term {} '[[y x] [x bool]] 'y)
         '[:ko {:msg "Cannot calculate type of variable.", :term y,
                :from {:msg "Cannot calculate type of variable.", :term x,
                       :from {:msg "No such variable in type context", :term bool}}}]))

  (is (= (type-of-term {} '[[x ✳]] 'x)
         '[:ok ✳]))

  (is (= (type-of-term {} '[[x □]] 'x)
         '[:ok □]))

  (is (= (type-of-term {} '[[bool ✳] [y bool]] 'x)
         '[:ko {:msg "No such variable in type context", :term x}])))

(deftest test-type-of-prod
  (is (= (type-of-term {} [] '(Π [x ✳] x))
         '[:ok ✳]))

  (is (= (type-of-term {} [] '(Π [x ✳] ✳))
         '[:ok □]))

  (is (= (type-of-term {} [] '(Π [x □] ✳))
         '[:ko {:msg "Cannot calculate domain type of product.", :term □,
                :from {:msg "Kind has not type" :term □}}]))

  (is (= (type-of-term {} [] '(Π [x ✳] □))
         '[:ko {:msg "Cannot calculate codomain type of product.", :term □,
                :from {:msg "Kind has not type" :term □}}])))
