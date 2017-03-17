
(ns latte-kernel.presyntax-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :refer :all]))


(deftest test-reserved-symbols
  (is (= (reserved-symbol? 'a) false))
  (is (= (reserved-symbol? 'λ) true)))


(deftest test-kind
  (is (= (kind? '□) true))
  (is (= (kind? :kind) true))
  (is (= (kind? 'a) false))
  (is (= (parse-term {} :kind)
         '[:ok □])))

(deftest test-type
  (is (= (type? '✳) true))
  (is (= (type? :type) true))
  (is (= (type? 'a) false))
  (is (= (parse-term {} :type)
         '[:ok ✳])))

(deftest test-parse-symbol
  (is (= (parse-term {} 'x #{'x})
         '[:ok x]))
  (is (= (parse-term {} 'x #{'y})
         '[:ok x]))
  (is (= (parse-term {'x {:arity 0}} 'x)
         '[:ok (x)]))
  (is (= (parse-term {'x {:arity 1}} 'x)
         '[:ok (x)])))

(deftest test-parse-binding
  (is (= (parse-binding {} '[x :type] #{})
         '[:ok [[x ✳]]]))
  (is (= (parse-binding {} '[x y z :type] #{})
         '[:ok [[x ✳] [y ✳] [z ✳]]]))
  (is (= (parse-binding {} '[x y Π :type] #{})
         '[:ko {:msg "Wrong binding variable: symbol is reserved",
                :term [x y Π :type],
                :symbol Π}]))
  (is (= (parse-binding {} '[x y x :type] #{})
         '[:ko {:msg "Duplicate binding variable", :term [x y x :type], :var x}]))
  (is (= (parse-binding {} '[x] #{})
         '[:ko {:msg "Binding must have at least 2 elements", :term [x]}]))
  (is (= (parse-binding {} '[x y :bad] #{})
         '[:ko {:msg "Wrong binding type", :term [x y :bad], :from {:msg "Cannot parse term", :term :bad}}])))

