
(ns latte-kernel.presyntax-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :refer :all]
            [latte-kernel.defenv :as defenv]))

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
  (is (= (parse-term defenv/empty-env :type)
         '[:ok ✳])))

(deftest test-parse-symbol
  (is (= (parse-term defenv/empty-env 'x #{'x})
         '[:ok x]))

  (is (= (parse-term defenv/empty-env 'x #{'y})
         '[:ok x]))

  (is (= (parse-term (defenv/mkenv {'x (defenv/map->Definition {:arity 0})}) 'x)
         '[:ok (x)]))

  (is (= (parse-term (defenv/mkenv {'x (defenv/map->Definition {:arity 1})}) 'x)
         '[:ok (x)])))

(deftest test-parse-binding
  (is (= (parse-binding defenv/empty-env '[x :type] #{})
         '[:ok [[x ✳]]]))

  (is (= (parse-binding defenv/empty-env '[x y z :type] #{})
         '[:ok [[x ✳] [y ✳] [z ✳]]]))

  (is (= (parse-binding defenv/empty-env '[x y Π :type] #{})
         '[:ko {:msg "Wrong binding variable: symbol is reserved",
                :term [x y Π :type],
                :symbol Π}]))

  (is (= (parse-binding defenv/empty-env '[x y x :type] #{})
         '[:ko {:msg "Duplicate binding variable", :term [x y x :type], :var x}]))

  (is (= (parse-binding defenv/empty-env '[x] #{})
         '[:ko {:msg "Binding must have at least 2 elements", :term [x]}]))

  #_(is (= (parse-binding defenv/empty-env '[x y :bad] #{})
         '[:ko {:msg "Wrong binding type", :term [x y :bad], :from {:msg "Cannot parse term", :term :bad}}])))

(deftest test-parse-lambda-term
  (is (= (parse-term defenv/empty-env '(λ [x :type] x))
         '[:ok (λ [x ✳] x)]))

  (is (= (parse-term defenv/empty-env '(λ [x y :type] x))
         '[:ok (λ [x ✳] (λ [y ✳] x))]))

  (is (= (parse-term defenv/empty-env '(λ [x x :type] x))
         '[:ko {:msg "Wrong bindings in λ form",
                :term (λ [x x :type] x),
                :from {:msg "Duplicate binding variable",
                       :term [x x :type],
                       :var x}}]))

  (is (= (parse-term defenv/empty-env '(λ [x] x))
         '[:ko {:msg "Wrong bindings in λ form",
                :term (λ [x] x),
                :from {:msg "Binding must have at least 2 elements", :term [x]}}]))

  (is (= (parse-term defenv/empty-env '(λ [x :type] z))
         '[:ok (λ [x ✳] z)])))

(deftest test-parse-product-term
  (is (= (parse-term defenv/empty-env '(Π [x :type] x))
         '[:ok (Π [x ✳] x)]))

  (is (= (parse-term defenv/empty-env '(Π [x y :type] x))
         '[:ok (Π [x ✳] (Π [y ✳] x))])))

(deftest test-parse-terms
  (is (= (parse-terms defenv/empty-env '(x y z) #{'x 'y 'z})
         '[:ok [x y z]]))

  (is (= (parse-terms defenv/empty-env '(x y z) #{'x 'z})
         '[:ok [x y z]])))

(deftest test-parse-arrow-term
  (is (= (parse-term defenv/empty-env '(⟶ :type :type))
         '[:ok (Π [⇧ ✳] ✳)]))

  (is (= (parse-term defenv/empty-env '(⟶ sigma tau mu))
         '[:ok (Π [⇧ sigma] (Π [⇧ tau] mu))])))

(deftest test-parse-defined-term
  (is (= (parse-term (defenv/mkenv {'ex (defenv/map->Definition {:arity 2})})
                     '(ex x :kind) #{'x})
         '[:ok (ex x □)]))

  (is (= (parse-term (defenv/mkenv {'ex (defenv/map->Definition {:arity 3})})
                     '(ex x y z) '#{x y z})
         '[:ok (ex x y z)])))

(deftest test-left-binarize
  (is (= (left-binarize '(a b))
         '[a b]))

  (is (= (left-binarize '(a b c))
         '[[a b] c]))

  (is (= (left-binarize '(a b c d e))
         '[[[[a b] c] d] e])))

(deftest test-parse-application-term
  (is (= (parse-term defenv/empty-env '(x y) '#{x y})
         '[:ok [x y]]))

  (is (= (parse-term defenv/empty-env '(x y z) '#{x y z})
         '[:ok [[x y] z]]))

  (is (= (parse-term defenv/empty-env '(x y z t) '#{x y z t})
         '[:ok [[[x y] z] t]]))

  (is (= (parse-term defenv/empty-env '(λ [x :type] x :type :kind))
         '[:ok (λ [x ✳] [[x ✳] □])])))
