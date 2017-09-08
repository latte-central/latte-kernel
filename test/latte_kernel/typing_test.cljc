
(ns latte-kernel.typing-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.defenv :as defenv]
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

(deftest test-type-of-abs
  (is (= (type-of-term {} '[[bool ✳] [t bool] [y bool]]
                       '(λ [x bool] x))
         '[:ok (Π [x bool] bool)]))

  (is (= (type-of-term {} [] '(λ [x ✳] x))
         '[:ok (Π [x ✳] ✳)]))

  (is (= (type-of-term {} '[[y bool]] '(λ [x bool] x))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x bool] x),
                :from {:msg "Cannot calculate type of variable.", :term x,
                       :from {:msg "No such variable in type context", :term bool}}}]))

  (is (= (type-of-term {} '[[y ✳] [z y]] '(λ [x z] x))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x z] x),
                :from {:msg "Not a correct type (super-type is not a sort)", :term x, :type z, :sort y}}]))

  (is (= (type-of-term {} '[[y bool]] '(λ [x ✳] y))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] y),
                :from {:msg "Cannot calculate type of variable.", :term y,
                       :from {:msg "No such variable in type context", :term bool}}}]))

  (is (= (type-of-term {} '[[y bool]] '(λ [x ✳] □))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] □),
                :from {:msg "Kind has not type" :term □}}]))

  (is (= (type-of-term {} '[[y bool]] '(λ [x ✳] ✳))
         '[:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type).",
                :term (λ [x ✳] ✳), :codomain □,
                :from {:msg "Cannot calculate codomain type of product.", :term □,
                       :from {:msg "Kind has not type", :term □}}}]))
  (is (= (type-of-term {} '[[w ✳] [y w] [z y]] '(λ [x ✳] z))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.", :term (λ [x ✳] z),
                :from {:msg "Not a correct type (super-type is not a sort)", :term z, :type y, :sort w}}])))

(deftest test-type-of-app
  (is (= (type-of-term {} '[[bool ✳] [y bool]]
                       '[(λ [x bool] x) y])
         '[:ok bool])))

;; (deftest test-type-of-refdef
;;   (let [eqdef ]))

(deftest test-type-of-refdef

  (is (= (type-of-term {'test (defenv/map->Definition
                                '{:params [[x ✳] [y ✳]]
                                  :type ✳
                                  :arity 2})}
                       '[[a ✳] [b ✳]]
                       '(test a b))
         '[:ok ✳]))

  (is (= (type-of-term {'test (defenv/map->Definition
                                '{:params [[x ✳] [y ✳]]
                                  :type ✳
                                  :arity 2})}
                       '[[bool ✳] [a ✳] [b bool]]
                       '(test a b))
         '[:ko {:msg "Wrong argument type", :term (test b), :arg b, :expected-type ✳}])))

