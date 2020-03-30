(ns latte-kernel.typing-test
  (:require #?@(:clj [[clojure.test :refer :all]
                      [matcher-combinators.test]]
                :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.defenv :as defenv]
            [latte-kernel.presyntax :as parse]
            [latte-kernel.typing :refer :all]))

(deftest test-type-of-term
  (is (= (type-of-term defenv/empty-env [] '□)
         '[:ko {:msg "Kind has not type" :term □} nil])))

(deftest test-type-of-type
  (is (= (type-of-term defenv/empty-env [] '✳)
         '[:ok □ ✳])))

(deftest test-type-of-var
  (is (= (type-of-term defenv/empty-env '[[bool ✳] [x bool]] 'x)
         '[:ok bool x]))

  (is (= (type-of-term defenv/empty-env '[[x bool]] 'x)
         '[:ko {:msg "Cannot calculate type of variable.",
                :term x,
                :from {:msg "No such variable in type context", :term bool}}
           nil]))

  (is (= (type-of-term defenv/empty-env '[[y x] [x bool]] 'y)
         '[:ko {:msg "Cannot calculate type of variable.",
                :term y,
                :from {:msg "Cannot calculate type of variable.",
                       :term x,
                       :from {:msg "No such variable in type context", :term bool}}}
           nil]))

  (is (= (type-of-term defenv/empty-env '[[x ✳]] 'x)
         '[:ok ✳ x]))

  (is (= (type-of-term defenv/empty-env '[[x □]] 'x)
         '[:ok □ x]))

  (is (= (type-of-term defenv/empty-env '[[bool ✳] [y bool]] 'x)
         '[:ko {:msg "No such variable in type context", :term x} nil])))

(deftest test-type-of-prod
  (is (= (type-of-term defenv/empty-env [] '(Π [x ✳] x))
         '[:ok ✳ (Π [x ✳] x)]))

  (is (= (type-of-term defenv/empty-env [] '(Π [x ✳] ✳))
         '[:ok □ (Π [x ✳] ✳)]))

  (is (= (type-of-term defenv/empty-env [] '(Π [x □] ✳))
         '[:ko {:msg "Cannot calculate domain type of product.",
                :term □,
                :from {:msg "Kind has not type", :term □}}
           nil]))

  (is (= (type-of-term defenv/empty-env [] '(Π [x ✳] □))
         '[:ko {:msg "Cannot calculate codomain type of product.",
                :term □,
                :from {:msg "Kind has not type", :term □}}
           nil])))

(deftest test-type-of-abs
  (is (= (type-of-term defenv/empty-env '[[bool ✳] [t bool] [y bool]]
                       '(λ [x bool] x))
         '[:ok (Π [x bool] bool) (λ [x bool] x)]))

  (is (= (type-of-term defenv/empty-env [] '(λ [x ✳] x))
         '[:ok (Π [x ✳] ✳) (λ [x ✳] x)]))

  (is (= (type-of-term defenv/empty-env '[[y bool]] '(λ [x bool] x))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.",
                :term (λ [x bool] x),
                :from {:msg "Cannot calculate type of variable.",
                       :term x,
                       :from {:msg "No such variable in type context", :term bool}}}
           nil]))

  (is (= (type-of-term defenv/empty-env '[[y ✳] [z y]] '(λ [x z] x))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.",
                :term (λ [x z] x),
                :from {:msg "Not a correct type (super-type is not a sort)", :term x, :type z, :sort y}}
           nil]))

  (is (= (type-of-term defenv/empty-env '[[y bool]] '(λ [x ✳] y))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.",
                :term (λ [x ✳] y),
                :from {:msg "Cannot calculate type of variable.",
                       :term y,
                       :from {:msg "No such variable in type context", :term bool}}}
           nil]))

  (is (= (type-of-term defenv/empty-env '[[y bool]] '(λ [x ✳] □))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.",
                :term (λ [x ✳] □),
                :from {:msg "Kind has not type", :term □}}
           nil]))

  (is (= (type-of-term defenv/empty-env '[[y bool]] '(λ [x ✳] ✳))
         '[:ko {:msg "Not a valid codomain type in abstraction (cannot calculate super-type).",
                :term (λ [x ✳] ✳),
                :codomain □,
                :from {:msg "Cannot calculate codomain type of product.",
                       :term □,
                       :from {:msg "Kind has not type", :term □}}}
           nil]))
  (is (= (type-of-term defenv/empty-env '[[w ✳] [y w] [z y]] '(λ [x ✳] z))
         '[:ko {:msg "Cannot calculate codomain type of abstraction.",
                :term (λ [x ✳] z),
                :from {:msg "Not a correct type (super-type is not a sort)", :term z, :type y, :sort w}}
           nil])))

(deftest test-type-of-app
  (is (= (type-of-term defenv/empty-env '[[bool ✳] [y bool]]
                       '[(λ [x bool] x) y])
         '[:ok bool [(λ [x bool] x) y]]))

  ;; typing fails on operand
  (is (match? '[:ko
                {:msg "Cannot calculate operand (right-hand) type in application.",
                 :term [(λ [x A] x) y],
                 :from {:msg "Cannot calculate type of variable.",
                        :term y,
                        :from {:msg "No such variable in type context",
                               :term bool}}}
                nil]
              (type-of-term defenv/empty-env
                            '[[A ✳] [y bool]]
                            '[(λ [x A] x) y]))))
  ;; TODO: typing fails on operator

(deftest test-type-of-refdef
  (is (= (type-of-term (defenv/mkenv {'test (defenv/map->Definition
                                              '{:params [[x ✳] [y ✳]]
                                                :type ✳
                                                :arity 2})})
                       '[[a ✳] [b ✳]]
                       '(test a b))
         '[:ok ✳ (test a b)]))

  (is (= (type-of-term (defenv/mkenv {'test (defenv/map->Definition
                                             '{:params [[x ✳] [y ✳]]
                                               :type ✳
                                               :arity 2})})
                       '[[a ✳] [b ✳]]
                       '(test a))
         '[:ok (Π [y ✳] ✳) (test a)]))

  (is (= (type-of-term (defenv/mkenv {'test (defenv/map->Definition
                                              '{:params [[x ✳] [y ✳]]
                                                :type ✳
                                                :arity 2})})
                       '[[bool ✳] [a ✳] [b bool]]
                       '(test a b))
         '[:ko {:msg "Wrong argument type", :term (test b), :arg b, :arg-type bool, :expected-type ✳} nil])))

(def fake-eq (defenv/map->Definition
               {:params '[[T ✳] [x T] [y T]]
                :type (second (parse/parse-term
                               defenv/empty-env
                               '(forall [P (==> T :type)]
                                        (==> (P x) (P y)))))  ;; it's fake ! Use of ==> instead of <=> to spare one def
                :arity 3}))

(def eq-implicit (defenv/map->Implicit
                      {:implicit-fn (fn [def-env ctx [x T] [y U]]
                                      (list 'equal% T x y))}))

(deftest test-type-of-refdef-implicit

  (is (= (type-of-term (defenv/mkenv {'equal% fake-eq
                                      'equal eq-implicit})
                       '[[U ✳] [a U] [b U]]
                       '(equal a b))
         '[:ok (Π [P (Π [⇧ U] ✳)] (Π [⇧' [P a]] [P b])) (equal% U a b)])))

(def eq-implicit-cst (defenv/map->Implicit
                       {:implicit-fn (fn [def-env ctx n [x T] [y U]]
                                       (print "n =" n)
                                       (list 'equal% T x y))}))

(deftest test-type-of-refdef-implicit-cst

  (is (= (type-of-term (defenv/mkenv {'equal% fake-eq
                                      'equal eq-implicit-cst})
                       '[[U ✳] [a U] [b U]]
                       '(equal [::parse/host-constant 4] a b))
         '[:ok (Π [P (Π [⇧ U] ✳)] (Π [⇧' [P a]] [P b])) (equal% U a b)])

      #?(:clj (is (= (with-out-str (type-of-term (defenv/mkenv {'equal% fake-eq
                                                                'equal eq-implicit-cst})
                                                 '[[U ✳] [a U] [b U]]
                                                 '(equal [::parse/host-constant 4] a b)))
                     "n = 4")))))

(deftest test-rebuild-type
  (is (= (rebuild-type defenv/empty-env '[[bool ✳] [t bool] [y bool]]
                       '(Π [x bool] bool))
         '[:ok (Π [x bool] bool)])))
