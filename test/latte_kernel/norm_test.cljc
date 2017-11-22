
(ns latte-kernel.norm-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.defenv :as defenv]
            [latte-kernel.norm :refer :all]))

(deftest test-beta-reduction
  (is (= (beta-reduction '[(λ [x ✳] [x x]) y])
         '[y y])))

(deftest test-beta-red
  (is (= (beta-red '[(λ [x ✳] x) y])
         'y))
  
  (is (= (beta-red '[[(λ [x ✳] x) y] z])
         '[y z]))
  
  (is (= (beta-red '(λ [y [(λ [x □] x) ✳]] y))
         '(λ [y ✳] y)))
  
  (is (= (beta-red '[z [(λ [x ✳] x) y]])
         '[z y]))

  (is (= (beta-red '(let [x ✳ y] x))
         'y))

  (is (= (beta-red '(λ [x ✳] (let [x ✳ y] x)))
         '(λ [x ✳] y)))

  (is (= (beta-red '(λ [x ✳] (let [y ✳ x] y)))
         '(λ [x ✳] x)))

  (is (= (beta-red '(λ [x ✳] (let [x ✳ x] x)))
         '(λ [x ✳] x)))
  
  (is (= (beta-red '(:latte-kernel.syntax/ascribe z [(λ [x ✳] x) y]))
         'z))
  
  (is (= (beta-red '(:latte-kernel.syntax/ascribe [(λ [x ✳] x) y] z))
         'y))
  
  (is (= (beta-red '[x y])
         '[x y])))

(deftest test-instantiate-def
  (is (= (instantiate-def '[[x ✳] [y ✳] [z ✳]]
                          '[[x y] [z x]]
                          '((λ [t ✳] t) t1 [t2 t3]))
         '(let [x ✳ (λ [t ✳] t)] (let [y ✳ t1] (let [z ✳ [t2 t3]] [[x y] [z x]])))))
  
  (is (= (instantiate-def '[[x ✳] [y ✳] [z ✳] [t ✳]]
                          '[[x y] [z t]]
                          '((λ [t ✳] t) t1 [t2 t3]))
         '(let [x ✳ (λ [t ✳] t)] (let [y ✳ t1] (let [z ✳ [t2 t3]] (λ [t ✳] [[x y] [z t]]))))))
  
  (is (= (instantiate-def '[[x ✳] [y ✳] [z ✳]]
                          '[[x y] z]
                          '())
         '(λ [x ✳] (λ [y ✳] (λ [z ✳] [[x y] z]))))))

(deftest test-delta-reduction
  (is (= (delta-reduction (defenv/mkenv {'test (defenv/map->Definition
                                                 '{:name test
                                                   :arity 3
                                                   :params [[x ✳] [y □] [z ✳]]
                                                   :parsed-term [y (λ [t ✳] [x [z t]])]
                                                   :opts {}})})
                          []
                          '(test [a b] c [t (λ [t] t)]))
         '[(let [x ✳ [a b]] (let [y □ c] (let [z ✳ [t (λ [t] t)]] [y (λ [t ✳] [x [z t]])]))) true]))

  (is (= (delta-reduction (defenv/mkenv {'test (defenv/map->Theorem
                                                 '{:name test
                                                   :arity 3
                                                   :params [[x ✳] [y □] [z ✳]]
                                                   :proof [y (λ [t ✳] [x [z t]])]})})
                          []
                          '(test [a b] c [t (λ [t] t)]))
         '[(test [a b] c [t (λ [t] t)]) false]))
 
  (is (= (delta-reduction (defenv/mkenv {'test (defenv/map->Axiom
                                                 '{:arity 3
                                                   :tag :axiom
                                                   :params [[x ✳] [y □] [z ✳]]})})
                          []
                          '(test [a b] c [t (λ [t] t)]))
         '[(test [a b] c [t (λ [t] t)]) false]))

  (is (= (delta-reduction (defenv/mkenv {'test (defenv/map->Definition
                                                 '{:arity 3
                                                   :tag :definition
                                                   :params [[x ✳] [y □] [z ✳]]
                                                   :parsed-term [y (λ [t ✳] [x [z t]])]
                                                   :opts {}})})
                          []
                          '(test [a b] c))
         '[(let [x ✳ [a b]] (let [y □ c] (λ [z ✳] [y (λ [t ✳] [x [z t]])]))) true])))

(deftest test-delta-step
  (is (= (delta-step {} [] 'x)
         '[x 0]))
      
  (is (= (delta-step (defenv/mkenv {'test (defenv/map->Definition
                                            '{:arity 1
                                              :tag :definition
                                              :params [[x ✳]]
                                              :parsed-term [x x]
                                              :opts {}})})
                     []
                     '[y (test [t t])])
         '[[y (let [x ✳ [t t]] [x x])] 1]))

  (is (= (delta-step (defenv/mkenv {'test (defenv/map->Definition
                                            '{:arity 2
                                              :tag :definition
                                              :params [[x ✳] [y ✳]]
                                              :parsed-term [x [y x]]
                                              :opts {}})})
                     []
                     '[y (test [t t] u)])
         '[[y (let [x ✳ [t t]] (let [y ✳ u] [x [y x]]))] 1]))

  (is (= (delta-step (defenv/mkenv {'test (defenv/map->Definition
                                            '{:arity 2
                                              :tag :definition
                                              :params [[x ✳] [y ✳]]
                                              :parsed-term [x [y x]]
                                              :opts {:opaque true}})})
                     []
                     '[y (test [t t] u)])
         '[[y (test [t t] u)] 0])))

(deftest test-normalize
  (is (= (normalize '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y]))
         '(λ [y ✳] y))))


(deftest test-beta-eq?
  (is (= (beta-eq? '(λ [z ✳] z)
                   '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y]))
         true)))

