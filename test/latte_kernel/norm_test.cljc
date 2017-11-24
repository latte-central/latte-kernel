
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

  (is (= (beta-red '(λ [y ✳] (let [x ✳ y] (λ [y ✳] (test x y z)))))
         ;; => if *this* is not a bug, what is ?! (λ [y ✳] (λ [y ✳] (test x y z)))))
         ;; => this one is nice too ! (λ [y ✳] (λ [y ✳] (test y y z)))
         ;; => and what about this one ? (λ [y ✳] (λ [y' ✳] (test y' y' z)))
         '(λ [y ✳] (λ [y' ✳] (test y y' z)))))

  (is (= (beta-red '(let [y ✳ z] (let [x ✳ y] (λ [y ✳] (test x y z)))))
         '(λ [y' ✳] (test z y' z))))
  
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
         '[[[(λ [x ✳] (λ [y ✳] (λ [z ✳] [[x y] [z x]]))) (λ [t ✳] t)] t1] [t2 t3]]))

  (is (= (instantiate-def '[[x ✳] [y ✳] [z ✳]]
                          '[[x y] [z x]]
                          '((λ [t ✳] t) t1 [t2 t3]))
         '[[[(λ [x ✳] (λ [y ✳] (λ [z ✳] [[x y] [z x]]))) (λ [t ✳] t)] t1] [t2 t3]]))
  
  (is (= (instantiate-def '[[x ✳] [y ✳] [z ✳] [t ✳]]
                          '[[x y] [z t]]
                          '((λ [t ✳] t) t1 [t2 t3]))
         '[[[(λ [x ✳] (λ [y ✳] (λ [z ✳] (λ [t ✳] [[x y] [z t]])))) (λ [t ✳] t)] t1] [t2 t3]]))
  
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
         '[[[[(λ [x ✳] (λ [y □] (λ [z ✳] [y (λ [t ✳] [x [z t]])]))) [a b]] c] [t (λ [t] t)]] true]))

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
         '[[[(λ [x ✳] (λ [y □] (λ [z ✳] [y (λ [t ✳] [x [z t]])]))) [a b]] c] true])))

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
         '[[y [(λ [x ✳] [x x]) [t t]]] 1]))

  (is (= (delta-step (defenv/mkenv {'test (defenv/map->Definition
                                            '{:arity 2
                                              :tag :definition
                                              :params [[x ✳] [y ✳]]
                                              :parsed-term [x [y x]]
                                              :opts {}})})
                     []
                     '[y (test [t t] u)])
         '[[y [[(λ [x ✳] (λ [y ✳] [x [y x]])) [t t]] u]] 1]))

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

