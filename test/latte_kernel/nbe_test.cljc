(ns latte-kernel.nbe-test
  (:require #?(:clj  [clojure.test :refer     [is deftest]]
               :cljs [cljs.test :refer-macros [is deftest]])
            [latte-kernel.nbe :as nbe :refer :all]
            [latte-kernel.syntax :as stx]
            [latte-kernel.norm :as beta-norm]
            [latte-kernel.defenv :as defenv]))

(deftest test-evaluation
  (is (= (evaluation 'a)
         'a))

  (is (= (evaluation '[(λ [a ✳] a) b])
         'b))

  (is (= (evaluation '[a b])
         ['a 'b]))

  (let [[b [x tx] f] (evaluation '(λ [a ✳] a))]
    (is (= b 'λ))
    (is (= x 'a))
    (is (= tx '✳))
    (is (fn? f))
    (is (= (f 5) 5)))

  (let [res (evaluation '[(λ [a ✳] (λ [b ✳] [a b])) c])
        [b [x tx] f] res]
    (is (= b 'λ))
    (is (= x 'b))
    (is (= tx '✳))
    (is (fn? f))
    (is (= (f 'd) '[c d])))

  (let [[v1 v2] (evaluation '[[(λ [a ✳] (λ [b ✳] [a b])) c] d])]
    (is (= v1 'c))
    (is (= v2 'd)))

  (let [term '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c]]
    (is (= (evaluation term)
           'c)))

  (let [term '(::stx/ascribe z [(λ [x ✳] x) y])
        [as v1 v2] (evaluation term)]
     (is (= as ::stx/ascribe))
     (is (= v1 'z))
     (is (= v2 'y)))

  (let [term1 '(Π [⇧ A] B)
        term2 '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B)))))
        [b1 [v1 t1] f1] (evaluation term1)
        [b2 [v2 t2] f2] (evaluation term2)]
    (is (= b1 b2 'Π))
    (is (= t1 v2 'A))
    (is (= v1 '⇧))
    (is (= t2 '✳))
    (is (and (fn? f1) (fn? f2)))))

(deftest test-quotation
  (is (= (quotation 'y)
         'y))

  (is (= (quotation '[y z])
         '[y z]))

  (let [[l [x tx] body] (quotation (list 'λ '[y ✳] (fn [x] x)))]
    (is (= l 'λ))
    (is (= x body '_1))
    (is (= (meta x) (meta body) {:name 'y}))
    (is (= tx '✳)))

  (is (= (quotation '(::stx/ascribe y z))
         '(::stx/ascribe y z)))

  (let [[p [x tx] body] (quotation (list 'Π '[⇧ A] (fn [x] 'B)))]
    (is (= p 'Π))
    (is (= x '_1))
    (is (= (meta x) {:name '⇧}))
    (is (= tx 'A))
    (is (= body 'B))))

(deftest test-norm
  (is (= (norm 'a)
         'a))

  (is (= (norm '(λ [x ✳] x))
         '(λ [_1 ✳] _1)))

  (is (= (norm '[[(λ [x ✳] (λ [y ✳] [x y])) z] t])
         '[z t]))

  (is (= (norm '[(λ [x ✳] (λ [y ✳] [x y])) z])
         '(λ [_1 ✳] [z _1])))

  (is (= (norm '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c])
         'c))

  (is (= (norm '[[[(λ [x ✳] (λ [y ✳] (λ [x ✳] [x y]))) a] b] c])
         '[c b]))

  (is (= (norm '(λ [x ✳] [(λ [y ✳] (λ [z ✳] [[x y] z])) a]))
         '(λ [_1 ✳] (λ [_2 ✳] [[_1 a] _2]))))

  (is (= (norm '[(λ [a ✳] [a b]) c])
         '[c b]))

  (is (= (norm '(Π [⇧ A] B))
         '(Π [_1 A] B)))

  (let [term '[(λ [a T] (Π [b T] [b a])) b]]
    (is (stx/alpha-eq? (first (beta-norm/beta-step term))
                       (norm term))))


  (let [term '(Π [a T] (Π [a T] (Π [a T] [a a])))]
    (is (stx/alpha-eq? (first (beta-norm/beta-step term))
                       (norm term))))

  (let [term '(Π [C' ✳]
               (Π [⇧ (Π [⇧' (Π [C ✳] (Π [⇧ (Π [⇧' A]
                                            (Π [⇧'' B]
                                             C))]
                                      C))]
                      (Π [⇧'' C] C'))]
                C'))]
    (is (stx/alpha-eq? (first (beta-norm/beta-step term))
                       (norm term)))))

(deftest test-equiv-beta-red
  "These tests are the same as those in norm-test"
  (is (= (norm '[(λ [x ✳] [x x]) y])
         '[y y]))

  (is (= (norm '[(λ [x ✳] x) y])
         'y))

  (is (= (norm '[[(λ [x ✳] x) y] z])
         '[y z]))

  (is (= (norm '(λ [y [(λ [x □] x) ✳]] y))
         '(λ [_1 ✳] _1)))

  (is (= (norm '[z [(λ [x ✳] x) y]])
         '[z y]))

  (is (= (norm '(::stx/ascribe z [(λ [x ✳] x) y]))
         '(::stx/ascribe z y)))

  (is (= (norm '(::stx/ascribe [(λ [x ✳] x) y] z))
         '(::stx/ascribe y z)))

  (is (= (norm '[x y])
         '[x y]))

  (is (= (norm '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y]))
         '(λ [_1 ✳] _1))))

(deftest test-delta-nbe
  (is (= (norm defenv/empty-env [] 'x)
         'x))

  (is (= (norm (defenv/mkenv {'test (defenv/map->Definition
                                     '{:arity 1
                                       :tag :definition
                                       :params [[x ✳]]
                                       :parsed-term [x x]
                                       :opts {}})})
           []
           '[y (test [t t])])
         '[y [[t t] [t t]]]))

  (is (= (norm (defenv/mkenv {'test (defenv/map->Definition
                                     '{:arity 2
                                       :tag :definition
                                       :params [[x ✳] [y ✳]]
                                       :parsed-term [x [y x]]
                                       :opts {}})})
           []
           '[y (test [t t] u)])
         '[y [[t t] [u [t t]]]]))

  (is (= (norm (defenv/mkenv {'test (defenv/map->Definition
                                     '{:arity 2
                                       :tag :definition
                                       :params [[x ✳] [y ✳]]
                                       :parsed-term [x [y x]]
                                       :opts {:opaque true}})})
           []
           '[y (test [t t] u)])
         '[y (test [t t] u)])))

