(ns latte-kernel.nbe-test
  (:require #?(:clj [clojure.test :refer [is deftest]]
               :cljs [cljs.test :as t :refer-macros [is deftest]])
            [latte-kernel.nbe :as nbe :refer :all]
            [latte-kernel.syntax :as stx]
            [latte-kernel.norm :as beta-norm]))

(deftest test-evaluation
  (is (= (evaluation 'a)
         'a))

  (let [[kw1 l v1] (evaluation '[(λ [a ✳] a) b])
        [kw2 b v2 t f] l]
    (is (= kw1 ::nbe/app))
    (is (= kw2 ::nbe/binder))
    (is (= b 'λ))
    (is (= v2 'a))
    (is (= t '✳))
    (is (= v1 'b))
    (is (fn? f))
    (is (= (f v1) v1)))

  (is (= (evaluation '[a b])
         [::nbe/app 'a 'b]))

  (let [[a1 [a2 l v1] v2] (evaluation '[[(λ [a ✳] (λ [b ✳] [a b])) c] d])
        [b1 b2 v3 t f] l]
    (is (= a1 a2 ::nbe/app))
    (is (= b1 ::nbe/binder))
    (is (= b2 'λ))
    (is (= v1 'c))
    (is (= v2 'd))
    (is (= v3 'a))
    (is (= t '✳))
    (is (fn? f)))

  (let [[a1 [a2 [a3 [b1 b2 arg t _] v1] v2] v3] (evaluation '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c])]
    (is (= a1 a2 a3 ::nbe/app))
    (is (= b1 ::nbe/binder))
    (is (= b2 'λ))
    (is (= arg 'x))
    (is (= t '✳)))

  (let [[as v1 [ap [b1 b2 v2 t1 _] v3]] (evaluation '(::stx/ascribe z [(λ [x ✳] x) y]))]
     (is (= as ::nbe/asc))
     (is (= v1 'z))
     (is (= v2 'x))
     (is (= v3 'y))
     (is (= ap ::nbe/app))
     (is (= b1 ::nbe/binder))
     (is (= b2 'λ))
     (is (= t1 '✳)))

  (let [[kw1 b1 v1 t1 _] (evaluation '(Π [⇧ A] B))
        [kw2 b2 v2 t2 _] (evaluation '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B))))))]
    (is (= kw1 kw2 ::nbe/binder))
    (is (= b1 b2 'Π))
    (is (= t1 v2 'A))
    (is (= v1 '⇧))
    (is (= t2 '✳))))

(deftest test-normalisation
  (is (= (evaluation 'a)
         (normalisation (evaluation 'a))))

  (let [l1 (evaluation '(λ [y ✳] y))
        l2 (normalisation (evaluation '(λ [y ✳] y)))]
    (is (= (take 3 l1) (take 3 l2))))

  (is (= (normalisation (evaluation '[(λ [x ✳] x) y]))
         'y))

  (is (= (normalisation [::nbe/app 'y 'z])
         [::nbe/app 'y 'z]))

  (is (= (normalisation (evaluation '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c]))
         'c))

  (let [[_ _ _ _ f] (normalisation (evaluation '[(λ [x ✳] (λ [y ✳] [x y])) a]))]
    (is (fn? f))
    (is (= (f 'b)
           [::nbe/app 'a 'b])))

  (let [[_ v1 v2] (normalisation (evaluation '(::stx/ascribe z [(λ [x ✳] x) y])))]
    (is (= v1 'z))
    (is (= v2 'y))))

(deftest test-quotation
  (is (= (quotation #{'y} 'y)
         'y))

  (is (= (quotation #{'y 'z} [::nbe/app 'y 'z])
         '[y z]))

  (is (= (quotation #{} [::nbe/binder 'λ 'y '✳ (fn [x] x)])
         '(λ [y ✳] y)))

  (is (= (quotation #{'y 'z} [::nbe/asc 'y 'z])
         '(::stx/ascribe y z)))

  (is (= (quotation #{'B} [::nbe/binder 'Π '⇧ 'A (fn [x] 'B)])
         '(Π [⇧ A] B))))

(deftest test-norm
  (is (= (norm 'a)
         'a))

  (is (= (norm '(λ [x ✳] x))
         '(λ [x ✳] x)))

  (is (= (norm '[[(λ [x ✳] (λ [y ✳] [x y])) z] t])
         '[z t]))

  (is (= (norm '[(λ [x ✳] (λ [y ✳] [x y])) z])
         '(λ [y ✳] [z y])))

  (is (= (norm '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c])
         'c))

  (is (= (norm '[[[(λ [x ✳] (λ [y ✳] (λ [x ✳] [x y]))) a] b] c])
         '[c b]))

  (is (= (norm '(λ [x ✳] [(λ [y ✳] (λ [z ✳] [[x y] z])) a]))
         '(λ [x ✳] (λ [z ✳] [[x a] z]))))

  (is (= (norm '[(λ [a ✳] [a b]) c]))
      '[c b])

  (is (= (norm '(Π [⇧ A] B))
         '(Π [⇧ A] B)))

  (is (= (norm '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B))))))
         '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧' A] (Π [⇧'' A] B)))))))

  (let [term '[(λ [y T]
                (Π [α ✳]
                 (Π [⇧ (Π [x' (Π [⇧ T] ✳)]
                        (Π [⇧' [(λ [x (Π [⇧ T] ✳)]
                                 ("prop/and" [X x] [x y]))
                                x']]
                         α))]
                  α)))
               x']]
    (is (stx/alpha-eq? (norm term)
          (first (beta-norm/beta-step term)))))

  (let [term '[(λ [a T] (Π [b T] [b a])) b]]
    (is (stx/alpha-eq? (norm term)
          (first (beta-norm/beta-step term)))))

  (let [term '(Π [a T] (Π [a T] (Π [a T] [a a])))
        res1 (stx/alpha-norm (norm term))
        res2 (stx/alpha-norm (first (beta-norm/beta-step term)))]
    (is (= res1 res2)))

  (let [term '(Π [x' T]
                [(λ [y T]
                  (Π [⇧ (Π [x' ✳] ;3
                          (Π [⇧' [(λ [x ✳]
                                    ("prop/and" [X x] [x y]))
                                  x']]
                           y))]
                     y))
                 x'])
        res1 (stx/alpha-norm (norm term))
        res2 (stx/alpha-norm (first (beta-norm/beta-step term)))]
    (is (= res1 res2)))

  (let [term '(Π [C' ✳]
               (Π [⇧ (Π [⇧' (Π [C ✳] (Π [⇧ (Π [⇧' A]
                                            (Π [⇧'' B]
                                             C))]
                                      C))]
                      (Π [⇧'' C] C'))]
                C'))
        res1 (stx/alpha-norm (norm term))
        res2 (stx/alpha-norm (first (beta-norm/beta-step term)))]
    (is (= res1 res2)))

  (let [term '("core/int")
        res1 (stx/alpha-norm (norm term))
        res2 (stx/alpha-norm (first (beta-norm/beta-step term)))]
    (is (= res1 res2))))

(deftest test-equiv-beta-red
  "These tests are the same as those in norm-test"
  (is (= (norm '[(λ [x ✳] [x x]) y])
         '[y y]))

  (is (= (norm '[(λ [x ✳] x) y])
         'y))

  (is (= (norm '[[(λ [x ✳] x) y] z])
         '[y z]))

  (is (= (norm '(λ [y [(λ [x □] x) ✳]] y))
         '(λ [y ✳] y)))

  (is (= (norm '[z [(λ [x ✳] x) y]])
         '[z y]))

  (is (= (norm '(::stx/ascribe z [(λ [x ✳] x) y]))
         '(::stx/ascribe z y)))

  (is (= (norm '(::stx/ascribe [(λ [x ✳] x) y] z))
         '(::stx/ascribe y z)))

  (is (= (norm '[x y])
         '[x y]))

  (is (= (norm '(λ [y [(λ [x □] x) ✳]] [(λ [x ✳] x) y]))
         '(λ [y ✳] y))))
