(ns latte-kernel.nbe-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest]])
            [latte-kernel.nbe :as nbe :refer :all]
            [latte-kernel.syntax :as stx]
            [latte-kernel.norm :as beta-norm]))

(deftest test-evaluation
  (is (= (evaluation 'a)
         ::nbe/a))

  (is (= (evaluation '(λ [a ✳] a))
         [::nbe/lambda ::nbe/a ::nbe/✳ `(fn [~'a] (normalisation ~'a))]))

  (let [[kw1 l v1] (evaluation '[(λ [a ✳] a) b])
        [kw2 v2 t f] l]
    (is (= kw1 ::nbe/app))
    (is (= kw2 ::nbe/lambda))
    (is (= v2 ::nbe/a))
    (is (= t ::nbe/✳))
    (is (= v1 ::nbe/b))
    (is (fn? (eval f)))
    (is (= ((eval f) v1) v1)))

  (is (= (evaluation '[a b])
         [::nbe/app ::nbe/a ::nbe/b]))

  (let [[a1 [a2 l v1] v2] (evaluation '[[(λ [a ✳] (λ [b ✳] [a b])) c] d])
        [l1 v3 t1 [f arg [n [l2 v4 t2 f2]]]] l]
    (is (= a1 a2 ::nbe/app))
    (is (= l1 ::nbe/lambda))
    (is (= v1 ::nbe/c))
    (is (= v2 ::nbe/d))
    (is (= v3 ::nbe/a))
    (is (= v4 ::nbe/b))
    (is (= t1 t2 ::nbe/✳))
    (is (= f `fn))
    (is (= arg '[a]))
    (is (= n `normalisation))
    (is (= l2 ::nbe/lambda))
    (is (fn? (eval (last l))))
    (is (= (first f2) `fn)))

  (let [[a1 [a2 [a3 f v1] v2] v3] (evaluation '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c])
        [l1 arg1 _ [_ _ [n1 [l2 arg2 _ [_ _ [n2 [l3 arg3 _ [_ _ [n3 body]]]]]]]]] f]
    (is (= a1 a2 a3 ::nbe/app))
    (is (= l1 l2 l3 ::nbe/lambda))
    (is (= n1 n2 n3 `normalisation))
    (is (= arg1 ::nbe/x))
    (is (= arg2 ::nbe/x'))
    (is (= arg3 ::nbe/x''))
    (is (= body 'x'')))

  (is (= (evaluation '(λ [a ✳] [(λ [b ✳] [a b]) c]))
         [::nbe/lambda ::nbe/a ::nbe/✳
          `(fn [~'a]
             (normalisation [::nbe/app
                             [::nbe/lambda ::nbe/b ::nbe/✳
                               (fn [~'b] (normalisation [::nbe/app ~'a ~'b]))]
                             ::nbe/c]))]))

  (let [[as v1 [ap [l v2 t1 f] v3]] (evaluation '(::stx/ascribe z [(λ [x ✳] x) y]))]
     (is (= as ::nbe/asc))
     (is (= v1 ::nbe/z))
     (is (= v2 ::nbe/x))
     (is (= v3 ::nbe/y))
     (is (= ap ::nbe/app))
     (is (= l ::nbe/lambda))
     (is (= t1 ::nbe/✳))
     (is (= f `(fn [~'x] (normalisation ~'x)))))

  (let [[kw v t body] (evaluation '(Π [⇧ A] B))]
    (is (= kw ::nbe/pi))
    (is (= v ::nbe/⇧))
    (is (= t ::nbe/A))
    (is (= body ::nbe/B)))

  (is (= (evaluation '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B))))))
         [::nbe/pi ::nbe/A ::nbe/✳
          [::nbe/pi ::nbe/B ::nbe/✳
           [::nbe/pi ::nbe/⇧ [::nbe/pi ::nbe/⇧ ::nbe/A ::nbe/B]
            [::nbe/pi ::nbe/⇧' ::nbe/A
             [::nbe/pi ::nbe/⇧'' ::nbe/A ::nbe/B]]]]])))

(deftest test-normalisation
  (is (= (evaluation 'a)
         (normalisation (evaluation 'a))))

  (let [l1 (evaluation '(λ [y ✳] y))
        l2 (normalisation (evaluation '(λ [y ✳] y)))]
    (is (= (take 3 l1) (take 3 l2))))

  (is (= (normalisation (evaluation '[(λ [x ✳] x) y]))
         ::nbe/y))

  (is (= (normalisation [::nbe/app ::nbe/y ::nbe/z])
         [::nbe/app ::nbe/y ::nbe/z]))

  (is (= (normalisation (evaluation '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c]))
         ;; We can see here how long the nbe-specific syntax can become
         (normalisation [::nbe/app
                         [::nbe/app
                          [::nbe/app
                           [::nbe/lambda ::nbe/x ::nbe/✳
                            `(fn [~'x]
                               (nbe/normalisation
                                [::nbe/lambda ::nbe/x ::nbe/✳
                                 (fn [~'x]
                                   (nbe/normalisation
                                    [::nbe/lambda ::nbe/x ::nbe/✳
                                     (fn [~'x] (nbe/normalisation ~'x))]))]))]
                           ::nbe/a]
                          ::nbe/b]
                         ::nbe/c])
         ::nbe/c))

  (let [[_ _ _ f] (normalisation (evaluation '[(λ [x ✳] (λ [y ✳] [x y])) a]))]
    (is (fn? f))
    (is (= (f ::nbe/b)
           [::nbe/app ::nbe/a ::nbe/b])))

  (let [[_ v1 v2] (normalisation (evaluation '(::stx/ascribe z [(λ [x ✳] x) y])))]
    (is (= v1 ::nbe/z))
    (is (= v2 ::nbe/y)))

  (is (= (normalisation (evaluation '(Π [⇧ A] B)))
         (evaluation '(Π [⇧ A] B))))

  (is (= (normalisation (evaluation '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B)))))))
         (evaluation '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B)))))))))

(deftest test-quotation
  (is (= (quotation ::nbe/y)
         (quotation 'y)
         'y))

  (is (= (quotation [::nbe/app ::nbe/y ::nbe/z])
         '[y z]))

  (is (= (quotation [::nbe/lambda ::nbe/y ::nbe/✳
                      (fn [x] x)])
         '(λ [y ✳] y)))

  (is (= (quotation [::nbe/asc ::nbe/z ::nbe/y])
         '(::stx/ascribe z y)))

  (is (= (quotation [::nbe/pi ::nbe/⇧ ::nbe/A ::nbe/B])
         '(Π [⇧ A] B))))

(deftest test-norm
;   (is (= (norm 'a)
;          'a))
;
;   (is (= (norm '(λ [x ✳] x))
;          '(λ [x ✳] x)))
;
;   (is (= (norm '[[(λ [x ✳] (λ [y ✳] [x y])) z] t])
;          '[z t]))
;
;   (is (= (norm '[(λ [x ✳] (λ [y ✳] [x y])) z])
;          '(λ [y ✳] [z y])))
;
;   (is (= (norm '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c])
;          'c))
;
;   (is (= (norm '[[[(λ [x ✳] (λ [y ✳] (λ [x ✳] [x y]))) a] b] c])
;          '[c b]))
;
;   (is (= (norm '(λ [x ✳] [(λ [y ✳] (λ [z ✳] [[x y] z])) a]))
;          '(λ [x ✳] (λ [z ✳] [[x a] z]))))
;
;   (is (= (norm '[(λ [a ✳] [a b]) c]))
;       '[c b])
;
;   (is (= (norm '(Π [⇧ A] B))
;          '(Π [⇧ A] B)))
;
;   (is (= (norm '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B))))))
;          '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧' A] (Π [⇧'' A] B)))))))
;
;   (let [term '[(λ [y T]
;                 (Π [α ✳]
;                  (Π [⇧ (Π [x' (Π [⇧ T] ✳)]
;                         (Π [⇧' [(λ [x (Π [⇧ T] ✳)]
;                                  ("prop/and" [X x] [x y]))
;                                 x']]
;                          α))]
;                   α)))
;                x']]
;     (is (stx/alpha-eq? (norm term)
;           (first (beta-norm/beta-step term)))))
;
;   (let [term '[(λ [a T] (Π [b T] [b a])) b]]
;     (is (stx/alpha-eq? (norm term)
;           (first (beta-norm/beta-step term)))))
;
;   (let [term '(Π [a T] (Π [a T] (Π [a T] [a a])))
;         res1 (stx/alpha-norm (norm term))
;         res2 (stx/alpha-norm (first (beta-norm/beta-step term)))]
;     (is (= res1 res2)))
;
;   (let [term '(Π [x' T]
;                 [(λ [y T]
;                   (Π [⇧ (Π [x' ✳] ;3
;                           (Π [⇧' [(λ [x ✳]
;                                     ("prop/and" [X x] [x y]))
;                                   x']]
;                            y))]
;                      y))
;                  x'])
;         res1 (stx/alpha-norm (norm term))
;         res2 (stx/alpha-norm (first (beta-norm/beta-step term)))]
;     (is (= res1 res2)))

  (let [term '(Π [C' ✳]
               (Π [⇧ (Π [⇧' (Π [C ✳] (Π [⇧ (Π [⇧' A]
                                            (Π [⇧'' B]
                                             C))]
                                      C))]
                      (Π [⇧'' C] C'))]
                C'))
        res1 (stx/alpha-norm (norm term))
        res2 (stx/alpha-norm (first (beta-norm/beta-step term)))
        _ (println "Expected:" res2)
        _ (println "Actual:  " res1)]
    (is (= res1 res2))))

;; smallest bugging form
; (Π [C' ✳]
;  (Π [⇧ (Π [⇧' (Π [C ✳] (Π [⇧ (Π [⇧' A]
;                               (Π [⇧'' B]
;                                C))]
;                         C))]
;         (Π [⇧'' C] C'))]
;   C'))


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
