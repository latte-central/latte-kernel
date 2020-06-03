(ns latte-kernel.syntax-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :as prestx]
            [latte-kernel.syntax :refer :all]))

(deftest test-term-reduce
  (is (= (term-reduce {} 42 '(λ [x t] (test x y z)))
         42))

  (is (= (term-reduce {} nil '[::prestx/host-constant 42])
         [::prestx/host-constant 42]))

  (is (= (term-reduce {:var (fn [vs v] (conj vs v))} #{} '(λ [x t] (test x y z)))
         '#{x y z t})))

(deftest test-free-vars
  (is (= (free-vars 'x)
         #{'x}))

  (is (= (free-vars '[x y])
         #{'x 'y}))

  (is (= (free-vars '(λ [x t] [x [y z]]))
         #{'t 'y 'z}))

  (is (= (free-vars '(Π [x t] [x [y z]]))
         #{'t 'y 'z}))

  (is (= (free-vars '(λ [x t] (test x y z)))
         '#{t y z}))

  (is (= (free-vars '(:latte-kernel.syntax/ascribe x [y z]))
         '#{x y z}))

  (is (= (free-vars '(λ [x y] (:latte-kernel.syntax/ascribe x [y z])))
         '#{y z})))

(deftest test-vars- ;; nameclash
  (is (= (vars 'x)
       #{'x}))

  (is (= (vars '[x y])
         #{'x 'y}))

  (is (= (vars '(λ [x t] (test x [y z])))
         #{'t 'x 'y 'z}))

  (is (= (vars '(Π [x t] (test x [y z])))
         #{'t 'x 'y 'z}))

  (is (= (vars '(:latte-kernel.syntax/ascribe x [y z]))
         '#{x y z}))

  (is (= (vars '(λ [x y] (:latte-kernel.syntax/ascribe x [y z])))
         '#{x y z})))

(deftest test-bound-vars
  (is (= (bound-vars 'x)
         #{}))

  (is (= (bound-vars '[x y])
         #{}))

  (is (= (bound-vars '(λ [x t] (test x [y z])))
         #{'x}))

  (is (= (bound-vars '(λ [x t] (test t [y z])))
         #{}))

  (is (= (bound-vars '(Π [x t] (test x [y z])))
         #{'x}))

  (is (= (bound-vars '(:latte-kernel.syntax/ascribe x [y z]))
         '#{}))

  (is (= (bound-vars '(λ [x y] (:latte-kernel.syntax/ascribe x [y z])))
         '#{x})))

(deftest test-mk-fresh
  (is (= (mk-fresh 'x '#{x x' x''})
         'x'''))

  (is (=(mk-fresh 'x '#{x x' x'' x'''})
        'x-4)))

(deftest test-subst
  (is (= (subst 'x {'x '✳})
         '✳))

  (is (= (subst 'y {'x '✳})
         'y))

  (is (= (subst '[y x] {'x '✳})
         '[y ✳]))

  (is (= (subst '(:latte-kernel.syntax/ascribe x y) '{x ✳, y z})
         '(:latte-kernel.syntax/ascribe ✳ z)))

  (is (= (subst '[x (λ [x ✳] (test x y z y))] {'x '✳, 'y '□})
         '[✳ (λ [x' ✳] (test x' □ z □))]))

  (is (= (subst '[x (Π [x ✳] [y x])] {'x '✳, 'y 'x})
         '[✳ (Π [x' ✳] [x x'])]))

  (is (= (subst '(λ [x ✳] (test x y (λ [x ✳] (test x y z)) y)) {'x ':replace})
         '(λ [x' ✳] (test x' y (λ [x'' ✳] (test x'' y z)) y))))

  (is (= (subst '(λ [x ✳] (test x y (λ [x ✳] (test x y x')) y)) {'x :replace-x
                                                                 'x' :replace-x'})
         '(λ [x'' ✳] (test x'' y (λ [x''' ✳] (test x''' y :replace-x')) y))))

  (is (= (subst '(test x y (λ [x ✳] (test x y x')) y) {'x :replace-x
                                                       'x' :replace-x'})
         '(test :replace-x y (λ [x'' ✳] (test x'' y :replace-x')) y)))

  (is  ;; XXX: this comes from a very subtile bug !
   (= (subst '(Π [⇧ (Π [x' T] (Π [⇧ (Π [x T] (Π [⇧ [X x]] [[R x] x']))] [R z]))]
                 [R z]) 'z 'x)
      '(Π [⇧ (Π [x' T] (Π [⇧' (Π [x'' T] (Π [⇧'' [X x'']] [[R x''] x']))] [R x]))] [R x]))))

(deftest test-alpha-norm
  (is (= (alpha-norm 'x)
         'x))

  (is (= (alpha-norm '(λ [x ✳] x))
         '(λ [_1 ✳] _1)))

  (is (= (alpha-norm '[x (λ [x ✳] (test x y [x z]))])
         '[x (λ [_1 ✳] (test _1 y [_1 z]))])))

(deftest test-alpha-eq?
  (is (alpha-eq? '(λ [x ✳] x)
                 '(λ [y ✳] y)))
  ;; the type part of an ascription is not
  ;; considered for alpha-equivalence
  (is (alpha-eq? '(:latte-kernel.syntax/ascribe (λ [x ✳] x) (∀ [A □] A))
                 '(λ [z ✳] z))))

(deftest test-top-assumption
  (is (= (top-assumption '(Π [x T] U)) '[T U]))
  (is (= (top-assumption '(λ [x T] U)) '[nil (λ [x T] U)])))

(deftest test-assumptions
  (is (= (assumptions '(Π [x T] U)) '[T]))
  (is (= (assumptions '(Π [x T] (Π [y U] V))) '[T U])))

(deftest test-readable-term
  (let [y1 (with-meta '_1 {:name 'y})
        term (list 'λ [y1 '✳] y1)]
    (is (= (readable-term term)
           '(λ [y ✳] y)))
    (is (= (alpha-norm (readable-term term))
           '(λ [_1 ✳] _1))))

  (let [x1 (with-meta '_1 {:name 'x})]
    (is (= (readable-term (list 'λ [x1 '✳] [x1 'x]))
           '(λ [x' ✳] [x' x]))))

  (let [arr (with-meta '_1 {:name '⇧})]
    (is (= (readable-term (list 'Π [arr 'A] 'B))
           '(Π [⇧ A] B))))

  (let [x1 (with-meta '_1 {:name 'x})
        x2 (with-meta '_2 {:name 'x})
        term (list 'λ [x1 'A] (list 'λ [x2 'B] [[x1 x2] 'x]))]
    (is (= (readable-term term)
           '(λ [x' A] (λ [x'' B] [[x' x''] x]))))))
