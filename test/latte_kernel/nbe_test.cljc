(ns latte-kernel.nbe-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest]])
            [latte-kernel.nbe :as nbe :refer :all]
            [latte-kernel.syntax :as stx]))

(deftest test-evaluation
  (is (= (evaluation 'a)
         [::nbe/var ::nbe/a]))

  (is (= (evaluation '(λ [a ✳] a))
         [::nbe/lambda '(fn [a] a)]))

  (let [[kw1 [kw2 f] v] (evaluation '[(λ [a ✳] a) b])]
    (is (= kw1 ::nbe/app))
    (is (= kw2 ::nbe/lambda))
    (is (= (meta f)
           {::nbe/var-name ::nbe/a
            ::nbe/var-type [::nbe/sort ::nbe/✳]}))
    (is (= v [::nbe/var ::nbe/b]))
    (is (fn? (eval f)))
    (is (= ((eval f) v) v)))

  (is (= (evaluation '[a b])
         [::nbe/app
           [::nbe/var ::nbe/a]
           [::nbe/var ::nbe/b]]))

  (let [[a1 [a2 [l1 f1] v1] v2] (evaluation '[[(λ [a ✳] (λ [b ✳] [a b])) c] d])
        [f arg [l2 f2]] f1]
    (is (= a1 a2 ::nbe/app))
    (is (= l1 ::nbe/lambda))
    (is (= v1 [::nbe/var ::nbe/c]))
    (is (= v2 [::nbe/var ::nbe/d]))
    (is (= f 'fn))
    (is (= arg '[a]))
    (is (= l2 ::nbe/lambda))
    (is (fn? (eval f1)))
    (is (= (meta f1)
           {::nbe/var-name ::nbe/a
            ::nbe/var-type [::nbe/sort ::nbe/✳]}))
    (is (= (first f2) 'fn)))

  (let [[a1 [a2 [a3 f1]]] (evaluation '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c])
        [l1 [_ _ [l2 [_ _ [l3 [_ _ body]]]]]] f1]
    (is (= a1 a2 a3 ::nbe/app))
    (is (= l1 l2 l3 ::nbe/lambda))
    (is (= body 'x)))

  (let [[as [v1 v2] [ap [l f] [v3 v4]]] (evaluation '(::stx/ascribe z [(λ [x ✳] x) y]))]
     (is (= as ::nbe/asc))
     (is (= v1 v3 ::nbe/var))
     (is (= v2 ::nbe/z))
     (is (= v4 ::nbe/y))
     (is (= ap ::nbe/app))
     (is (= l ::nbe/lambda))
     (is (= f '(fn [x] x))))

  (let [[kw v] (evaluation '(Π [⇧ A] B))]
    (is (= kw ::nbe/pi))
    (is (= v [::nbe/var ::nbe/B]))
    (is (= (meta v) {::nbe/var-name ::nbe/⇧, ::nbe/var-type [::nbe/var ::nbe/A]})))

  (is (= (evaluation '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B))))))
         [:latte-kernel.nbe/pi
          [:latte-kernel.nbe/pi
           [:latte-kernel.nbe/pi
            [:latte-kernel.nbe/pi
             [:latte-kernel.nbe/pi 'B]]]]])))

(deftest test-normalisation
  (is (= (evaluation 'a)
         (normalisation (evaluation 'a))))

  (let [[_ f1] (evaluation '(λ [y ✳] y))
        [_ f2] (normalisation (evaluation '(λ [y ✳] y)))]
    (is (= f1 f2))
    (is (= (meta f1) (meta f2))))

  (is (= (normalisation [::nbe/app
                         [::nbe/lambda
                           (with-meta '(fn [x] x)
                             {::nbe/var-name ::nbe/x
                              ::nbe/var-type [::nbe/sort ::nbe/✳]})]
                         [::nbe/var 'y]])
         [::nbe/var 'y]))

  (is (= (normalisation [::nbe/app
                         [::nbe/var 'y]
                         [::nbe/var 'z]])
         [::nbe/app
           [::nbe/var 'y]
           [::nbe/var 'z]]))

  (is (= (normalisation (evaluation '[[[(λ [x ✳] (λ [x ✳] (λ [x ✳] x))) a] b] c]))
         ;; We can see here how long the nbe-specific syntax can become
         (normalisation [::nbe/app
                         [::nbe/app
                          [::nbe/app
                           [::nbe/lambda
                            (with-meta
                             (list 'fn ['x]
                              [::nbe/lambda
                               (with-meta
                                (list 'fn ['x]
                                  [::nbe/lambda
                                   (with-meta '(fn [x] x)
                                     {::nbe/var-name ::nbe/x
                                      ::nbe/var-type [::nbe/sort ::nbe/✳]})])
                                {::nbe/var-name ::nbe/x
                                 ::nbe/var-type [::nbe/sort ::nbe/✳]})])
                             {::nbe/var-name ::nbe/x
                              ::nbe/var-type [::nbe/sort ::nbe/✳]})]
                           [::nbe/var ::nbe/a]]
                          [::nbe/var ::nbe/b]]
                         [::nbe/var ::nbe/c]])
        [::nbe/var ::nbe/c]))

  (let [[_ f] (normalisation (evaluation '[(λ [x ✳] (λ [y ✳] [x y])) a]))]
    (is (fn? f))
    (is (= (f [::nbe/var ::nbe/b])
           [::nbe/app
            [::nbe/var ::nbe/a]
            [::nbe/var ::nbe/b]])))

  (let [[_ [_ v1] [_ v2]] (normalisation (evaluation '(::stx/ascribe z [(λ [x ✳] x) y])))]
    (is (= v1 ::nbe/z))
    (is (= v2 ::nbe/y)))

  (is (= (normalisation (evaluation '(Π [⇧ A] B)))
         (evaluation '(Π [⇧ A] B))))

  (is (= (normalisation (evaluation '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B)))))))
         (evaluation '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B)))))))))

(deftest test-quotation
  (is (= (quotation [::nbe/var 'y])
         'y))

  (is (= (quotation [::nbe/app
                     [::nbe/var 'y]
                     [::nbe/var 'z]])
         '[y z]))

  (is (= (quotation [::nbe/lambda
                 ;; The symbol used for the actual function instanciation
                 ;; doesn't matter since we use the metadatum to convert back.
                     (with-meta '(fn [x] x)
                       {::nbe/var-name ::nbe/y
                        ::nbe/var-type [::nbe/sort ::nbe/✳]})])
         '(λ [y ✳] y)))

  (is (= (quotation [::nbe/asc [::nbe/var ::nbe/z] [::nbe/var ::nbe/y]])
         '(::stx/ascribe z y)))

  (is (= (quotation [::nbe/pi
                     (with-meta [::nbe/var ::nbe/B]
                       {::nbe/var-name ::nbe/⇧
                        ::nbe/var-type [::nbe/var ::nbe/A]})])
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

  (is (= (norm '(Π [⇧ A] B))
         '(Π [⇧ A] B)))

  (is (= (norm '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B))))))
         '(Π [A ✳] (Π [B ✳] (Π [⇧ (Π [⇧ A] B)] (Π [⇧ A] (Π [⇧ A] B))))))))

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
