
(ns latte-kernel.norm-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
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

  (is (= (beta-red '(:latte-kernel.syntax/ascribe z [(λ [x ✳] x) y]))
         '(:latte-kernel.syntax/ascribe z y)))
  
  (is (= (beta-red '(:latte-kernel.syntax/ascribe [(λ [x ✳] x) y] z))
         '(:latte-kernel.syntax/ascribe y z)))
  
  (is (= (beta-red '[x y])
         '[x y])))
