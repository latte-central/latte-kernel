
(ns latte-kernel.proof-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :as parse]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.proof :refer :all]))

(def ctx1 (let [[_ [_ ctx1]] (elab-declare defenv/empty-env [] 'A '✳ {})]
            ctx1))

(def ctx2 (let [[_ [_ ctx2]] (elab-declare defenv/empty-env ctx1 'B '✳ {})]
            ctx2))

(def ctx3 (let [[_ [_ ctx3]] (elab-declare defenv/empty-env ctx2 'f (second (parse/parse-term defenv/empty-env '(==> A B))) {})]
            ctx3))

(def ctx4 (let [[_ [_ ctx4]] (elab-declare defenv/empty-env ctx3 'x 'A {})]
            ctx4))

(deftest test-elab-declare
  (is (= (elab-declare defenv/empty-env [] 'A '✳ {})
         '[:ok [[{} {}] ([A ✳])]]))

  (is (= ctx1 '([A ✳])))

  (is (= ctx2 '([B ✳] [A ✳])))

  (is (= ctx3 '([f (Π [⇧ A] B)] [B ✳] [A ✳])))

  (is (= ctx4 '([x A] [f (Π [⇧ A] B)] [B ✳] [A ✳]))))

(def state5 (second (elab-have defenv/empty-env ctx4 '<a> (second (parse/parse-term defenv/empty-env '(==> A B))) 'f {})))

(def state6 (second (elab-have (first state5) (second state5) '<b> 'B (second (parse/parse-term (first state5) '(<a> x))) {})))


(deftest test-elab-have
  (let [[def-env5 ctx5] state5]
    (is (= ctx5 ctx4))

    (is (defenv/registered-definition? def-env5 '<a>))

    (is (= (second(defenv/fetch-definition def-env5 '<a> true))
           '#latte_kernel.defenv.Definition{:name <a>, :params [], :arity 0, :parsed-term f, :type (Π [⇧ A] B)})))

  (let [[def-env6 ctx6] state6]
    (is (= ctx6 ctx4))

    (is (defenv/registered-definition? def-env6 '<a>))
    (is (defenv/registered-definition? def-env6 '<b>))

    (is (= (second(defenv/fetch-definition def-env6 '<b> true))
           '#latte_kernel.defenv.Definition{:name <b>, :params [], :arity 0, :parsed-term [(<a>) x], :type B}))))

(deftest test-local-defs-with-free-occurrence
  (is (= (local-defs-with-free-occurrence (second (first state6)) 'x)
         #{'<b>})))

(deftest test-ref-uses-in-term
  (is (= (ref-uses-in-term (:parsed-term (second (defenv/fetch-definition (first state6) '<a>))))
         #{}))
  
  (is (= (ref-uses-in-term (:parsed-term (second (defenv/fetch-definition (first state6) '<b>))))
         '#{<a>})))



;;{
;; An example (low-level) proof script

;; Step 0:

;; local-defs={}   ctx=[]    var-deps=[]    def-uses={} 

;; Step 1 :

;; [:declare A *]

;; local-defs={}   ctx=[[A *]]   var-deps=[[A #{}]]    def-uses={} 

;; Step 2 :

;; [:declare B *]

;; local-defs={}   ctx=[[B *] [A *]]   var-deps=[[B #{}] [A #{}]]    def-uses={} 

;; Step 3 :

;; [:declare f (==> A B)]

;; local-defs={}   ctx=[[f (==> A B)] [B *] [A *]]   var-deps=[[f #{}][B #{}] [A #{}]]  def-uses={} 

;; Step 4 :

;; [:declare x A]

;; local-defs={}   ctx=[[x A] [f (==> A B)] [B *] [A *]]   var-deps=[[x #{}][f #{}][B #{}] [A #{}]]  def-uses={}

;; Step 5 :

;; [:have <a> (==> A B) f]

;; local-defs={<a>:=f::(==> A B)}
;; ctx=[[x A] [f (==> A B)] [B *] [A *]]
;; var-deps=[[x #{}][f #{<a>}][B #{<a>}] [A #{<a>}]]  def-uses={<a> #{}}

;; Step 6 :

;; [:have <b> B (<a> x)]

;; local-defs={<a>:=f::(==> A B)
;;             <b>:=(<a> x)::B}
;; ctx=[[x A] [f (==> A B)] [B *] [A *]]
;; var-deps=[[x #{<b>}][f #{<a>}][B #{<a>,<b>}] [A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}

;; Step 7 :

;; [:discharge x]

;; local-defs={<a>:=f::(==> A B)
;;             <b>(x::A):=(<a> x)::B}
;; ctx=[[f (==> A B)] [B *] [A *]]
;; var-deps=[[f #{<a>}][B #{<a>,<b>}] [A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}

;; Step 8 :

;; [:discharge f]

;; local-defs={<a>(f::(==> A B)):=f::(==> (==> A B) (==> A B))
;;             <b>(f::(==> A B), x::A):=((<a> f) x)::B}
;; ctx=[[B *] [A *]]
;; var-deps=[[B #{<a>,<b>}] [A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}

;; Step 9 :

;; [:discharge B]

;; local-defs={<a>(B::*, f::(==> A B)):=f::(forall [B *] (==> (==> A B) (==> A B)))
;;             <b>(B::*, f::(==> A B), x::A):=(forall [B *] ((<a> B f) x))::(==> B B)}
;; ctx=[A *]]
;; var-deps=[[A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}

;; Step 10 :

;; [:discharge A]

;; local-defs={<a>(A::*, B::*, f::(==> A B)):=f::(forall [A B *] (==> (==> A B) (==> A B)))
;;             <b>(A::*, B::*, f::(==> A B), x::A):=(forall [A B *] ((<a> A B f) x))::(==> B B)}
;; ctx=[A *]]
;; var-deps=[[A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}

;; Step 11 :

;; [:qed <a>]

;; <a>::(forall [A B *] (==> (==> A B) (==> A B)))


;;}
