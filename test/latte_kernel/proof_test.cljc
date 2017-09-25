
(ns latte-kernel.proof-test
  (:require #?(:clj [clojure.test :refer :all]
               :cljs [cljs.test :as t :refer-macros [is deftest testing]])
            [latte-kernel.presyntax :as parse]
            [latte-kernel.defenv :as defenv]
            [latte-kernel.proof :refer :all]))

(def ctx1 (let [[_ [_ ctx1]] (elab-declare defenv/empty-env [] [] {} 'A '✳ {})]
            ctx1))

(def vdeps1 (let [[_ [_ _ vdeps1]] (elab-declare defenv/empty-env [] [] {} 'A '✳ {})]
             vdeps1))

(def ctx2 (let [[_ [_ ctx2]] (elab-declare defenv/empty-env ctx1 vdeps1 {} 'B '✳ {})]
            ctx2))

(def vdeps2 (let [[_ [_ _ vdeps2]] (elab-declare defenv/empty-env ctx1 vdeps1 {} 'B '✳ {})]
              vdeps2))

(def ctx3 (let [[_ [_ ctx3]] (elab-declare defenv/empty-env ctx2 vdeps2 {}
                                           'f (second (parse/parse-term defenv/empty-env '(==> A B))) {})]
            ctx3))

(def vdeps3 (let [[_ [_ _ vdeps3]] (elab-declare defenv/empty-env ctx2 vdeps2 {}
                                           'f (second (parse/parse-term defenv/empty-env '(==> A B))) {})]
            vdeps3))

(def ctx4 (let [[_ [_ ctx4]] (elab-declare defenv/empty-env ctx3 vdeps3 {} 'x 'A {})]
            ctx4))

(def vdeps4 (let [[_ [_ _ vdeps4]] (elab-declare defenv/empty-env ctx3 vdeps3 {} 'x 'A {})]
              vdeps4))

(deftest test-elab-declare
  ;; Step 0:
  ;; local-defs={}   ctx=[]    var-deps=[]    def-uses={} 
  
  (is (= (elab-declare defenv/empty-env [] [] {} 'A '✳ {})
         '[:ok [[{} {}] ([A ✳]) ([A #{}]) {}]]))

  ;; Step 1: [:declare A *]
  ;; local-defs={}   ctx=[[A *]]   var-deps=[[A #{}]]    def-uses={}
  
  (is (= ctx1 '([A ✳])))

  (is (= vdeps1 '([A #{}])))
  
  ;; Step 2: [:declare B *]
  ;; local-defs={}   ctx=[[B *] [A *]]   var-deps=[[B #{}] [A #{}]]    def-uses={} 
  (is (= ctx2 '([B ✳] [A ✳])))
  (is (= vdeps2 '([B #{}] [A #{}])))
  
  ;; Step 3: [:declare f (==> A B)]
  ;; local-defs={}   ctx=[[f (==> A B)] [B *] [A *]]   var-deps=[[f #{}][B #{}] [A #{}]]  def-uses={} 
  (is (= ctx3 '([f (Π [⇧ A] B)] [B ✳] [A ✳])))
  (is (= vdeps3 '([f #{}] [B #{}] [A #{}])))

  ;; Step 4: [:declare x A]
  ;; local-defs={}   ctx=[[x A] [f (==> A B)] [B *] [A *]]   var-deps=[[x #{}][f #{}][B #{}] [A #{}]]  def-uses={}
  (is (= ctx4 '([x A] [f (Π [⇧ A] B)] [B ✳] [A ✳])))
  (is (= vdeps4 '([x #{}] [f #{}] [B #{}] [A #{}]))))


(deftest test-update-var-deps
  (is (= (update-var-deps vdeps4 '<a> 'f)
         '[[x #{}] [f #{<a>}] [B #{}] [A #{}]]))

  (is (= (-> vdeps4
             (update-var-deps '<a> 'f)
             (update-var-deps '<a> (second (parse/parse-term defenv/empty-env '(==> A B)))))
         '[[x #{}] [f #{<a>}] [B #{<a>}] [A #{<a>}]]))

  )

(let [state5 (second (elab-have defenv/empty-env ctx4 vdeps4 {} '<a> (second (parse/parse-term defenv/empty-env '(==> A B))) 'f {}))
      [def-env5 ctx5 vdeps5 dfuses5] state5]
  (def def-env5 def-env5)
  (def ctx5 ctx5)
  (def vdeps5 vdeps5)
  (def dfuses5 dfuses5))

(let [state6 (second (elab-have def-env5 ctx5 vdeps5 dfuses5 '<b> 'B (second (parse/parse-term def-env5 '(<a> x))) {}))
      [def-env6 ctx6 vdeps6 dfuses6] state6]
  (def def-env6 def-env6)
  (def ctx6 ctx6)
  (def vdeps6 vdeps6)
  (def dfuses6 dfuses6))

(deftest test-ref-uses-in-term
  (is (= (ref-uses-in-term (:parsed-term (second (defenv/fetch-definition def-env6 '<a>))))
         #{}))
  
  (is (= (ref-uses-in-term (:parsed-term (second (defenv/fetch-definition def-env6 '<b>))))
         '#{<a>})))

(deftest test-update-def-uses
  (is (= (update-def-uses dfuses5 '<b> (:parsed-term (second (defenv/fetch-definition def-env6 '<b>))))
         '{<a> #{<b>}})))

(deftest test-elab-have
  ;; Step 5 : [:have <a> (==> A B) f]
  ;; local-defs={<a>:=f::(==> A B)}
  ;; ctx=[[x A] [f (==> A B)] [B *] [A *]]
  ;; var-deps=[[x #{}][f #{<a>}][B #{<a>}] [A #{<a>}]]  def-uses={<a> #{}}
  
  (is (= ctx5 ctx4))

  (is (defenv/registered-definition? def-env5 '<a>))

  (is (= (second(defenv/fetch-definition def-env5 '<a> true))
         '#latte_kernel.defenv.Definition{:name <a>, :params [], :arity 0, :parsed-term f, :type (Π [⇧ A] B)}))

  (is (= vdeps5
         '[[x #{}] [f #{<a>}] [B #{<a>}] [A #{<a>}]]))

  (is (= dfuses5
         '{<a> #{}}))
  
  ;; Step 6 : [:have <b> B (<a> x)]
  ;; local-defs={<a>:=f::(==> A B)
  ;;             <b>:=(<a> x)::B}
  ;; ctx=[[x A] [f (==> A B)] [B *] [A *]]
  ;; var-deps=[[x #{<b>}][f #{<a>}][B #{<a>,<b>}] [A #{<a>}]]  def-uses={<a> #{<b>}, <b> #{}}
  (is (= ctx6 ctx5))

  (is (defenv/registered-definition? def-env6 '<a>))
  (is (defenv/registered-definition? def-env6 '<b>))

  (is (= (second(defenv/fetch-definition def-env6 '<b> true))
         '#latte_kernel.defenv.Definition{:name <b>, :params [], :arity 0, :parsed-term [(<a>) x], :type B}))

  (is (= vdeps6
         '[[x #{<b>}] [f #{<a>}] [B #{<a> <b>}] [A #{<a>}]]))

  (is (= dfuses6
         '{<a> #{<b>}, <b> #{}}))

  )


(deftest test-abstract-local-defs
  (is (= (:params (second (defenv/fetch-definition (abstract-local-defs def-env6 (second (first vdeps6)) 'x 'A) '<b>)))
         '[[x A]])))




;;{
;; An example (low-level) proof script


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
