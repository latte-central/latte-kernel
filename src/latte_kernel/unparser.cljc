(ns latte-kernel.unparser
  (:require [latte-kernel.utils :as u]
            [latte-kernel.syntax :as stx]))

(def +unparser-registry+ (atom {:fundamental []
                                :standard []
                                :user []
                                :unparsers {}}))


(declare unregister-unparser!)

(defn register-unparser!
  ([ident unparser] (register-unparser! :user ident unparser))
  ([category ident unparser]
   (when (get (:unparsers @+unparser-registry+) ident)
     (unregister-unparser! ident))
   (when (not (contains? #{:fundamental :standard :user} category))
     (throw (ex-info "Wrong unparser category." {:category category})))
   (swap! +unparser-registry+ (fn [registry]
                                (-> registry
                                    (update category #(conj % ident))
                                    (assoc-in [:unparsers ident] unparser))))))

;; (register-unparser! :fundamental :impl (fn [term] [term false]))
;; (register-unparser! :fundamental :impl2 (fn [term] [term false]))

(defn unregister-unparser! [ident]
  (when (not (contains? (:unparsers @+unparser-registry+) ident))
    (throw (ex-info "No such unparser." {:ident ident})))
  (swap! +unparser-registry+ (fn [registry]
                               {:fundamental (u/vremove #(= % ident) (:fundamental registry))
                                :standard (u/vremove #(= % ident) (:standard registry))
                                :user (u/vremove #(= % ident) (:standard registry))
                                :unparsers (dissoc (:unparsers registry) ident)})))

;; (unregister-unparser! :impl2)
;; (unregister-unparser! :impl)

(defn unparse-term-once [registry order term]
  (if (seq order)
    (let [unparser (get-in registry [:unparsers (first order)])
          [term' modified?] (unparser term)]
      (if modified?
        [term' true]
        (recur registry (rest order) term)))
    ;; no more unparser to try
    [term false]))

(defn unparse-term-rec [registry order term]
  (cond
    (stx/binder? term)
    (let [[binder [x ty] body] term
          [ty' ty-modif?] (unparse-term-rec registry order ty)
          [body' body-modif?] (unparse-term-rec registry order body)
          [term' term-modif?] (unparse-term-once registry order (list binder [x ty'] body'))]
      [term' (or ty-modif? body-modif? term-modif?)])
    (stx/let? term)
    (let [[_ [x ty xval] body] term
          [ty' ty-modif?] (unparse-term-rec registry order ty)
          [xval' xval-modif?] (unparse-term-rec registry order xval)
          [body' body-modif?] (unparse-term-rec registry order body)
          [term' term-modif?] (unparse-term-once registry order (list 'let [x ty' xval'] body'))]
      [term' (or ty-modif? xval-modif? body-modif? term-modif?)])
    (stx/app? term)
    (let [[term1 term2] term
          [term1' term1-modif?] (unparse-term-rec registry order term1)
          [term2' term2-modif?] (unparse-term-rec registry order term2)
          [term' term-modif?] (unparse-term-once registry order [term1' term2'])]
      [term' (or term1-modif? term2-modif? term-modif?)])
    (stx/ascription? term)
    (let [[asc term1 term2] term
          [term1' term1-modif?] (unparse-term-rec registry order term1)
          [term2' term2-modif?] (unparse-term-rec registry order term2)
          [term' term-modif?] (unparse-term-once registry order (list asc term1' term2'))]
      [term' (or term1-modif? term2-modif? term-modif?)])
    (stx/ref? term)
    (let [[dname & args] term
          [args' args-modif?] (reduce (fn [[args modif?] arg]
                                        (let [[arg' arg-modif?] (unparse-term-rec registry order arg)]
                                          [(conj args arg') (or modif? arg-modif?)])) [[] false] args)
          [term' term-modif?] (unparse-term-once registry order (list* dname args'))]
      [term' (or args-modif? term-modif?)])
    :else ;; non-recursive cases
    (unparse-term-once registry order term)))

(defn unparse [term]
  (let [order (concat (:fundamental @+unparser-registry+)
                      (:standard @+unparser-registry+)
                      (:user @+unparser-registry+))
        [term' modif?] (unparse-term-rec @+unparser-registry+ order term)]
    ;;; XXX: do something else if modif? is true?
    term'))

;; Fundamental unparsers

(defn prod-impl-unparser [term]
  (if (stx/prod? term)
    (let [[_ [x A] B] term]
      (if (not (contains? (stx/free-vars B) x))
        (if (and (sequential? B)
                 (not-empty B)
                 (= (first B) '==>))
          [(list* '==> A (rest B)) true]
          [(list '==> A B) true])
        [term false]))
    [term false]))

(defn install-fundamental-unparsers! []
  (register-unparser! :fundamental :prod-impl prod-impl-unparser))

