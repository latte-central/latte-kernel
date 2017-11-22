(ns latte-kernel.defs
  "Definition handling."
  (:require [latte-kernel.defenv :as defenv]
            [latte-kernel.syntax :as stx]))


(defn mk-params-renaming
  ([params] (mk-params-renaming params 1))
  ([params level]
   (loop [params params, level level, nparams [], ren {}]
     (if (seq params)
       (let [nparam (symbol (str "%" level))]
         (recur (rest params) (inc level) (conj nparams nparam) (assoc ren (first params) nparam)))
       [nparams ren]))))

;; (mk-params-renaming '[A B C D E])
;; => [[%1 %2 %3 %4 %5] {A %1, B %2, C %3, D %4, E %5}]

(defn mkdef
  "Make a definition with parameter renaming."
  [name params term type opts]
  (let [[params' ren] (mk-params-renaming params)
        term' (stx/renaming term ren)
        type' (stx/renaming type ren)]
    (defenv/->Definition name params' (count params') term' type' opts)))



