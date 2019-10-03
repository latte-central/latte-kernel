(ns codox
  "Codox Runner to be operated via Clojure CLI

   Usage: clj -A:codox"
  (:gen-class)
  (:require [codox.main :as codox]))

(def options
  {:source-paths ["src"]
   :output-path "docs"
   :metadata {:doc/format :markdown}
   :namespaces []
   :name "LaTTe"
   :license {:name "MIT Licence"
             :url "http://opensource.org/licenses/MIT"}
   #_#_
   :root-path "src"
   :description "LaTTe : a Laboratory for Type Theory Experiments"
   :version "1.0b7-SNAPSHOT"})

(defn -main []
  (println "Codox Starting")
  (codox/generate-docs options))
