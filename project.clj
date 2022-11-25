(defproject latte-kernel "1.0b10-SNAPSHOT"
  :description "The (very) small kernel of the LaTTe proof assistant"
  :url "https://github.com/latte-central/latte-kernel.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}}
          ;;:namespaces []
  :plugins [[lein-cljsbuild "1.1.8"]]
  :cljsbuild {:builds [{:source-paths ["src-cljs"]
                        :compiler {:output-to "resources/public/js/main.js"
                                   :optimizations :whitespace
                                   :pretty-print true}}]}
  :profiles {:dev {:dependencies
                   [[org.clojure/clojure "1.11.1"]
                    [org.clojure/clojurescript "1.11.60"]
                    [cider/piggieback "0.5.3"]
                    [lambdaisland/kaocha "1.71.1119"]
                    [nubank/matcher-combinators "3.7.0"]]}
             :test {:dependencies [[org.clojure/clojure "1.11.1"]]}})
