(defproject latte-kernel "1.0"
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
                   [[org.clojure/clojure "1.12.145"]
                    [org.clojure/clojurescript "1.12.145"]
                    [cider/piggieback "0.6.0"]
                    [lambdaisland/kaocha "1.91.1392"]
                    [nubank/matcher-combinators "3.10.0"]]}
             :test {:dependencies [[org.clojure/clojure "1.12.5"]]}})
