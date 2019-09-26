(defproject latte-prelude "1.0b6-SNAPSHOT"
  :description "The core library for the LaTTe proof assistant."
  :url "https://github.com/fredokun/latte-prelude.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.1"]
                 [latte "1.0b6-SNAPSHOT"]]
  :main latte-prelude.main
  :aliases {"certify" ["run" ":certify"]
            "clear-cert" ["run" ":clear-cert"]}
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-prelude.prop
                       latte-prelude.equal
                       latte-prelude.quant
                       latte-prelude.classic
                       latte-prelude.fun]}
  :profiles {:uberjar {:aot [latte-prelude.main]}}
  :plugins [[lein-codox "0.10.7"]])






