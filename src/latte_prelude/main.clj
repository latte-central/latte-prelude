(ns latte-prelude.main
  (:gen-class)
  (:require [latte.main :refer [latte-main]]))

(defn -main [& args]
  (latte-main args "latte-prelude"
              '[latte-prelude.prop
                latte-prelude.equal
                latte-prelude.quant
                latte-prelude.classic
                latte-prelude.fun
                latte-prelude.algebra]))




