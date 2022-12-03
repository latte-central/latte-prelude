(ns latte-prelude.algebra
  "Basic algebraic definitions."

  (:refer-clojure :exclude [and or not])
  
  (:require
   [latte-kernel.norm :as norm]
   
   [latte.utils :refer [decomposer set-opacity!]]
   [latte.core :as latte :refer [definition defthm defimplicit defimplicit*
                                 assume have qed proof]]
   
   [latte-prelude.utils :as pu]
   [latte-prelude.prop :as p :refer [<=> and or not]]
   [latte-prelude.equal :as eq :refer [equal]])
)


(definition associative
  "The property of law `⋅` to be associative.
This makes the type `T` associated to the law a *semigroup*."
  [[?T :type] [⋅ (==> T T T)]]
  (∀ [x y z T]
     (equal (⋅ (⋅ x y) z)
            (⋅ x (⋅ y z)))))

(definition identity-left
  "The property of an element `e` to be a left-identity of a law `⋅`."
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (∀ [x T] (equal (⋅ e x) x)))


(definition identity-right
  "The property of an element `e` to be a left-identity of a law `⋅`."
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (∀ [x T] (equal (⋅ x e) x)))

