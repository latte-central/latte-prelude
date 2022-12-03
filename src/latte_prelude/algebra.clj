(ns latte-prelude.algebra
  "Basic algebraic definitions."

  (:refer-clojure :exclude [and or not identity])
  
  (:require
   [latte-kernel.norm :as norm]
   
   [latte.utils :refer [decomposer set-opacity!]]
   [latte.core :as latte :refer [definition defthm defimplicit defimplicit*
                                 assume have qed proof try-proof]]
   
   [latte-prelude.utils :as pu]
   [latte-prelude.prop :as p :refer [<=> and and* or not]]
   [latte-prelude.equal :as eq :refer [equal]]
   [latte-prelude.quant :as q :refer [single]])
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
  "The property of an element `e` to be a right-identity of a law `⋅`."
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (∀ [x T] (equal (⋅ x e) x)))

(definition identity
  "The property of an element `e` to be an identity of a law `⋅`"
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (and (identity-left ⋅ e)
       (identity-right ⋅ e)))

(defthm identity-single
  "There is at most one identity element of a law `⋅`"
  [[?T :type] [⋅ (==> T T T)]]
  (single (identity-def T ⋅)))

(proof 'identity-single-thm
  (assume [e1 T
           e2 T
           He1 (identity ⋅ e1)
           He2 (identity ⋅ e2)]
    (have <a> (equal (⋅ e1 e2) e2)
          :by ((p/and-elim-left He1) e2))
    (have <b> (equal (⋅ e1 e2) e1)
          :by ((p/and-elim-right He2) e1))
    (have <c> (equal e1 e2)
          :by (eq/eq-trans (eq/eq-sym <b>)
                           <a>)))
  (qed <c>))

(definition monoid
  "The law `⋅` together with the unit element `e` for a monoid."
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (and* (associative ⋅)
        (identity-left ⋅ e)
        (identity-right ⋅ e)))


           


