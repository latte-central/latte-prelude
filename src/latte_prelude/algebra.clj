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
     (equal (⋅ x (⋅ y z))
            (⋅ (⋅ x y) z))))

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

(definition cancel-left
  "The property of law `⋅` to be *left-cancellable*"
  [[?T :type] [⋅ (==> T T T)]]
  (∀ [x y z T] (==> (equal (⋅ x y) (⋅ x z))
                    (equal y z))))

(definition cancel-right
  "The property of law `⋅` to be *right-cancellable*"
  [[?T :type] [⋅ (==> T T T)]]
  (∀ [x y z T] (==> (equal (⋅ y x) (⋅ z x))
                    (equal y z))))


(definition commutative
    "The property of law `⋅` to be commutative."
  [[?T :type] [⋅ (==> T T T)]]
  (∀ [x y T] (equal (⋅ x y) (⋅ y x))))

(defthm comm-identity-right
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (==> (commutative ⋅)
       (identity-left ⋅ e)
       (identity-right ⋅ e)))

(proof 'comm-identity-right-thm
  (assume [Hcom _ 
           Hleft _]
    (assume [x T]
      (have <a> (equal (⋅ e x) x) :by (Hleft x))
      (have <b> (equal (⋅ x e) (⋅ e x)) :by (Hcom x e))
      (have <c> (equal (⋅ x e) x) :by (eq/eq-trans <b> <a>))))
  (qed <c>))

(defthm comm-identity-left
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (==> (commutative ⋅)
       (identity-right ⋅ e)
       (identity-left ⋅ e)))

(proof 'comm-identity-left-thm
  (assume [Hcom _ 
           Hright _]
    (assume [x T]
      (have <a> (equal (⋅ x e) x) :by (Hright x))
      (have <b> (equal (⋅ e x) (⋅ x e)) :by (Hcom e x))
      (have <c> (equal (⋅ e x) x) :by (eq/eq-trans <b> <a>))))
  (qed <c>))

(definition monoid
  "The law `⋅` together with the unit element `e` form a monoid."
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (and* (associative ⋅)
        (identity-left ⋅ e)
        (identity-right ⋅ e)))

(definition has-inverse
  "The law `.` with identity `e` has inverse elements."
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (==> (identity ⋅ e) 
       (∀ [x T] (q/exists [ix T] (and (equal (⋅ x ix) e)
                                      (equal (⋅ ix x) e))))))

(definition group
  "The law `⋅` together with the unit element `e` form a group."
  [[?T :type] [⋅ (==> T T T)] [e T]]
  (and* (associative ⋅)
        (identity-left ⋅ e)
        (identity-right ⋅ e)
        (has-inverse ⋅ e)))



  


