(ns latte-prelude.quant
  "Basic definitions and theorems about the universal
  and existential quantifiers.

  Note that for the universal quantifier, it is a primitive of the
  calculus of constructions, hence Latte.

  The elimination rule for ∀ (for all) is application, and introduction
  is through lambda-abstraction."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation defimplicit
                                          proof qed assume have]]

            [latte.utils :as u]
            [latte-prelude.prop :as p :refer [and]]
            [latte-prelude.equal :as eq :refer [equal equality]]))

(definition ex
  "The encoding for the existential quantifier.

`(ex P)` encodes the existential quantification

> there exists an element of (implicit) type `T` such that the predicate
> `P` holds for this element.

Remark: this is a second-order, intuitionistic definition that
 is more general than the definition in classical logic.
"
  [?T :type, P (==> T :type)]
  (Σ [t T] (P t)))

(defnotation exists
  "The existential quantification  `(exists [x T] P)`
 is a shortcut for `(ex (lambda [x T] P))`, corresponding
 to the usual notation for existential quantification: ∃x:T.(P x)

> there exists an `x` of type `T` such that `(P x)` is true."
  [bindings body]
  [:ok (list #'ex (list 'lambda bindings body))])

(alter-meta! #'exists update-in [:style/indent] (fn [_] [1 :form :form]))

(defthm ex-elim
  "The (intuitionistic) elimination rule for the existential quantifier."
  [?T :type, P (==> T :type), A :type]
  (==> (ex P)
       (forall [x T] (==> (P x) A))
       A))

(proof 'ex-elim-thm
  (qed
    (λ [p (Σ [t T] (P t))]
      (λ [f (Π [x T] (==> (P x) A))]
        (f (pr1 p) (pr2 p))))))

(defthm ex-intro
  "The introduction rule for the existential quantifier."
  [?T :type, P (==> T :type), x T]
  (==> (P x)
       (ex P)))

(proof 'ex-intro-thm (qed (λ [t (P x)] (pair x t))))

(definition single
  "The constraint that \"there exists at most\"..."
  [?T :type, P (==> T :type)]
  (forall [x y T]
    (==> (P x)
         (P y)
         (equal x y))))

(defthm single-intro
  "Introduction rule for [[single]]."
  [?T :type, P (==> T :type)]
  (==> (forall [x y T]
               (==> (P x)
                    (P y)
                    (equal x y)))
       (single P)))

(proof 'single-intro-thm
  (assume [H (forall [x y T]
               (==> (P x)
                    (P y)
                    (equal x y)))]
    (have <a> (single P) :by H))
  (qed <a>))

(defthm single-elim
  "Elimination rule for [[single]]."
  [?T :type, P (==> T :type), x T, y T]
  (==> (single P)
       (P x)
       (P y)
       (equal x y)))

(proof 'single-elim-thm
  (assume [H1 (single P)
           H2 (P x)
           H3 (P y)]
    (have <a> (equal x y)
          :by (H1 x y H2 H3)))
  (qed <a>))

(definition unique
  "The constraint that \"there exists a unique\" ..."
  [?T :type, P (==> T :type)]
  (and (ex P)
       (single P)))

(defaxiom the-ax
  "The unique element descriptor.

  `(the T P u)` defines the unique inhabitant of type
 `T` satisfying the predicate `P`. This is provided
 thanks to the uniqueness proof `u` (of type `(unique T P)`.
"
  [[T :type] [P (==> T :type)] [u (unique P)]]
  T)

(defimplicit the
 "The unique element descriptor.

  `(the P u)` defines the unique object
 satisfying the predicate `P`. This is provided
 thanks to the uniqueness proof `u` (of type `(unique P)`.
This is the implicit version of the axiom [[the-ax]]."
  [def-env ctx [P P-type] [u u-type]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-type)]
    (list #'the-ax T P u)))

(defaxiom the-prop-ax
  "The property of the unique element descriptor."
  [T :type, P (==> T :type), u (unique P)]
  (P (the P u)))

(defimplicit the-prop
  "The property of `the`, from [[the-prop-ax]]."
  [def-env ctx [P P-type] [u u-type]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-type)]
    (list #'the-prop-ax T P u)))

(defthm the-lemma
  "The unique element is ... unique."
  [?T :type, P (==> T :type), u (unique P)]
  (forall [y T]
          (==> (P y)
               (equal y (the P u)))))

(proof 'the-lemma-thm
  (have <a> (single P) :by (p/and-elim-right u))
  (have <b> (P (the P u)) :by (the-prop P u))
  (assume [y T
           Hy (P y)]
    (have <c> (equal y (the P u))
          :by ((single-elim P y (the P u)) <a> Hy <b>)))
  (qed <c>))
