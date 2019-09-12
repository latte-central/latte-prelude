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

`(ex T P)` encodes the existential quantification

> there exists an element of type `T` such that the predicate
> `P` holds for this element.

Remark: this is a second-order, intuitionistic definition that
 is more general than the definition in classical logic.
"
  [[P (==> ?T :type)]]
  (forall [α :type]
    (==> (forall [x T] (==> (P x) α))
         α)))

(defnotation exists
  "The existential quantification  `(exists [x T] P)`
 is a shortcut for `(ex T (lambda [x T] P))`, corresponding
 to the usual notation for existential quantification: ∃x:T.(P x)

> there exists an `x` of type `T` such that `(P x)` is true."
  [bindings body]
  [:ok (list #'ex (list 'lambda bindings body))])

(alter-meta! #'exists update-in [:style/indent] (fn [_] [1 :form :form]))

(defthm ex-elim-thm
  "The (intuitionistic) elimination rule for the existential quantifier."
  [[T :type] [P (==> T :type)] [A :type]]
  (==> (ex P)
       (forall [x T] (==> (P x) A))
       A))

(proof 'ex-elim-thm
  (assume [H1 (ex P)
           H2 (forall [x T] (==> (P x) A))]
    (have <a> (==> (forall [x T] (==> (P x) A))
                   A) :by (H1 A))
    (have <b> A :by (<a> H2)))
  (qed <b>))

(defimplicit ex-elim
  "The elimination rule for the existential quantifier, an implicit version of [[ex-elim-thm]]."
  [def-env ctx [P P-ty] [A A-ty]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-ty)]
    (list #'ex-elim-thm T P A)))

(defthm ex-intro-thm
  "The introduction rule for the existential quantifier."
  [[T :type] [P (==> T :type)] [x T]]
  (==> (P x)
       (ex P)))

(proof 'ex-intro-thm
  (assume [H (P x)
           A :type
           y (forall [z T] (==> (P z) A))]
    (have <a> (==> (P x) A) :by (y x))
    (have <b> A :by (<a> H)))
  (qed <b>))

(defimplicit ex-intro
  "The introduction rule for the existential quantifier, an implicit version of [[ex-intro-thm]]."
  [def-env ctx [P P-ty] [x x-ty]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-ty)]
    (list #'ex-intro-thm T P x)))

;; ex is made opaque
(u/set-opacity! #'ex-intro true)

(definition single-prop
  "The constraint that \"there exists at most\"..."
  [[T :type] [P (==> T :type)]]
  (forall [x y T]
    (==> (P x)
         (P y)
         (equal x y))))

(defimplicit single
  "The constraint that \"there exists at most\"... (an implicit version of [[single-prop]])."
  [def-env ctx [P P-type]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-type)]
    (list #'single-prop T P)))

(defthm single-intro-thm
  "Introduction rule for [[single]]."
  [[T :type] [P (==> T :type)]]
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

(defimplicit single-intro
  "There proof that there is a single `x` such that `(P x)`, cf [[single-intro-thm]]."
  [def-env ctx [P P-ty]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-ty)]
    (list #'single-intro-thm T P)))

(defthm single-elim-thm
  "Elimination rule for [[single]]."
  [[T :type] [P (==> T :type)] [x T] [y T]]
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

(defimplicit single-elim
  "Elimination rule for [[single]], cf. [[single-elim-thm]]."
  [def-env ctx [P P-ty] [x x-ty] [y y-ty]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-ty)]
    (list #'single-elim-thm T P x y)))

;; single can now be made opaque
(u/set-opacity! #'single true)

(definition unique-prop
  "The constraint that \"there exists a unique\" ..."
  [[T :type] [P (==> T :type)]]
  (and (ex P)
       (single P)))

(defimplicit unique
  "The constraint that \"there exists a unique\" ... (an implicit version of [[unique-prop]])."
  [def-env ctx [P P-type]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-type)]
    (list #'unique-prop T P)))

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
  [[T :type] [P (==> T :type)] [u (unique P)]]
  (P (the P u)))

(defimplicit the-prop
  "The property of `the`, from [[the-prop-ax]]."
  [def-env ctx [P P-type] [u u-type]]
  (let [[T _] (p/decompose-impl-type def-env ctx P-type)]
    (list #'the-prop-ax T P u)))

(defthm the-lemma-thm
  "The unique element is ... unique."
  [[T :type] [P (==> T :type)] [u (unique P)]]
  (forall [y T]
    (==> (P y)
         (equal y (the P u)))))

(proof 'the-lemma-thm
  (have <a> (single-prop T P) :by (p/and-elim-right u))
  (have <b> (P (the-ax T P u)) :by (the-prop P u))
  (assume [y T
           Hy (P y)]
    (have <c> (==> (P y)
                   (P (the P u))
                   (equal y (the P u))) :by (<a> y (the P u)))
    (have <d> (equal y (the P u)) :by (<c> Hy <b>)))
  (qed <d>))

