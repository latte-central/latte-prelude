(ns latte-prelude.quant
  "Basic definitions and theorems about the universal
  and existential quantifiers.

  Note that for the universal quantifier, it is a primitive of the
  calculus of constructions, hence Latte.

  The elimination rule for ∀ (for all) is application, and introduction
  is through lambda-abstraction."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation defimplicit
                                          example proof qed assume have]]

            [latte.utils :as u]
            [latte-prelude.prop :as p :refer [and]]
            [latte-prelude.equal :as eq :refer [equal equality]]))

(defn decompose-forall-type [def-env ctx t]
  (u/decomposer
   (fn [t]
     (if (clojure.core/and (seq t)
                           (= (count t) 3)
                           (= (first t) 'Π))
       (let [[_ [x A] B] t]
         [[x A] B])
       (throw (ex-info "Cannot infer a universal quantification" {:type t}))))
   def-env ctx t))

(definition ex
  "The encoding for the existential quantifier.

`(ex P)` encodes the existential quantification

> there exists an element of (implicit) type `T` such that the predicate
> `P` holds for this element.

Remark: this is a second-order, intuitionistic definition that
 is more general than the definition in classical logic.
"
  [?T :type, P (==> T :type)]
  (forall [α :type]
    (==> (forall [x T] (==> (P x) α))
         α)))

(defn decompose-ex-type [def-env ctx t]
  (u/decomposer
   (fn [t]
     (if (clojure.core/and (seq t)
                           (= (count t) 3)
                           (= (first t) #'latte-prelude.quant/ex-def))
       [(second t) (nth t 2)]
       (throw (ex-info "Cannot infer an existential type" {:type t}))))
   def-env ctx t))

(defnotation exists
  "The existential quantification  `(exists [x T] P)`
 is a shortcut for `(ex (lambda [x T] P))`, corresponding
 to the usual notation for existential quantification: ∃x:T.(P x)

> there exists an `x` of type `T` such that `(P x)` is true."
  [bindings body]
  [:ok (list #'ex (list 'lambda bindings body))])

(alter-meta! #'exists update-in [:style/indent] (fn [_] [1 :form :form]))

(defthm ex-elim-rule
  "The (intuitionistic) elimination rule for the existential quantifier."
  [?T :type, P (==> T :type), A :type]
  (==> (ex P)
       (forall [x T] (==> (P x) A))
       A))

(proof 'ex-elim-rule-thm
  (assume [H1 (ex P)
           H2 (forall [x T] (==> (P x) A))]
    (have <a> (==> (forall [x T] (==> (P x) A))
                   A) :by (H1 A))
    (have <b> A :by (<a> H2)))
  (qed <b>))

(defimplicit ex-elim
  "An elimination rule written `(ex-elim ex-proof x-proof)` with:
  - `ex-proof` of type `(ex P)` for some property `P` if type `(==> T :type)`, 
  - `x-proof` a proof of `(forall [x T] (==> (P x) A))` for
 some goal statement `A`. Thanks to [[ex-elim-rule]] the goal `A` is concluded."
  [def-env ctx [ex-proof ex-proof-type] [x-proof x-proof-type]]
  (let [[T P] (decompose-ex-type def-env ctx ex-proof-type)
        [_ Q] (decompose-forall-type def-env ctx x-proof-type)
        [_ A] (p/decompose-impl-type def-env ctx Q)]
    [[(list #'ex-elim-rule-thm T P A) ex-proof] x-proof]))

(example [[T :type] [A :type] [P (==> T :type)] [Hex (ex P)]]
    (==> (forall [x T] (==> (P x) A))
         A)
  ;; proof
  (assume [Hx (forall [x T] (==> (P x) A))]
    (have <a> A :by (ex-elim Hex Hx)))
  (qed <a>))

(defthm ex-intro
  "The introduction rule for the existential quantifier."
  [?T :type, P (==> T :type), x T]
  (==> (P x)
       (ex P)))

(proof 'ex-intro-thm
  (assume [H (P x)
           A :type
           y (forall [z T] (==> (P z) A))]
    (have <a> (==> (P x) A) :by (y x))
    (have <b> A :by (<a> H)))
  (qed <b>))

;; ex is made opaque
(u/set-opacity! #'ex-def true)

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



