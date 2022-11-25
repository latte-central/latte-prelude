(ns latte-prelude.quant
  "Basic definitions and theorems about the universal
  and existential quantifiers.

  Note that for the universal quantifier, it is a primitive of the
  calculus of constructions, hence Latte.

  The elimination rule for ∀ (for all) is application, and introduction
  is through lambda-abstraction."

  (:refer-clojure :exclude [and or not])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation defimplicit
                                          example proof try-proof qed assume have]]

            [latte.utils :as u]
            [latte-prelude.prop :as p :refer [and or not]]
            [latte-prelude.equal :as eq :refer [equal equality]]
            [latte-prelude.classic :as classic]
            [latte.search :as search]))

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

(defthm ex-impl
  "Use of implication in existentials."
  [[?T :type] [P Q (==> T :type)]]
  (==> (ex P)
       (forall [x T] (==> (P x) (Q x)))
       (ex Q)))

(proof 'ex-impl-thm
  (assume [HP _
           Himpl _]
    (assume [x T Hx (P x)]
      (have <a> (Q x) :by (Himpl x Hx))
      (have <b> (ex Q) :by ((ex-intro Q x) <a>)))
    (have <c> (ex Q) :by (ex-elim HP <b>)))
  (qed <c>))

(defthm not-ex-elim
  "The classical elimination rule for negation of existence."
  [?T :type, P (==> T :type)]
  (==> (not (ex P))
       (forall [x T] (not (P x)))))

(proof 'not-ex-elim-thm
  (assume [Hnex (not (ex P))]
    (assume [x T]
      (assume [Hyes (P x)]
        (have <a1> (ex P) :by ((ex-intro P x) Hyes))
        (have <a> p/absurd :by (Hnex <a1>)))))
  (qed <a>))

(defthm not-ex-intro
  "The introduction rule for negation of existence."
  [?T :type, P (==> T :type)]
  (==> (forall [x T] (not (P x)))
       (not (ex P))))

(proof 'not-ex-intro-thm
  (assume [H (forall [x T] (not (P x)))]
    (assume [Hcontra (ex P)]
      (assume [x T Hx (P x)]
        (have <a> p/absurd :by (H x Hx)))
      (have <b> p/absurd :by (ex-elim Hcontra <a>))))
  (qed <b>))

(defthm not-not-elim
  "A classical (i.e. non-intuitionistic) elimination rule for double existential negation."
  [?T :type, P (==> T :type)]
  (==> (not (exists [x T] (not (P x))))
       (forall [x T] (P x))))

(proof 'not-not-elim-thm
  (assume [Hnex _]
    (assume [x T]
      (assume [Hyes (P x)]
        (have <a> (P x) :by Hyes))
      (assume [Hno (not (P x))]
        (have <b1> (exists [x T] (not (P x)))
              :by ((ex-intro (lambda [y T] (not (P y))) x) Hno))
        (have <b2> p/absurd :by (Hnex <b1>))
        (have <b> (P x) :by (<b2> (P x))))
      (have <c> (or (P x) (not (P x)))
            :by (classic/excluded-middle-ax (P x)))
      (have <d> (P x) :by (p/or-elim <c> <a> <b>))))
  (qed <d>))

;; ex is made opaque
(u/set-opacity! #'ex-def true)

(definition single
  "The constraint that \"there exists at most\"..."
  [?T :type, P (==> T :type)]
  (forall [x y T]
    (==> (P x)
         (P y)
         (equal x y))))

(defn decompose-single-type [def-env ctx t]
  (u/decomposer
   (fn [t]
     (if (clojure.core/and (seq t)
                           (= (count t) 3)
                           (= (first t) #'latte-prelude.quant/single-def))
       [(second t) (nth t 2)]
       (throw (ex-info "Cannot infer a \"single\" type" {:type t}))))
   def-env ctx t))

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

(defthm single-elim-rule
  "Elimination rule for [[single]]."
  [?T :type, P (==> T :type), x T, y T]
  (==> (single P)
       (P x)
       (P y)
       (equal x y)))

(proof 'single-elim-rule-thm
  (assume [H1 (single P)
           H2 (P x)
           H3 (P y)]
    (have <a> (equal x y)
          :by (H1 x y H2 H3)))
  (qed <a>))

(defimplicit single-elim
  "Elimination rule for [[single]]. `(single-elim s-proof x y)`
 such that the type of `s-proof` is `(single P)` for some property `P`, then
 we have `(==> (P x) (P y) (equal x y))` thanks to `[[single-elim-rule]]`."
  [def-env ctx [s-proof s-proof-type] [x x-type] [y y-type]]
  (let [[T P] (decompose-single-type def-env ctx s-proof-type)]
    [(list #'single-elim-rule-thm T P x y) s-proof]))

(example [[T :type] [P (==> T :type)] [Hs (single P)] [x T] [y T]]
    (==> (P x)
         (P y)
         (equal x y))
  ;; proof
  (assume [Hx (P x)
           Hy (P y)]
    (have <a> (equal x y) :by ((single-elim Hs x y) Hx Hy)))
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

  `(the u)` defines the unique object
 satisfying a predicate `P` as demonstrated by the proof `u` of type `(unique P)`. This is the implicit version of the axiom [[the-ax]]."
  [def-env ctx [u u-type]]
  (let [[exP _] (p/decompose-and-type def-env ctx u-type)
        [T P] (decompose-ex-type def-env ctx exP)]
    (list #'the-ax T P u)))

(example [[T :type] [P (==> T :type)]]
    (==> (ex P)
         (single P)
         T)
  ;; proof
  (assume [Hex (ex P)
           Hs (single P)]
    (have <a> T :by (the (p/and-intro Hex Hs))))
  (qed <a>))

(defaxiom the-prop-ax
  "The property of the unique element descriptor."
  [T :type, P (==> T :type), u (unique P)]
  (P (the u)))

(defimplicit the-prop
  "`(the-prop u)` proves `(P (the u))` from the proof `u` of `(unique P)`, for some property `P`. This is the main property of the unique descriptor [[the]], cf. [[the-prop-ax]]."
  [def-env ctx [u u-type]]
  (let [[exP _] (p/decompose-and-type def-env ctx u-type)
        [T P] (decompose-ex-type def-env ctx exP)]
    (list #'the-prop-ax T P u)))

(example [[T :type] [P (==> T :type)] [u (unique P)]]
    (P (the u))
  ;; proof
  (qed (the-prop u)))

(defthm the-lemma-prop
  "The unique element is ... unique."
  [?T :type, P (==> T :type), u (unique P)]
  (forall [y T]
          (==> (P y)
               (equal y (the u)))))

(proof 'the-lemma-prop-thm
  (have <a> (single P) :by (p/and-elim-right u))
  (have <b> (P (the u)) :by (the-prop u))
  (assume [y T
           Hy (P y)]
    (have <c> (equal y (the u)) 
          :by ((single-elim <a> y (the u)) Hy <b>)))
  (qed <c>))

(defimplicit the-lemma
  "`(the-lemma u)` proves that `(forall [y T] (==> (P y) (equal y (the u))))`
from the proof `u` that `(unique P)` for some property `P`."
  [def-env ctx [u u-type]]
  (let [[exP _] (p/decompose-and-type def-env ctx u-type)
        [T P] (decompose-ex-type def-env ctx exP)]
    (list #'the-lemma-prop-thm T P u)))

;; register for search facility
(search/register-search-namespace! 'latte-prelude.quant)

