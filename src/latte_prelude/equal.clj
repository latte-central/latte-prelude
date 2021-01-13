(ns latte-prelude.equal
  "The formal definition of equality, and its basic properties."

  (:refer-clojure :exclude [and or not])

  (:require
   [latte.utils :refer [decomposer set-opacity!]]
   [latte.core :as latte :refer [definition defthm defimplicit defimplicit*
                                          assume have qed proof]]

   [latte-prelude.utils :as pu]
   [latte-prelude.prop :as p :refer [<=> and or not]])
)

(definition equality
  "The intuitionistic, second-order definition of equality.
This corresponds to Leibniz's *indiscernibility of identicals*."
  [T :type, x T, y T]
  (forall [P (==> T :type)]
          (<=> (P x) (P y))))

(defimplicit equal
  "Equality of `x` and `y` (which must be of the same type `T`).
This is an implicit version of [[equality]]."
  [def-env ctx [x x-ty] [y y-ty]]
  (list #'equality x-ty x y))

(defn decompose-equal-type [def-env ctx t]
  (decomposer
   (fn [t]
     (if (clojure.core/and (seq t)
                           (= (count t) 4)
                           (= (first t) #'latte-prelude.equal/equality))
       [(second t) (nth t 2) (nth t 3)]
       ;; XXX: cannot decompose further because
       ;; we cannot retrieve the x and y of the
       ;; definition ... add dummy witnesses ?
       (throw (ex-info "Cannot infer an equal-type" {:type t}))))
   def-env ctx t))

(defthm eq-intro-thm
  "Introduction rule for [[equal]]. This is useful because
equality is opaque by default."
  [T :type, x T, y T]
  (==> (forall [P (==> T :type)]
               (<=> (P x) (P y)))
       (equal x y)))

(proof 'eq-intro-thm
  (assume [H (forall [P (==> T :type)]
                     (<=> (P x) (P y)))]
    (have <a> (equal x y) :by H))
  (qed <a>))

(defimplicit eq-intro
  "Introduction rule for [[equal]].
The type parameter `T` is implicit, cf. [[eq-intro-thm]] for the explicit version."
  [def-env cfx [x x-ty] [y y-ty]]
  (list #'eq-intro-thm x-ty x y))

(alter-meta! #'eq-intro update-in [:arglists] (fn [_] (list '[[x ?T] [y ?T]])))

(defthm eq-refl-thm
  "The reflexivity property of equality."
  [T :type, x T]
  (equal x x))

(proof 'eq-refl-thm 
  (assume [P (==> T :type)]
    (have <a> (<=> (P x) (P x)) :by (p/iff-refl (P x))))
  (qed <a>))

(defimplicit eq-refl
  "Equality is reflexive, cf. [[eq-refl-thm]]."
  [def-env ctx [x x-ty]]
  (list #'eq-refl-thm x-ty x))

(alter-meta! #'eq-refl update-in [:arglists] (fn [_] (list '[[x ?T]])))

(defthm eq-sym-thm
  "The symmetry property of equality."
  [T :type, x T, y T]
  (==> (equal x y)
       (equal y x)))

(proof 'eq-sym-thm 
  (assume [Heq (equal x y)
           P (==> T :type)]
    (have <a> (<=> (P x) (P y)) :by (Heq P))
    (have <b> (<=> (P y) (P x)) :by (p/iff-sym <a>)))
  (qed <b>))

(defimplicit eq-sym
  "
Proves `(equal y x)` from `eq-proof` by symmetry of equality, cf. [[eq-sym-thm]]."
  [def-env ctx [eq-term eq-ty]]
  (let [[T x y] (decompose-equal-type def-env ctx eq-ty)]
    [(list #'eq-sym-thm T x y) eq-term]))

(alter-meta! #'eq-sym update-in [:arglists] (fn [_] (list '[[eq-proof (equal x y)]])))

(defthm eq-trans-thm
  "The transitivity property of equality."
  [T :type, [x y z T]]
  (==> (equal x y)
       (equal y z)
       (equal x z)))

(proof 'eq-trans-thm 
  (assume [H1 (equal x y)
           H2 (equal y z)
           P (==> T :type)]
    (have <a> (<=> (P x) (P y)) :by (H1 P))
    (have <b> (<=> (P y) (P z)) :by (H2 P))
    (have <c> (<=> (P x) (P z))
          :by (p/iff-trans <a> <b>)))
  (qed <c>))

(defimplicit eq-trans
  "
Proves `(equal x z)` from `eq1` and `eq2` by transitivity of `equal`, cf. [[eq-trans-thm]]."
  [def-env ctx [eq-term1 ty1] [eq-term2 ty2]]
  (let [[T1 x1 y1] (decompose-equal-type def-env ctx ty1)
        [T2 x2 y2] (decompose-equal-type def-env ctx ty2)]
    [[(list #'eq-trans-thm T1 x1 y1 y2) eq-term1] eq-term2]))

(alter-meta! #'eq-trans update-in [:arglists] (fn [_] (list '[[eq1 (equal x y)] [eq2 (equal y z)]])))

(defimplicit* eq-trans*
  "

Transitivity of `equal`, a n-ary version of [[eq-trans]].

For example:

```
(eq-trans* eq1 eq2)
==> (eq-trans eq1 eq2)

(eq-trans* eq1 eq2 eq3)
==> (eq-trans (eq-trans eq1 eq2) eq3)

(eq-trans* eq1 eq2 eq3 eq4)
==> (eq-trans (eq-trans (eq-trans eq1 eq2) eq3) eq4)
````
etc.
`"
  [def-env ctx & eq-terms]
  ;; (println "[eq-trans*] eq-terms=" eq-terms)
  ;; (when-not (and (seq eq-terms) (>= (count eq-terms) 2))
  ;;   (println "  ==> here 1")
  ;;   (throw (ex-info "There must be at least two arguments."
  ;;                   {:special 'latte-prelude.equal/eq-trans*
  ;;                    :arg eq-terms})))
  (let [[T x1 y1] (decompose-equal-type def-env ctx (second (first eq-terms)))]
    (loop [eq-terms' (rest eq-terms), x1 x1, y1 y1, ret (ffirst eq-terms)]
      (if (seq eq-terms')
        (let [[_ x2 y2] (decompose-equal-type def-env ctx (second (first eq-terms')))]
          (recur (rest eq-terms') x1 y2
                 [[(list #'eq-trans-thm T x1 y1 y2) ret] (ffirst eq-terms')]))
        ;; we're done
        (do
          ;; (println "  ==> ret=" ret)
          ret)))))

(alter-meta! #'eq-trans* update-in [:arglists] (fn [_] (list '[[eq1 (equal x1 x2)] [eq2 (equal x2 x3)] ... [eqN (equal xN_1 xN)]])))

;; (defthm test-eq-trans
;;   [[T :type] [a T] [b T] [c T] [d T]]
;;   (==> (equal T a b)
;;        (equal T b c)
;;        (equal T c d)
;;        (equal T a d)))

;; (proof test-eq-trans
;;     
;;   (assume [H1 (equal T a b)
;;            H2 (equal T b c)
;;            H3 (equal T c d)]
;;      (have <a> (equal T a d)
;;            :by (eq-trans* H1 H2 H3))
;;     ;; (have <a> (equal T a c)
;;     ;;       :by (((eq-trans T a b c) H1) H2))
;;     ;; (have <b> (equal T a d)
;;     ;;       :by (((eq-trans T a c d) <a>) H3))
;;     (qed <a>)))

(defthm eq-subst-prop
  "Substitutivity property of equality. This is the main elimination rule."
  [?T :type, P (==> T :type), x T, y T]
  (==> (equal x y)
       (P x)
       (P y)))

(proof 'eq-subst-prop-thm 
  (assume [H1 (equal x y)
           H2 (P x)]
    (have <a> (<=> (P x) (P y)) :by (H1 P))
    (have <b> (P y) :by ((p/iff-elim-if <a>) H2)))
  (qed <b>))

(defimplicit eq-subst
  "
Proves `(P y)` given the fact that `(equal x y)` and `(P x)`

This is thanks to substitutivity of `equal`, cf. [[eq-subst-prop]]."
  [def-env ctx [P P-type] [eq-term eq-type] [Px Px-type]]
  (let [[T x y] (decompose-equal-type def-env ctx eq-type)]
    [[(list #'eq-subst-prop-thm T P x y) eq-term] Px]))

(alter-meta! #'eq-subst update-in [:arglists] (fn [_] (list '[[P (==> T :type)] [eq (equal x y)] [Px (P x)]])))

(defimplicit subst
  "Proves `(P y)` from proofs of `(P x)` and `(equal x y)`.
The difference with [[eq-subst]] is that we try to
infer the property `P`."
  [def-env ctx [Px Px-type] [eq-xy eq-xy-type]]
  (let [[T x y] (decompose-equal-type def-env ctx eq-xy-type)]
    ;; (println "find: " x)
    ;; (println "  in: " Px-type)
    (if-let [path (pu/find-term x Px-type)]
      (do ;; (println "path = " path)
          (let [P (pu/build-subst-lambda Px-type T path true)]
            [[(list #'eq-subst-prop-thm T P x y) eq-xy] Px]))
      (throw (ex-info "Cannot infer substitution." {:term Px-type
                                                    :subterm x})))))

(defthm eq-cong-prop
  "Congruence property of equality."
  [?T :type, ?U :type, f (==> T U), x T, y T]
  (==> (equal x y)
       (equal (f x) (f y))))

(proof 'eq-cong-prop-thm
  (assume [H1 (equal x y)
           Q (==> U :type)]
    (assume [H2 (Q (f x))]
      (have <a1> _ :by (eq-subst-prop (lambda [z T] (Q (f z))) x y))
      (have <a> (Q (f y)) :by (<a1> H1 H2)))
    (have <b> (equal y x) :by (eq-sym H1))
    (assume [H3 (Q (f y))]
      (have <c1> _ :by (eq-subst-prop (lambda [z T] (Q (f z))) y x))
      (have <c> (Q (f x)) :by (<c1> <b> H3)))
    (have <d> (<=> (Q (f x)) (Q (f y))) :by (p/iff-intro <a> <c>)))
  (qed <d>))

(defimplicit eq-cong
  "
Proves `(equal (f x) (f y))` by congruence of `equal`, cf. [[eq-cong-prop]]."
  [def-env ctx [f f-ty] [eq-term eq-ty]]
  (let [[T x y] (decompose-equal-type def-env ctx eq-ty)
        [T' U] (p/decompose-impl-type def-env ctx f-ty)]
    [(list #'eq-cong-prop-thm T U f x y) eq-term]))

(alter-meta! #'eq-cong update-in [:arglists] (fn [_] (list '[[f (==> T U)] [eq (equal x y)]])))

;; now that we have intros and elims, we make equality opaque.
(set-opacity! #'equality true)


