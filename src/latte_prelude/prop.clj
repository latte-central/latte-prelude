(ns latte-prelude.prop
  "Basic definitions and theorems for (intuitionistic) propositional logic.
  Most natural deduction rules are provided as theorems in this namespace."

  (:refer-clojure :exclude [and or not])

  (:require [clojure.core.match :refer [match]]
            [latte-kernel.syntax :as stx]
            [latte-kernel.norm :as norm]
            [latte-kernel.unparser :as unparser]
            [latte.utils :as u :refer [set-opacity! decomposer]]
            [latte.core
             :as latte
             :refer [defthm defimplicit defimplicit*
                     definition example try-example defnotation
                     lambda forall proof assume have qed]]
            [latte.search :as search]))

(defthm impl-refl
  "Implication is reflexive."
  [A :type]
  (==> A A))

(proof 'impl-refl
  (assume [x A]
    (have <a> A :by x))
  (qed <a>))
;; or direct term:  (qed (lambda [x A] x))

(defthm impl-ignore
  "A variant of reflexivity."
  [A :type, B :type]
  (==> A B A))

(proof 'impl-ignore
    (qed (lambda [x A]
                 (lambda [y B] x))))
;; or script:  (assume [x _ y _] (have <a> A :by x)) (qed <a>)

(defthm impl-trans-thm
  "Implication is transitive."
  [A :type, B :type, C :type]
  (==> (==> A B)
       (==> B C)
       (==> A C)))

(proof 'impl-trans-thm  
  (assume [H1 _ ;; (==> A B)
           H2 _ ;; (==> B C)
           x A]
    (have <a> B :by (H1 x))
    (have <b> C :by (H2 <a>)))
  (qed <b>))

(defn decompose-impl-type [def-env ctx t]
  (decomposer (fn [t] (match
                       t
                       (['Π [_ A] B] :seq) [A B]
                       :else 
                       (throw (ex-info "Not an implication type" {:type t}))))
              def-env ctx t))

;; register implication as potential source of implicit type parameters
(u/register-implicit-type-parameters-handler! '==> #'decompose-impl-type nil)

(defn decompose-lambda-term [def-env ctx t]
  (decomposer (fn [t] (match
                       t
                       (['λ [x A] B] :seq) [[x A] B]
                       :else 
                       (throw (ex-info "Not a lambda" {:term t}))))
              def-env ctx t))

(defimplicit impl-trans
  "Implication is transitive.

  `(impl-trans pAB pBC)` yields `(==> A C)`
  from the proof `pAB` that `(==> A B)`
  and the proof `pBC` that `(==> B C)`
  
  cf. [[impl-trans-thm]]
"
  [def-env ctx [impl1 ty1] [impl2 ty2]]
  (let [[A B] (decompose-impl-type def-env ctx ty1)
        [B' C] (decompose-impl-type def-env ctx ty2)]
    (when-not (norm/beta-eq? def-env ctx B B')
      (throw (ex-info "Type in the middle mismatch" {:implicit 'latte.prop/impl-trans
                                                     :left-rhs-type B
                                                     :right-lhs-type B'})))
    [[(list #'latte-prelude.prop/impl-trans-thm A B C) impl1] impl2]))

(alter-meta! #'impl-trans update-in [:arglists] (fn [_] (list '[[?A ?B ?C :type] [pA (==> A B)] [pB (==> B C)]])))

(definition absurd
  "Absurdity."
  []
  (forall [α :type] α))

(defthm ex-falso
  "Ex falso sequitur quodlibet
   (proof by contradiction, elimination for absurdity)."
  [A :type]
  (==> absurd A))

(proof 'ex-falso   
  (assume [f absurd]
    (have <a> A :by (f A)))
  (qed <a>))

(definition not
  "Logical negation."
  [A :type]
  (==> A absurd))

(defthm absurd-intro
  "Introduction rule for absurdity."
  [A :type]
  (==> A (not A)
       absurd))

(proof 'absurd-intro    
  (assume [x A
           y (not A)]
    (have <a> absurd :by (y x)))
  (qed <a>))

(defthm impl-not-not
  "The if half of double negation.

This can be seen as an introduction rule for ¬¬ (not-not) propositions.
Note that double-negation is a law of classical (non-intuitionistic) logic."
  [A :type]
  (==> A (not (not A))))

(proof 'impl-not-not   
  (assume [x A
           H (not A)]
    (have <a> absurd :by (H x)))
  (qed <a>))

(definition truth
  "Logical truth."
  []
  (not absurd))

(defthm truth-is-true
  "The truth is true (really ?)."
  []
  truth)

(proof 'truth-is-true 
  (have <a> truth :by (impl-refl absurd))
  (qed <a>))

(definition and
  "logical conjunction."
  [A :type, B :type]
  (forall [C :type]
    (==> (==> A B C)
         C)))

(defn and-unparser [term]
  (match
   term
   (['Π [C '✳]
     (['==> (['==> A B C1] :seq)
       C2] :seq)] :seq) (if (= C C1 C2)
                          [(list 'and A B) true]
                          [term false])
   (['Π [C '✳]
     (['==> (['==> A (['==> B C1] :seq)] :seq)
       C2] :seq)] :seq) (if (= C C1 C2)
                          [(list 'and A B) true]
                          [term false])
   :else [term false]))

;; (and-unparser '(Π [X ✳] (==> (==> A B X) X)))
;; (and-unparser '(Π [X ✳] (==> (==> A (==> B X)) X)))

(unparser/register-unparser! :and and-unparser)

(defthm and-intro-thm
  "Introduction rule for logical conjunction."
  [A :type, B :type]
  (==> A B
       (and A B)))

(proof 'and-intro-thm  
  (assume [x A
           y B
           C :type
           z (==> A B C)]
    (have <a> (==> B C) :by (z x))
    (have <b> C :by (<a> y)))
  (qed <b>))

(defimplicit and-intro
  "An introduction rule that takes a proof
`a` of type `A`, a proof `b` of type `B` and yields
a proof of type `(and A B)`.

This is an implicit version of [[and-intro-thm]]."
  [def-env ctx [a ty-a] [b ty-b]]
  [[(list #'and-intro-thm ty-a ty-b) a] b])

(alter-meta! #'and-intro update-in [:arglists] (fn [_] (list '[[?A ?B :type] [a A] [b B]])))

(example [[A :type] [B :type] [x A] [y B]]
    (and A B)
  (qed (and-intro x y)))

(defthm and-elim-left-thm
  "Elimination rule for logical conjunction.
   This one only keeps the left-side of the conjunction"
  [A :type, B :type]
  (==> (and A B)
       A))

(proof 'and-elim-left-thm 
  (assume [H1 (and A B)]
    (have <a> (==> (==> A B A) A) :by (H1 A))
    (have <b> (==> A B A) :by (impl-ignore A B))
    (have <c> A :by (<a> <b>)))
  (qed <c>))

(defn decompose-and-type
  ([def-env ctx t] (decompose-and-type def-env ctx t false)) 
  ([def-env ctx t def-only?]
   (decomposer
    (fn [t]
      (cond
        ;; definitional and
        (clojure.core/and (seq? t) 
                          (= (count t) 3)
                          (= (first t) #'latte-prelude.prop/and))
        [(second t) (nth t 2)]
        
        def-only? (throw (ex-info "Not a definitional conjunction type" {:type t}))

        :else
        (match t
               ([Π [C ✳]
                 (['Π [_ (['Π [_ A] (['Π [_ B] C'] :seq)] :seq)] C''] :seq)] :seq)
               (if (= C C' C'')
                 [A B]
                 (throw (ex-info "Not a conjunction type: mismatch variables" {:type t
                                                                               :vars [C C' C'']})))
               :else 
               (throw (ex-info "Not a conjunction type" {:type t})))))
    def-env ctx t)))

;; (decompose-and-type latte-kernel.defenv/empty-env [] '(Π [C ✳] (Π [⇧ (Π [⇧ A] (Π [⇧ B] C))] C)))

(defimplicit and-elim-left
  "An implicit elimination rule that takes a proof
 `p` of type `(and A B)` and yields a proof of `A`.

This is an implicit version of [[and-elim-left-thm]]."
  [def-env ctx [and-term ty]]
  (let [[A B] (decompose-and-type def-env ctx ty)]
    [(list #'and-elim-left-thm A B) and-term]))

(alter-meta! #'and-elim-left update-in [:arglists] (fn [_] (list '[[?A ?B :type] [p (and A B)]])))

(defthm and-elim-right-thm
  "Elimination rule for logical conjunction.
   This one only keeps the right-side of the conjunction"
  [A :type, B :type]
  (==> (and A B)
       B))

(proof 'and-elim-right-thm   
  (assume [H1 (and A B)]
    (have <a> (==> (==> A B B) B) :by (H1 B))
    (have <b> (==> A B B) :by (lambda [x A]
                              (lambda [y B]
                                y)))
    (have <c> B :by (<a> <b>)))
  (qed <c>))

(defimplicit and-elim-right
  "An implicit elimination rule that takes a proof
`p` of type `(and A B)` and yields a proof of `B`.

This is an implicit version of [[and-elim-right-thm]]."
  [def-env ctx [and-term ty]]
  (let [[A B] (decompose-and-type def-env ctx ty)]
    [(list #'and-elim-right-thm A B) and-term]))

(alter-meta! #'and-elim-right update-in [:arglists] (fn [_] (list '[[?A ?B :type] [p (and A B)]])))

(defthm and-sym-thm
  "Symmetry of conjunction."
  [A :type, B :type]
  (==> (and A B)
       (and B A)))

(proof 'and-sym-thm 
  (assume [H (and A B)]
    ;; (have <a> A :by ((and-elim-left A B) H))
    (have <a> A :by (and-elim-left H))
    ;;(have b B :by ((and-elim-right A B) H))
    (have <b> B :by (and-elim-right H))
    (have <c> (==> B A
                 (and B A)) :by (and-intro-thm B A))
    (have <d> (and B A) :by (<c> <b> <a>)))
  (qed <d>))

(defimplicit and-sym
  "Symmetry of conjunction. 
  Proves `(and B A)` from a proof `p` that `(and A B)`.

This is an implicit version of [[and-sym-thm]]."
  [def-env ctx [and-term ty]]
  (let [[A B] (decompose-and-type def-env ctx ty)]
    [(list #'and-sym-thm A B) and-term]))

(alter-meta! #'and-sym update-in [:arglists] (fn [_] (list '[[?A ?B :type] [p (and A B)]])))

(defn mk-nary-op-right-leaning
  "A simple utility for creating \"right-leaning\" n-ary operator calls."
  [op args]
  (if (seq args)
    (if (seq (rest args))
      (cons op (list (first args) (mk-nary-op-right-leaning op (rest args))))
      (first args))
    ()))

;; (mk-nary-op-right-leaning 'and '[p1])
;; => p1

;; (mk-nary-op-right-leaning 'and '[p1 p2])
;; => (and p1 p2)

;; (mk-nary-op-right-leaning 'and '[p1 p2 p3])
;; => (and p1 (and p2 p3))

;; (mk-nary-op-right-leaning 'and '[p1 p2 p3 p4])
;; => (and p1 (and p2 (and p3 p4)))


(defn mk-nary-op-left-leaning
  "A simple utility for creating \"left-leaning\" n-ary operator calls.
  Remark: the `args` are reverted in input."
  [op args]
  (if (seq args)
    (if (seq (rest args))
      (list op (mk-nary-op-left-leaning op (rest args)) (first args))
      (first args))
    '()))

;; (mk-nary-op-left-leaning 'and '[p1])
;; => p1

;; (mk-nary-op-left-leaning 'and '[p2 p1])
;; => (and p1 p2)

;; (mk-nary-op-left-leaning 'and '[p3 p2 p1])
;; => (and (and p1 p2) p3)

;; (mk-nary-op-left-leaning 'and '[p4 p3 p2 p1])
;; => (and (and (and p1 p2) p3) p4)

(defnotation and*
  "A notation defining an n-ary variant of [[and]], which exploits the fact that
conjunction is associative. By default we use the leaf-leaning expansion:
```
(and* p1 p2 ... pN-1 pN) ≡ (and (and ... (and p1 p2) pN-1) pN)))
```
We favor this variant because it is often the case that we use conjunction for
a form of \"subclassing\". Consider some mathematical `<object>` defined as having some properties
`(and p1 p2)` (e.g. a preorder with reflexivity and transitivity). Then we might \"subclass\" 
such an object by considering a supplementary property, i.e. we want `(and <object> p3)` 
(e.g. a preorder with antisymetry hence a partial order). This is exactly `(and (and p1 p2) p3)`,
 and if it is of course isomorphic to the right-leaning version
`(and p1 (and p2 p3))`, only the left variant reflects the \"subclassing\" aspect.  
A right-leaning nary conjunction is provided by [[r-and*]]. 
"
  [& ps]
  (if (seq ps)
    [:ok (mk-nary-op-left-leaning #'and (reverse ps))]
    [:ko {:msg "and* nary operator needs at least 1 argument"
          :args ps}]))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         A)
  (qed (lambda [H (and* A B C)]
         (and-elim-left (and-elim-left H)))))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         B)
    (qed (lambda [H (and* A B C)]
         (and-elim-right (and-elim-left H)))))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         C)
  (qed (lambda [H (and* A B C)]
         (and-elim-right H))))

(defnotation r-and*
  "A notation defining an n-ary variant of [[and]], which exploits the fact that
conjunction is associative. This version is the right-leaning variant of [[and*]],
which means the following:
```
(and* p1 p2 ... pN-1 pN) ≡ (and p1 (and p2 (and ... (and pN-1 pN))))
```"
  [& ps]
  (if (seq ps)
    [:ok (mk-nary-op-right-leaning #'and ps)]
    [:ko {:msg "r-and* nary operator needs at least 1 argument"
          :args ps}]))

(example [[A :type] [B :type] [C :type]]
    (==> (r-and* A B C)
         A)
  (qed (lambda [H (r-and* A B C)]
         (and-elim-left H))))

(example [[A :type] [B :type] [C :type]]
    (==> (r-and* A B C)
         B)
    (qed (lambda [H (r-and* A B C)]
         (and-elim-left (and-elim-right H)))))

(example [[A :type] [B :type] [C :type]]
    (==> (r-and* A B C)
         C)
  (qed (lambda [H (r-and* A B C)]
         (and-elim-right (and-elim-right H)))))

(defn build-and-intros-left-leaning [args]
  (if (seq args)
    (if (seq (rest args))
      (list #'and-intro (build-and-intros-left-leaning (rest args)) (ffirst args))
      (ffirst args))
    (throw (ex-info "Empty and* intro list (please report)" {:args (reverse args)}))))

;; (build-and-intros-left-leaning '[[a1 A1]])
;; => a1

;; (build-and-intros-left-leaning '[[a1 A1] [a2 A2]])
;; => (#'latte-prelude.prop/and-intro a1 a2)

;; (build-and-intros-left-leaning '[[a3 A3] [a2 A2] [a1 A1]])
;; => (#'latte-prelude.prop/and-intro (#'latte-prelude.prop/and-intro a1 a2) a3)

;; (build-and-intros-left-leaning '[[a4 A4] [a3 A3] [a2 A2] [a1 A1]])
;; => (#'latte-prelude.prop/and-intro (#'latte-prelude.prop/and-intro (#'latte-prelude.prop/and-intro a1 a2) a3) a4)

(defimplicit* and-intro*
  "A nary variant of [[and-intro]], the introduction rule for conjunction.
It builds a proof of `(and* A1 A2 ... AN)` from proofs of the `Ai`'s"
  [def-env ctx & args]
  (build-and-intros-left-leaning (reverse args)))

(example [[A :type] [B :type] [C :type]]
    (==> A B C
         (and* A B C))
  (assume [a _ b _ c _]
    (have <a> _ :by (and-intro* a b c)))
  (qed <a>))

(defn build-and-intros-right-leaning [args]
  (if (seq args)
    (if (seq (rest args))
      (list #'and-intro (ffirst args) (build-and-intros-right-leaning (rest args)))
      (ffirst args))
    (throw (ex-info "Empty r-and* intro list (please report)" {:args args}))))

;; (build-and-intros-right-leaning '[[a1 A1]])
;; => a1

;; (build-and-intros-right-leaning '[[a1 A1] [a2 A2]])
;; => (#'latte-prelude.prop/and-intro a1 a2)

;; (build-and-intros-right-leaning '[[a1 A1] [a2 A2] [a3 A3]])
;; => (#'latte-prelude.prop/and-intro a1 (#'latte-prelude.prop/and-intro a2 a3))

(defimplicit* r-and-intro*
  "A nary \"right-leaning\" variant of [[and-intro]], the introduction rule for conjunction.
It builds a proof of `(r-and* A1 A2 ... AN)` from proofs of the `Ai`'s

Remark: the default \"left-leaning\" varient is [[and-intro*]]."
  [def-env ctx & args]
  (build-and-intros-right-leaning args))

(example [[A :type] [B :type] [C :type]]
    (==> A B C
         (r-and* A B C))
  (assume [a _ b _ c _]
    (have <a> _ :by (r-and-intro* a b c)))
  (qed <a>))


(defn and*-arity [def-env ctx and-type]
  (let [res (try (decompose-and-type def-env ctx and-type true)
                 (catch Exception e nil))]
    (if (nil? res)
      1
      (let [[L _] res]
        (inc (and*-arity def-env ctx L))))))

(defn elim-path [l r n arity]
  (let [nb-left (- arity n)
        lefts (repeat nb-left l)]
    (if (> n 1)
      (conj lefts r)
      lefts)))

;; (elim-path :left :right 1 2)
;; => (:left)
;; (elim-path :left :right 2 2)
;; => (:right)

;; (elim-path :left :right 1 3)
;; => (:left :left)
;; (elim-path :left :right 2 3)
;; => (:right :left)
;; (elim-path :left :right 3 3)
;; => (:right)

;; (elim-path :left :right 1 4)
;; => (:left :left :left)
;; (elim-path :left :right 2 4)
;; => (:right :left :left)
;; (elim-path :left :right 3 4)
;; => (:right :left)
;; (elim-path :left :right 4 4)
;; => (:right)

(defn build-and-elim [def-env ctx n and-term and-type]
  (let [arity (and*-arity def-env ctx and-type)]
    (when-not (<= 1 n arity)
      (throw (ex-info "Wrong n-ary conjunction elimination index: must be between 1 and and-type-arity)"
                      {:and-term and-term
                       :index n
                       :and-type and-type
                       :and-type-arity arity})))
    (let [path (elim-path #'and-elim-left #'and-elim-right n arity)]
      (loop [path (reverse path), term and-term]
        (if (seq path)
          (recur (rest path) (list (first path) term))
          term)))))

(defimplicit and-elim*
  "This is a generic elimination rule for n-ary
 conjunction (e.g. as introduced by the [[and*]] notation).
In `(and-elim* n and-term)`  the index `n` corresponds to
the `n`-th operand of the term.

For example (informally ):

 - `(and-elim* 1 (and* a b c)≡(and (and a b) c)) ==> a` 
 - `(and-elim* 2 (and* a b c)) ==> b`
 - `(and-elim* 3 (and* a b c)) ==> c`

Internally, the correct nesting of [[and-elim-left]] and
[[and-elim-right]] is constructed. Errors are raised
if the index is incorrect or if the specificied term
is not a conjunction."
  [def-env ctx n [and-term and-type]]
  (let [elim-term (build-and-elim def-env ctx n and-term and-type)]
    ;; (println "elim-term =" elim-term)
    elim-term))


(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         A)
  (qed (lambda [H (and* A B C)]
         (and-elim* 1 H))))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         A)
  (assume [H (and* A B C)]
    (have <a> A :by (and-elim* 1 H)))
  (qed <a>))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         B)
  (qed (lambda [H (and* A B C)]
         (and-elim* 2 H))))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         C)
  (qed (lambda [H (and* A B C)]
         (and-elim* 3 H))))

(try-example [[A :type] [B :type] [C :type]]
     (==> (and* A B C)
          C)
   (qed (lambda [H (and* A B C)]
          (and-elim* 4 H))))
;; => [:failed "Proof failed: Qed step failed: cannot infer term type."
;;             {:cause {:msg "Cannot calculate codomain type of abstraction.",
;;              :term (λ [H (#'latte-prelude.prop/and (#'latte-prelude.prop/and A B) C)] (#'latte-prelude.prop/and-elim* 4 H)),
;;              :from {:implicit and-elim*, :msg "Wrong n-ary conjunction elimination index: must be between 1 and and-type-arity)",
;;                     :and-term H, :index 4, :and-type (#'latte-prelude.prop/and (#'latte-prelude.prop/and A B) C), :and-type-arity 3}},
;;              :meta {:line 552, :column 4}}]

(defn build-r-and-elim [def-env ctx n and-term and-type]
  (loop [k n, and-term and-term, and-type and-type]
    (let [[L R] (try (decompose-and-type def-env ctx and-type)
                     (catch Exception e
                       (if (zero? k)
                         [nil nil]
                         (throw (ex-info "Wrong n-ary conjunction elimination (right-leaning): not a conjunction"
                                         {:and-term and-term
                                          :index (- n k)
                                          :arg-type and-type
                                          :cause e})))))]
      (cond
        (nil? L) and-term
        (zero? k) [(list #'and-elim-left-thm L R) and-term]
        :else (recur (dec k) [(list #'and-elim-right-thm L R) and-term] R)))))

(defimplicit r-and-elim*
  "This is a generic elimination rule for (right-leaning) n-ary
 conjunction (e.g. as introduced by the [[r-and*]] notation).
In `(r-and-elim* n r-and-term)`  the index `n` corresponds to
the `n`-th operand of the term.

This is the right-leaning version of the default [[and-elim*]]."
  [def-env ctx n [and-term and-type]]
  (if (clojure.core/not (clojure.core/and (integer? n)
                                          (>= n 1)))
    (throw (ex-info "Wrong (righ-leaning) elimination index `n`, must be a strictly positive integer." {:index n}))
    (let [elim-term (build-r-and-elim def-env ctx (dec n) and-term and-type)]
      ;; (println "elim-term =" elim-term)
      elim-term)))


(example [[A :type] [B :type] [C :type]]
    (==> (r-and* A B C)
         A)
  (qed (lambda [H (r-and* A B C)]
         (r-and-elim* 1 H))))

(example [[A :type] [B :type] [C :type]]
    (==> (r-and* A B C)
         B)
  (qed (lambda [H (r-and* A B C)]
         (r-and-elim* 2 H))))

(example [[A :type] [B :type] [C :type]]
    (==> (r-and* A B C)
         C)
  (qed (lambda [H (r-and* A B C)]
         (r-and-elim* 3 H))))

;; (try-example [[A :type] [B :type] [C :type]]
;;      (==> (and* A B C)
;;           C)
;;    (qed (lambda [H (and* A B C)]
;;           (and-elim* 4 H))))
;; => [:failed "Proof failed: Qed step failed: cannot infer term type." {:cause {:msg "Cannot calculate codomain type of abstraction.", :term (λ [H (#'latte-prelude.prop/and A (#'latte-prelude.prop/and B C))] (#'latte-prelude.prop/and-elim* 3 H)), :from {:implicit and-elim*, :msg "Wrong n-ary conjunction elimination: not a conjunction", :and-term [(#'latte-prelude.prop/and-elim-right-thm B C) [(#'latte-prelude.prop/and-elim-right-thm A (#'latte-prelude.prop/and B C)) H]], :index 2, :arg-type C, :cause #error {
;;  :cause "Not a conjunction type"
;;  :data {:type C}
;;  :via
;;  [{:type clojure.lang.ExceptionInfo
;;    :message "Not a conjunction type"
;;    :data {:type C}
;;    :at ...}]}]

(definition or
  "logical disjunction."
  [A :type, B :type]
  (forall [C :type]
    (==> (==> A C)
         (==> B C)
         C)))

(defn or-unparser [term]
  (match
   term
   (['Π [C ✳]
     (['==>
       (['==> A C1] :seq)
       (['==> B C2] :seq)
       C3] :seq)] :seq) (if (= C1 C2 C3)
                          [(list 'or A B) true]
                          [term false])
   :else [term false]))

(unparser/register-unparser! :or or-unparser)

(defthm or-intro-left-thm
  "Introduction rule for logical disjunction.
This is the introduction by the left operand."
  [A :type, B :type]
  (==> A
       (or A B)))

(proof 'or-intro-left-thm  
  (assume [x A
           C :type
           H1 (==> A C)
           H2 (==> B C)]
    (have <a> C :by (H1 x)))
  (qed <a>))

(defimplicit or-intro-left
  "`(or-intro-left proofA B)` is left introduction for a disjunction `(or A B)`, 
with `proofA` a proof of `A`.
 
This is an implicit version of [[or-intro-left-thm]]."
  [def-env ctx [proofA A] [B kindB]]
  [(list #'or-intro-left-thm A B) proofA])

(defthm or-intro-right-thm
  "Introduction rule for logical disjunction.
This is the introduction by the right operand."
  [A :type, B :type]
  (==> B
       (or A B)))

(proof 'or-intro-right-thm  
  (assume [y B
           C :type
           H1 (==> A C)
           H2 (==> B C)]
    (have <a> C :by (H2 y)))
  (qed <a>))

(defimplicit or-intro-right
  "`(or-intro-left A proofB)` is right introduction for a disjunction `(or A B)`, 
with `proofB` a proof of `B`.

 This is an implicit version of [[or-intro-left-thm]]."
  [def-env ctx [A kindA] [proofB B]]
  [(list #'or-intro-right-thm A B) proofB])

(defthm or-elim-thm
  "Elimination rule for logical disjunction.
This corresponds to a important scheme of reasoning by cases. 
To prove a proposition `C` under the assumption  `(or A B)`:
 - first case: assume `A` and prove `C` 
 - second case: assume `B` and prove `C`
"
  [A :type, B :type]
  (==> (or A B)
       (forall [C :type]
         (==> (==> A C)
              (==> B C)
              C))))

(proof 'or-elim-thm  
  (assume [H1 (forall [D :type] (==> (==> A D)
                                     (==> B D)
                                     D))
           C :type
           H2 (==> A C)
           H3 (==> B C)]
    (have <a> (==> (==> A C) (==> B C) C) :by (H1 C))
    (have <b> (==> (==> B C) C) :by (<a> H2))
    (have <c> C :by (<b> H3)))
  (qed <c>))

;; (or A B)
;; = (forall [C :type]
;;       (forall [_ (forall [_ A] C)]
;;          (forall [_ (forall [_ B] C)]
;;               C)))

(defn decompose-or-type [def-env ctx t]
  (decomposer
   (fn [t]
     (if (clojure.core/and (seq? t) 
                           (= (count t) 3)
                           (= (first t) #'latte-prelude.prop/or))
       [(second t) (nth t 2)]
       (match t
              (['Π [C ✳] (['Π [_ (['Π [_ A] C1] :seq)] (['Π [_ (['Π [_ B] C2] :seq)] C3] :seq)] :seq)] :seq)
              (if (= C C1 C2 C3)
                [A B]
                (throw (ex-info "Not a disjunction type: mismatch variables" {:type t
                                                                              :vars [C C1 C2 C3]})))
              :else
              (throw (ex-info "Not a disjunction type" {:type t})))))
   def-env ctx t))
    
;; (decompose-or-type latte-kernel.defenv/empty-env [] '(Π [C ✳] (Π [⇧ (Π [⇧ A] C)] (Π [⇧ (Π [⇧ B] C)] C))))

(defimplicit or-elim
  "`(or-elim or-term left-proof right-proof)` is a
n elimination rule that takes a proof  `or-term` of type `(or A B)`,
a proof `left-proof` of type `(==> A prop)`, 
a proof `right-proof` of type `(==> B prop)`, and thus
concludes that `prop` holds by `[[or-elim-thm]]`.

This is (for now) the easiest rule to use for proof-by-cases."
  [def-env ctx [or-term or-type] [left-proof left-type] [right-proof right-type]]
  (let [[A B] (decompose-or-type def-env ctx or-type)
        [_ prop] (decompose-impl-type def-env ctx left-type)]
    [[[[(list #'or-elim-thm A B) or-term] prop] left-proof] right-proof]))

(defnotation or*
  "A notation defining an n-ary variant of [[or]], which exploits the fact that
disjunction is associative. By convention we have:
```
(or* p1 p2 ... pN-1 pN) ≡ (or p1 (or p2 (or ... (or pN-1 pN))))
```

Remark: unlike for conjunction, there is no real motivation to
use a left-leaning variant by default, so the simpler right-leaning
encoding is prefered.
"
  [& ps]
  (if (seq ps)
    [:ok (mk-nary-op-right-leaning #'or ps)]
    [:ko {:msg "and* nary operator needs at least 1 argument"
          :args ps}]))

(declare build-or-intro)

(defimplicit* or-intro*
  "A generic introduction rule for [[or*]].
Suppose we have a proof `p` of a proposition `Ai`, and suppose
also the sequence of types `A1`,...,`Ai`,...,`An`.

Then `(or-intro* A1 ... p ... An)` is a proof of `(or* A1 ... Ai ... An)`."
  [def-env ctx & args]
  (if (seq args)
    (build-or-intro args)
    (throw (ex-info "or-intro* nary rule needs at least 1 argument"
                    {:args args}))))

;; (or-intro* <x>) ≡ <x>
;; (or-intro* <x> A) ≡ (or-intro-left <x> A)
;; (or-intro* A <x>) ≡ (or-intro-right A <x>)
;; (or-intro* <x> A B) ≡ (or-intro-left <x> (or A B))
;; (or-intro* A <x> B) ≡ (or-intro-right A (or-intro-left <x> B))
;; (or-intro* A B <x>) ≡ (or-intro-right A (or-intro-right B <x>))

(defn build-or-intro [args]
  (if (seq (rest args))
    (let [[arg targ] (first args)]
      (if (stx/sort? targ)
        (list #'or-intro-right arg (build-or-intro (rest args)))
        (list #'or-intro-left arg (mk-nary-op-right-leaning #'or (map first (rest args))))))
    ;; only one argument
    (ffirst args)))

(build-or-intro '[[a A]])
;; => a

(build-or-intro '[[a A] [B ✳]])
;; => (#'latte-prelude.prop/or-intro-left a B)

(build-or-intro '[[A ✳] [b B]])
;; => (#'latte-prelude.prop/or-intro-right A b)

;; (build-or-intro '[[a A] [B ✳] [C ✳]])
;; => (#'latte-prelude.prop/or-intro-left a (#'latte-prelude.prop/or* B C))

;; (build-or-intro '[[A ✳] [b B] [C ✳]])
;; => (#'latte-prelude.prop/or-intro-right A (#'latte-prelude.prop/or-intro-left b (#'latte-prelude.prop/or* C)))

;; (build-or-intro '[[A ✳] [B ✳] [c C]])
;; => (#'latte-prelude.prop/or-intro-right A (#'latte-prelude.prop/or-intro-right B c))

(example [[A :type] [B :type] [C :type]]
    (==> A (or* A B C))
  (assume [a A]
    (have <a> _ :by (or-intro* a B C)))
  (qed <a>))

(example [[A :type] [B :type] [C :type]]
    (==> B (or* A B C))
  (assume [b B]
    (have <a> _ :by (or-intro* A b C)))
  (qed <a>))

(example [[A :type] [B :type] [C :type]]
    (==> C (or* A B C))
  (assume [c C]
    (have <a> _ :by (or-intro* A B c)))
  (qed <a>))

;; or-elim* with n branches is a little bit trickier (and useful)

(defn build-or-elim* [def-env ctx index or-term or-type case-proofs]
  (case (count case-proofs)
    (0 1) (throw (ex-info "Cannot build nary or-elim*: missing case proof(s)."
                          {:case-term or-term
                           :case-type or-type
                           :case-proofs case-proofs}))
    2 (list #'or-elim or-term (first case-proofs) (second case-proofs))
    ;; more than 2
    (try (let [[L R] (decompose-or-type def-env ctx or-type)]
           (let [Hcase (gensym (str "Hcase" index))]
             (list #'or-elim or-term (first case-proofs)
                   (list 'λ [Hcase R]
                         (build-or-elim* def-env ctx (inc index) Hcase R (rest case-proofs))))))
         (catch Exception _
           (throw (ex-info "Cannot build nary or-elim*: case term/type is not a disjunction"
                           {:case-term or-term
                            :case-type or-type
                            :case-proofs case-proofs}))))))

;; Hor :: (or A1 (or A2 ... (or An-1 An)))
;; (or-elim* Hor proof1 proof2 ... proofN-1 proofN)
;; ≡ (or-elim Hor
;;            proof1
;;            (lambda [Hc1 (or A2 ... (or An-1 An))]
;;               (or-elim Hc1
;;                        proof2
;;                        ...
;;                          proofN-2
;;                          (lambda [HcN (or An-1 An)]
;;                            (or-elim HcN proofN-1 proofN)))))


(defimplicit* or-elim*
  "Elimination rule for n-ary disjunction `(or* T1 T2 ... TN)`.

```clojure
(or-elim* or-term case1 case2 ... caseN)
```
is the same thing as the repeated and nested uses of `[[or-elim]]` for binary disjunction.
"
  [def-env ctx & args]
  (when (empty? args)
    (throw (ex-info "Cannot build nary or-elim*: missing arguments" {:args args})))
  (let [[[or-term or-type] & cases] args]
    (when (empty? cases)
      (throw (ex-info "Cannot build nary or-elim*: missing arguments"
                      {:or-term or-term
                       :or-type or-type
                       :args cases})))
    (let [elim-term (build-or-elim* def-env ctx 1 or-term or-type (map first cases))]
      ;; (println "elim-term =" elim-term)
      elim-term)))

;; here's a three branches example :

(example [[A :type] [B :type] [C :type] [D :type]]
    (==>
     ;; the disjunctive hypothesis
     (or A (or B C))
     ;; case 1
     (==> A D)
     ;; case 2
     (==> B D)
     ;; case 3
     (==> C D)
     ;; conclusion
     D)
  ;; proof
  (assume [Hor _
           proof1 (==> A D)
           proof2 (==> B D)
           proof3 (==> C D)]
    (have <elim> D :by (or-elim Hor
                                proof1
                                (lambda [Hc1 (or B C)]
                                  (or-elim Hc1 proof2 proof3)))))
  (qed <elim>))

(example [[A :type] [B :type] [C :type] [D :type]]
    (==>
     ;; the disjunctive hypothesis
     (or* A B C)
     ;; case 1
     (==> A D)
     ;; case 2
     (==> B D)
     ;; case 3
     (==> C D)
     ;; conclusion
     D)
  ;; proof
  (assume [Hor _
           proof1 (==> A D)
           proof2 (==> B D)
           proof3 (==> C D)]
    (have <elim> D :by (or-elim* Hor proof1 proof2 proof3)))
  (qed <elim>))

;; four branches ?

(example [[A :type] [B :type] [C :type] [D :type] [E :type]]
    (==>
     ;; the disjunctive hypothesis
     (or A (or B (or C D)))
     ;; case 1
     (==> A E)
     ;; case 2
     (==> B E)
     ;; case 3
     (==> C E)
     ;; case 4
     (==> D E)
     ;; conclusion
     E)
  ;; proof
  (assume [Hor _
           proof1 (==> A E)
           proof2 (==> B E)
           proof3 (==> C E)
           proof4 (==> D E)]
    (have <elim> E :by (or-elim Hor
                                proof1
                                (lambda [Hc1 (or B (or C D))]
                                  (or-elim Hc1
                                           proof2
                                           (lambda [Hc2 (or C D)]
                                             (or-elim Hc2 proof3 proof4)))))))
  (qed <elim>))

(example [[A :type] [B :type] [C :type] [D :type] [E :type]]
    (==>
     ;; the disjunctive hypothesis
     (or A (or B (or C D)))
     ;; case 1
     (==> A E)
     ;; case 2
     (==> B E)
     ;; case 3
     (==> C E)
     ;; case 4
     (==> D E)
     ;; conclusion
     E)
  ;; proof
  (assume [Hor _
           proof1 (==> A E)
           proof2 (==> B E)
           proof3 (==> C E)
           proof4 (==> D E)]
    (have <elim> E :by (or-elim* Hor proof1 proof2 proof3 proof4)))
  (qed <elim>))

(defthm or-not-elim-left
  "An elimination rule for disjunction, simpler than [[or-elim]].
This eliminates to the left operand."
  [A :type, B :type]
  (==> (or A B) (not B)
       A))

(proof 'or-not-elim-left  
  (assume [H1 (or A B)
           H2 (not B)]
    (have <a> (==> (==> A A) (==> B A) A) :by (H1 A))
    (have <b> (==> A A) :by (impl-refl A))
    (assume [x B]
      (have <c> absurd :by (H2 x))
      (have <d> A :by (<c> A)))
    (have <e> A :by (<a> <b> <d>)))
  (qed <e>))

(defthm or-not-elim-right
  "An elimination rule for disjunction, simpler than [[or-elim]].
This eliminates to the right operand."
  [A :type, B :type]
  (==> (or A B) (not A)
       B))

(proof 'or-not-elim-right    
  (assume [H1 _ H2 _]
    (have <a> (==> (==> A B) (==> B B) B) :by (H1 B))
    (have <b> (==> B B) :by (impl-refl B))
    (assume [x A]
      (have <c> absurd :by (H2 x))
      (have <d> B :by (<c> B)))
    (have <e> B :by (<a> <d> <b>)))
  (qed <e>))

(defthm or-sym-thm
  "Symmetry of disjunction."
  [A :type, B :type]
  (==> (or A B)
       (or B A)))

(proof 'or-sym-thm 
  (assume [H1 (or A B)
           D :type
           H2 (==> B D)
           H3 (==> A D)]
    (have <a> _ :by (H1 D))
    (have <b> D :by (<a> H3 H2)))
  (qed <b>))

(defimplicit or-sym
  "Symmetry of disjunction, an implicit version of [[or-sym-thm]]."
  [def-env ctx [or-term or-type]]
  (let [[A B] (decompose-or-type def-env ctx or-type)]
    [(list #'or-sym-thm A B) or-term]))

(defthm or-not-impl-elim
  "An alternative elimination rule for disjunction."
  [A :type, B :type]
  (==> (or A B)
       (==> (not A) B)))

(proof 'or-not-impl-elim 
  (assume [H (or A B)
           Hn (not A)]
    (assume [x A]
            (have <a> absurd :by (Hn x))
            "Thanks to absurdity we can get anything we want."
            (have <b> B :by (<a> B)))
    (have <c> (==> B B) :by (impl-refl B))
    (have <d> (==> (==> A B)
                   (==> B B)
                   B) :by (H B))
    (have <e> B :by (<d> <b> <c>)))
  (qed <e>))

(defthm or-assoc-thm
  [A :type, B :type, C :type]
  (==> (or (or A B) C)
       (or A (or B C))))

(proof 'or-assoc-thm  
  (assume [H1 (or (or A B)
                  C)]
    (assume [H2 (or A B)]
      (assume [H3 A]
        (have <a> (or A (or B C))
              :by (or-intro-left H3 (or B C))))
      (assume [H4 B]
        (have <b1> (or B C)
              :by (or-intro-left H4 C))
        (have <b> (or A (or B C))
              :by (or-intro-right A <b1>)))
      (have <c> ;; _
        (or A (or B C))
            :by (or-elim H2 <a> <b>)))
    (assume [H5 C]
      (have <d1> (or B C)
            :by (or-intro-right B H5))
      (have <d> (or A (or B C))
            :by (or-intro-right A <d1>)))
    (have <e> _ :by (or-elim H1 <c> <d>)))
  (qed <e>))


(defthm or-assoc-conv-thm
  [A :type, B :type, C :type]
  (==> (or A (or B C))
       (or (or A B) C)))

(proof 'or-assoc-conv-thm    
  (assume [H1 (or A (or B C))]
    (assume [H2 A]
      (have <a1> (or A B)
            :by (or-intro-left H2 B))
      (have <a> (or (or A B) C)
            :by (or-intro-left <a1> C)))
    (assume [H3 (or B C)]
      (assume [H4 B]
        (have <b1> (or A B)
              :by (or-intro-right A H4))
        (have <b> (or (or A B) C)
              :by (or-intro-left <b1> C)))
      (assume [H5 C]
        (have <c> (or (or A B) C)
              :by (or-intro-right (or A B) H5)))
      (have <d> _
            :by (or-elim H3 <b> <c>)))
    (have <e> _
          :by (or-elim H1 <a> <d>)))
  (qed <e>))

(defimplicit or-assoc
  "Associativity of disjunction, an implicit that subsumes both
[[or-assoc-thm]] and [[or-assoc-conv-thm]]."
  [def-env ctx [or-term or-type]]
  (let [[A B] (decompose-or-type def-env ctx or-type)]
    (try (let [[A1 A2] (decompose-or-type def-env ctx A)]
           [(list #'or-assoc-thm A1 A2 B) or-term])
         (catch Exception e
           (let [[B1 B2] (decompose-or-type def-env ctx B)]
             [(list #'or-assoc-conv-thm A B1 B2) or-term])))))

(definition <=>
  "Logical equivalence or 'if and only if'."
  [A :type, B :type]
  (and (==> A B)
       (==> B A)))

(defthm iff-refl
  "Reflexivity of logical equivalence."
  [A :type]
  (<=> A A))

(proof 'iff-refl   
  (have <a> (==> A A) :by (impl-refl A))
  (have <b> (==> (==> A A)
                 (==> A A)
                 (<=> A A))
        :by (and-intro-thm (==> A A) (==> A A)))
  (have <c> (<=> A A) :by (<b> <a> <a>))
  (qed <c>))

(defthm iff-intro-thm
  "Introduction rule for logical equivalence."
  [A :type, B :type]
  (==> (==> A B)
       (==> B A)
       (<=> A B)))

(proof 'iff-intro-thm   
  (assume [H1 (==> A B)
           H2 (==> B A)]
    (have <a> (==> (==> A B)
                 (==> B A)
                 (<=> A B)) :by (and-intro-thm (==> A B) (==> B A)))
    (have <b> (<=> A B) :by (<a> H1 H2)))
  (qed <b>))

(defimplicit iff-intro
  "Introduction rule for logical equivalence, an implicit version of [[iff-intro-thm]]."
  [def-env ctx [ab ab-type] [ba ba-type]]
  (let [[A B] (decompose-impl-type def-env ctx ab-type)
        [B A'] (decompose-impl-type def-env ctx ba-type)]
    ;; XXX: check somethings on A' vs. A ?
    [[(list #'iff-intro-thm A B) ab] ba]))

(defthm iff-elim-if-thm
  "Elimination rule for logical equivalence.
   This one only keeps the if part of the equivalence."
  [A :type, B :type]
  (==> (<=> A B)
       (==> A B)))

(proof 'iff-elim-if-thm   
  (assume [H (<=> A B)]
    (have <a> (==> (<=> A B)
                 (==> A B))
          :by (and-elim-left-thm (==> A B) (==> B A)))
    (have <b> (==> A B) :by (<a> H)))
  (qed <b>))

(defn decompose-iff-type
  [def-env ctx t]
  (if (clojure.core/and (seq? t) 
                           (= (count t) 3)
                           (= (first t) #'latte-prelude.prop/<=>))
    [(second t) (nth t 2)]
    ;; or something that works if things are made transparent
    (let [[L R] (decompose-and-type def-env ctx t)
          [A B] (decompose-impl-type def-env ctx L)]
      [A B])))

(defimplicit iff-elim-if
  "Left (if) elimination for `<=>`, an implicit version of [[iff-elim-if-thm]]."
  [def-env ctx [iff-term iff-type]]
  (let [[A B] (decompose-iff-type def-env ctx iff-type)]
    [(list #'iff-elim-if-thm A B) iff-term]))

(defthm iff-elim-only-if-thm
  "Elimination rule for logical equivalence.
   This one only keeps the only-if part of the equivalence."
  [A :type, B :type]
  (==> (<=> A B)
       (==> B A)))

(proof 'iff-elim-only-if-thm   
  (assume [H (<=> A B)]
    (have <a> (==> (<=> A B)
                 (==> B A))
          :by (and-elim-right-thm (==> A B) (==> B A)))
    (have <b> (==> B A) :by (<a> H)))
  (qed <b>))

(defimplicit iff-elim-only-if
  "Right (only if) elimination for `<=>`, an implicit version of [[iff-elim-only-if-thm]]."
  [def-env ctx [iff-term iff-type]]
  (let [[A B] (decompose-iff-type def-env ctx iff-type)]
    [(list #'iff-elim-only-if-thm A B) iff-term]))

(defthm iff-sym-thm
  "Symmetry of logical equivalence."
  [A :type, B :type]
  (==> (<=> A B)
       (<=> B A)))

(proof 'iff-sym-thm    
  (assume [H (<=> A B)]
    (have <a> (==> B A) :by (iff-elim-only-if H))
    (have <b> (==> A B) :by (iff-elim-if H))
    (have <c> (==> (==> B A)
                   (==> A B)
                   (<=> B A)) :by (iff-intro-thm B A))
    (have <d> (<=> B A) :by (<c> <a> <b>)))
    (qed <d>))

(defimplicit iff-sym
  "Symmetry of `<=>`, an implicit version of [[iff-sym-thm]]."
  [def-env ctx [iff-term iff-type]]
  (let [[A B] (decompose-iff-type def-env ctx iff-type)]
    [(list #'iff-sym-thm A B) iff-term]))

(defthm iff-trans-thm
  "Transitivity of logical equivalence."
  [[A B C :type]]
  (==> (<=> A B)
       (<=> B C)
       (<=> A C)))

(proof 'iff-trans-thm
  (assume [H1 (<=> A B)
           H2 (<=> B C)]
    (have <a> (==> A B) :by (iff-elim-if H1))
    (have <b> (==> B C) :by (iff-elim-if H2))
    (have <c> _ :by (impl-trans-thm A B C))
    (have <d> (==> A C) :by (<c> <a> <b>))
    (have <e> (==> C B) :by (iff-elim-only-if H2))
    (have <f> (==> B A) :by (iff-elim-only-if H1))
    (have <g> _ :by (impl-trans-thm C B A))
    (have <h> (==> C A) :by (<g> <e> <f>))
    (have <i> _ :by (iff-intro-thm A C))
    (have <k> (<=> A C) :by (<i> <d> <h>)))
  (qed <k>))

(defimplicit iff-trans
  "Transitivity of `<=>`, an implicit version of [[iff-trans-thm]]."
  [def-env ctx [iff-term1 iff-type1] [iff-term2 iff-type2]]
  (let [[A B] (decompose-iff-type def-env ctx iff-type1)
        [C D] (decompose-iff-type def-env ctx iff-type2)]
    ;; XXX: check that B and C are equal ?
    [[(list #'iff-trans-thm A B D) iff-term1] iff-term2]))


;; opaque definitions by default

(set-opacity! #'or true)
(set-opacity! #'and true)
;;(set-opacity! #'<=> true)

;; register for search facility
(search/register-search-namespace! 'latte-prelude.prop)
