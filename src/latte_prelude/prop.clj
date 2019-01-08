(ns latte-prelude.prop
  "Basic definitions and theorems for (intuitionistic) propositional logic.
  Most natural deduction rules are provided as theorems in this namespace."

  (:refer-clojure :exclude [and or not])

  (:require [clojure.core.match :refer [match]]
            [latte-kernel.norm :as norm]
            [latte-kernel.unparser :as unparser]
            [latte.utils :refer [set-opacity! decomposer]]
            [latte.core
             :as latte
             :refer [defthm defimplicit definition example try-example defnotation
                     lambda forall proof assume have qed]
             ]))

(defthm impl-refl
  "Implication is reflexive."
  [[A :type]]
  (==> A A))

(proof 'impl-refl
  (assume [x A]
    (have <a> A :by x))
  (qed <a>))
;; or direct term:  (qed (lambda [x A] x))

(defthm impl-ignore
  "A variant of reflexivity."
  [[A :type] [B :type]]
  (==> A B A))

(proof 'impl-ignore
    (qed (lambda [x A]
                 (lambda [y B] x))))
;; or script:  (assume [x _ y _] (have <a> A :by x)) (qed <a>)

(defthm impl-trans-thm
  "Implication is transitive."
  [[A :type] [B :type] [C :type]]
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

(defimplicit impl-trans
  [def-env ctx [impl1 ty1] [impl2 ty2]]
  (let [[A B] (decompose-impl-type def-env ctx ty1)
        [B' C] (decompose-impl-type def-env ctx ty2)]
    (when-not (norm/beta-eq? def-env ctx B B')
      (throw (ex-info "Type in the middle mismatch" {:implicit 'latte.prop/impl-trans
                                                     :left-rhs-type B
                                                     :right-lhs-type B'})))
    [[(list #'latte-prelude.prop/impl-trans-thm A B C) impl1] impl2]))

(definition absurd
  "Absurdity."
  []
  (forall [α :type] α))

(defthm ex-falso
  "Ex falso sequitur quodlibet
   (proof by contradiction, elimination for absurdity)."
  [[A :type]]
  (==> absurd A))

(proof 'ex-falso   
  (assume [f absurd]
    (have <a> A :by (f A)))
  (qed <a>))

(definition not
  "Logical negation."
  [[A :type]]
  (==> A absurd))

(defthm absurd-intro
  "Introduction rule for absurdity."
  [[A :type]]
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
  [[A :type]]
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type]]
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


(example [[A :type] [B :type] [x A] [y B]]
    (and A B)
  (qed (and-intro x y)))

(defthm and-elim-left-thm
  "Elimination rule for logical conjunction.
   This one only keeps the left-side of the conjunction"
  [[A :type] [B :type]]
  (==> (and A B)
       A))

(proof 'and-elim-left-thm 
  (assume [H1 (and A B)]
    (have <a> (==> (==> A B A) A) :by (H1 A))
    (have <b> (==> A B A) :by (impl-ignore A B))
    (have <c> A :by (<a> <b>)))
  (qed <c>))

(defn decompose-and-type [def-env ctx t]
  (decomposer
   (fn [t]
     (if (clojure.core/and (seq? t) 
                           (= (count t) 3)
                           (= (first t) #'latte-prelude.prop/and))
       [(second t) (nth t 2)]
       (match t
              ([Π [C ✳]
                (['Π [_ (['Π [_ A] (['Π [_ B] C'] :seq)] :seq)] C''] :seq)] :seq)
              (if (= C C' C'')
                [A B]
                (throw (ex-info "Not a conjunction type: mismatch variables" {:type t
                                                                              :vars [C C' C'']})))
              :else 
              (throw (ex-info "Not a conjunction type" {:type t})))))
   def-env ctx t))

;; (decompose-and-type latte-kernel.defenv/empty-env [] '(Π [C ✳] (Π [⇧ (Π [⇧ A] (Π [⇧ B] C))] C)))

(defimplicit and-elim-left
  "An implicit elimination rule that takes a proof
of type `(and A B)` and yields a proof of `A`.

This is an implicit version of [[and-elim-left-thm]]."
  [def-env ctx [and-term ty]]
  (let [[A B] (decompose-and-type def-env ctx ty)]
    [(list #'and-elim-left-thm A B) and-term]))

(defthm and-elim-right-thm
  "Elimination rule for logical conjunction.
   This one only keeps the right-side of the conjunction"
  [[A :type] [B :type]]
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
`and-term` of type `(and A B)` and yields a proof of `B`.

This is an implicit version of [[and-elim-right-thm]]."
  [def-env ctx [and-term ty]]
  (let [[A B] (decompose-and-type def-env ctx ty)]
    [(list #'and-elim-right-thm A B) and-term]))

(defthm and-sym-thm
  "Symmetry of conjunction."
  [[A :type] [B :type]]
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
  "Symmetry of conjunction, an implicit version of [[and-sym-]]."
  [def-env ctx [and-term ty]]
  (let [[A B] (decompose-and-type def-env ctx ty)]
    [(list #'and-sym-thm A B) and-term]))

(defn mk-nary-op
  "A simple utility for creating \"right-leaning\" n-ary operator calls."
  [op args]
  (if (seq args)
    (if (seq (rest args))
      (cons op (list (first args) (mk-nary-op op (rest args))))
      (first args))
    ()))

;; (mk-nary-op 'and '[p1])
;; => p1

;; (mk-nary-op 'and '[p1 p2])
;; => (and p1 p2)

;; (mk-nary-op 'and '[p1 p2 p3])
;; => (and p1 (and p2 p3))

;; (mk-nary-op 'and '[p1 p2 p3 p4])
;; => (and p1 (and p2 (and p3 p4)))

(defnotation and*
  "A notation defining an n-ary variant of conjunction, which exploits the fact that
conjunction is associative. By convention we have:
```
(and* p1 p2 ... pN-1 pN) ≡ (and p1 (and p2 (and ... (and pN-1 pN))))
```"
  [& ps]
  (if (seq ps)
    [:ok (mk-nary-op #'and ps)]
    [:ko {:msg "and* nary operator needs at least 1 argument"
          :args ps}]))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         A)
  (qed (lambda [H (and* A B C)]
         (and-elim-left H))))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         B)
    (qed (lambda [H (and* A B C)]
         (and-elim-left (and-elim-right H)))))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         C)
  (qed (lambda [H (and* A B C)]
         (and-elim-right (and-elim-right H)))))

(defn build-and-elim [def-env ctx n and-term and-type]
  (loop [k n, and-term and-term, and-type and-type]
    ;; (println "and-term=" and-term)
    (let [[L R] (try (decompose-and-type def-env ctx and-type)
                     (catch Exception e
                       (if (zero? k)
                         [nil nil]
                         (throw (ex-info "Wrong n-ary conjunction elimination: not a conjunction"
                                         {:and-term and-term
                                          :index (- n k)
                                          :arg-type and-type
                                          :cause e})))))]
      (cond
        (nil? L) and-term
        (zero? k) [(list #'and-elim-left-thm L R) and-term]
        :else (recur (dec k) [(list #'and-elim-right-thm L R) and-term] R)))))

(defimplicit and-elim*
  "This is a generic elimination rule for (right-leaning) n-ary
 conjunction (e.g. as introduced by the [[and*]] notation).
In `(and-elim* n and-term)`  the index `n` corresponds to
the (0-based) `n`-th operand of the term.

For example (informally ):

 - `(and-elim* 0 (and* a b c)≡(and a (and b c))) ==> a` 
 - `(and-elim* 1 (and* a b c)) ==> b`
 - `(and-elim* 2 (and* a b c)) ==> c`

Internally, the correct nesting of [[and-elim-left]] and
[[and-elim-right]] is constructed. Errors are raised
if the index is incorrect or if the specificied term
is not a conjunction."
  [def-env ctx n [and-term and-type]]
  (if (clojure.core/not (clojure.core/and (integer? n)
                                          (>= n 0)))
    (throw (ex-info "Wrong elimination index `n`, must be a positive integer." {:n n}))
    (let [elim-term (build-and-elim def-env ctx n and-term and-type)]
      ;; (println "elim-term =" elim-term)
      elim-term)))


(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         A)
  (qed (lambda [H (and* A B C)]
         (and-elim* 0 H))))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         B)
  (qed (lambda [H (and* A B C)]
         (and-elim* 1 H))))

(example [[A :type] [B :type] [C :type]]
    (==> (and* A B C)
         C)
  (qed (lambda [H (and* A B C)]
         (and-elim* 2 H))))

;; (try-example [[A :type] [B :type] [C :type]]
;;      (==> (and* A B C)
;;           C)
;;    (qed (lambda [H (and* A B C)]
;;           (and-elim* 3 H))))
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type]]
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
  "Left introduction for disjunction, an implicit version of [[or-intro-left-thm]]."
  [def-env ctx [left-term left-type] [right-type right-kind]]
  [(list #'or-intro-left-thm left-type right-type) left-term])

(defthm or-intro-right-thm
  "Introduction rule for logical disjunction.
This is the introduction by the right operand."
  [[A :type] [B :type]]
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
  "Right introduction for disjunction, an implicit version of [[or-intro-right-thm]]."
  [def-env ctx [left-type left-kind] [right-term right-type]]
  [(list #'or-intro-right-thm left-type right-type) right-term])

(defthm or-elim-thm
  "Elimination rule for logical disjunction.

Remark: this rule,
reflecting the definition of [[or]], provides a
 constructive way to eliminate disjunctions. 
A simpler elimination process is offered if one
 of the two disjuncts does not hold: 
cf. [[or-not-elim-left]] and [[or-not-elim-right]]."
  [[A :type] [B :type]]
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
  "An elimination rule that takes a proof
 `or-term` of type `(or A B)`, a proposition `prop`,
a proof `left-proof` of type `(==> A prop)`, 
a proof `right-proof` of type `(==> B prop)`, and thus
concludes that `prop` holds by `[[or-elim-thm]]`.

This is (for now) the easiest rule to use for proof-by-cases."
  [def-env ctx [or-term or-type] [prop prop-type] [left-proof left-type] [right-proof right-type]]
  (let [[A B] (decompose-or-type def-env ctx or-type)]
    [[[[(list #'or-elim-thm A B) or-term] prop] left-proof] right-proof]))

(defthm or-not-elim-left
  "An elimination rule for disjunction, simpler than [[or-elim]].
This eliminates to the left operand."
  [[A :type] [B :type]]
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type] [C :type]]
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
            :by (or-elim H2 (or A (or B C))
                         <a> <b>)))
    (assume [H5 C]
      (have <d1> (or B C)
            :by (or-intro-right B H5))
      (have <d> (or A (or B C))
            :by (or-intro-right A <d1>)))
    (have <e> _ :by (or-elim H1 (or A (or B C))
                             <c> <d>)))
  (qed <e>))


(defthm or-assoc-conv-thm
  [[A :type] [B :type] [C :type]]
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
            :by (or-elim H3 (or (or A B) C)
                         <b> <c>)))
    (have <e> _
          :by (or-elim H1 (or (or A B) C)
                       <a> <d>)))
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
  [[A :type] [B :type]]
  (and (==> A B)
       (==> B A)))

(defthm iff-refl
  "Reflexivity of logical equivalence."
  [[A :type]]
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type]]
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
  [[A :type] [B :type] [C :type]]
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
