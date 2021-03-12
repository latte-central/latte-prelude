(ns latte-prelude.fun
  "A **function** with domain `T` and codomain `U` 
  has type `(==> T U)`.

   This namespace provides some important properties about such
  functions.

  The main source of properties is the consideration of types
as objects and functions  as arrows in the so-called *LaTTe category*."

  (:refer-clojure :exclude [and or not identity])

  (:require [latte.core :as latte :refer [definition defaxiom defthm defnotation
                                          proof assume have pose qed
                                          forall lambda]]
            [latte-prelude.prop :as p :refer [and or not]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]))

(definition identity
  "The identity function."
  [T :type]
  (lambda [x T] x))

(definition domain
  "The domain of function `f`"
  [[?T ?U :type], f (==> T U)]
  T)

(definition codomain
  "The codomain of function `f`"
  [[?T ?U :type], f (==> T U)]
  U)

(definition compose
  "The composition of two functions `f` and `g`, or
`f` \"after\" `g`."
  [[?T ?U ?V :type], f (==> U V), g (==> T U)]
  (lambda [x T] (f (g x))))

;;; (<< f g h i) == (compose f (compose g h i))
;;;              == (compose f (compose g (compose h i)))

;;; (>> f g h i) == (<< i h g f)

(defnotation <<
  "A notation for iterated compositions of functions.

   Example :

   ```
   (<< f g h i) == (compose f (compose g h i))
                == (compose f (compose g (compose h i)))
   ```
   "
  [& fs]
  (if (seq fs)
    [:ok (p/mk-nary-op-right-leaning #'compose fs)]
    [:ko {:msg "`<<` nary operator needs at least 1 argument"
          :args fs}]))

;; (latte/term [T1 :type] [T2 :type] [T3 :type] [T4 :type] [T5 :type]
;;        [f (==> T4 T5)] [g (==> T3 T4)] [h (==> T2 T3)] [i (==> T1 T2)]
;;        (<< f g h i))
;; => (compose f (compose g (compose h i)))

;; (latte/term [T :type] [U :type] [f (==> T U)] (<< f))
;; => f

(defnotation >>
  "A notation for sequential composition of functions.

  Example :

  ```
  (>> f g h i)  == (<< i h g f)
  ```"
  [& fs]
  (if (seq fs)
    [:ok (cons #'<< (reverse fs))]
    [:ko {:msg "`>>` nary operator needs at least 1 argument"
          :args fs}]))

;; (latte/term [T1 :type] [T2 :type] [T3 :type] [T4 :type] [T5 :type]
;;        [i (==> T4 T5)] [h (==> T3 T4)] [g (==> T2 T3)] [f (==> T1 T2)]
;;        (>> f g h i))
;; => (compose i (compose h (compose g f)))

;; (latte/term [T :type] [U :type] [f (==> T U)] (>> f))
;; => f

(defthm fun-equal-ext
  "Functional equality is extensional."
  [[?T ?U :type], f (==> T U), g (==> T U)]
  (==> (equal f g)
       (forall [x T] (equal (f x) (g x)))))

(proof 'fun-equal-ext-thm
  (assume [Heq (equal f g)]
    (assume [x T]
      (have <a> (equal x x) :by (eq/eq-refl x))
      (have <b> (equal (f x) (f x)) :by (eq/eq-cong f <a>))
      (have <c> (equal (f x) (g x))
            :by (eq/eq-subst (lambda [$ (==> T U)]
                               (equal (f x) ($ x))) Heq <b>))))
  (qed <c>))

(defaxiom functional-extensionality
  [[?T ?U :type], f (==> T U), g (==> T U)]
  (==> (forall [x T] (equal (f x) (g x)))
       (equal f g)))

(defthm law-identity-left
  "The categorical left identity law for functions."
  [[T U :type]]
  (forall [g (==> T U)]
    (equal (<< g (identity T)) g)))

(proof 'law-identity-left
  (assume [g (==> T U)]
    (assume [x T]
      (have <a> (equal ((<< g (identity T)) x) (g x))
            :by (eq/eq-refl (g x))))
    (have <b> (equal (<< g (identity T)) g)
          :by ((functional-extensionality (<< g (identity T)) g) <a>)))
  (qed <b>))

(defthm law-identity-right
  "The categorical right identity law for functions."
  [[T U :type]]
  (forall [f (==> T U)]
    (equal (<< (identity U) f) f)))

(proof 'law-identity-right
  (assume [f (==> T U)]
    (assume [x T]
      (have <a> (equal ((<< (identity U) f) x) (f x))
            :by (eq/eq-refl (f x))))
    (have <b> (equal (<< (identity U) f) f)
          :by ((functional-extensionality (<< (identity U) f) f) <a>)))
  (qed <b>))

(defthm law-associativity
  "The categorical associativity law for functions."
  [[T U V W :type]]
  (forall [f (==> T U)]
    (forall [g (==> U V)]
      (forall [h (==> V W)]
        (equal (compose h (compose g f))
               (compose (compose h g) f))))))

(proof 'law-associativity
  (assume [f _ g _ h _]
    (assume [x T]
      (have <a> (equal ((compose h (compose g f)) x)
                       ((compose (compose h g) f) x))
            :by (eq/eq-refl ((compose h (compose g f)) x))))
    (have <b> _ :by ((functional-extensionality (compose h (compose g f))
                                                (compose (compose h g) f)) <a>)))
  (qed <b>))


(defaxiom Unit
  "The singleton type."
  []
  :type)

(defaxiom unit
  "The unique habitant of `Unit`."
  []
  Unit)

(definition point
  "The notion of a point in the LaTTe category."
  [T :type]
  (==> Unit T))

;; TODO (?) : functional extensionality for points

(definition retraction
  "The function `r` is a retraction of `f`."
  [[?T ?U :type] [f (==> T U)] [r (==> U T)]]
  (equal (<< r f) (identity T)))

(definition section
  "The function `s` is a section of `f`."
  [[?T ?U :type] [f (==> T U)] [s (==> U T)]]
  (equal (<< f s) (identity U)))

(defthm solve-section
  [[?T ?U :type], f (==> T U), s (==> U T)]
  (==> (section f s)
       (forall [V :type]
         (forall [y (==> V U)]
           (exists [x (==> V T)]
             (equal (<< f x) y))))))

(proof 'solve-section-thm
  (assume [Hs _]
    (assume [V :type
             y (==> V U)]
      (pose x := (<< s y))
      (have <a> (equal (<< f s) (identity U)) :by Hs)
      (have <b> (equal (<< f s y) (<< (identity U) y))
            :by (eq/eq-cong (lambda [$ (==> U U)]
                              (compose $ y)) <a>))
      (have <c> (equal (<< f x) (<< f s y)) :by (eq/eq-refl (<< f x)))
      (have <d> (equal (<< f x) (<< (identity U) y))
            :by (eq/eq-trans <c> <b>))
      (have <e> (equal (<< (identity U) y) y)
            :by ((law-identity-right V U) y))
      (have <f> (equal (<< f x) y)
            :by (eq/eq-trans <d> <e>))
      (have <g> _ :by ((q/ex-intro (lambda [x (==> V T)]
                                    (equal (<< f x) y)) x) <f>))))
  (qed <g>))

(definition injective
  "An injective function."
  [[?T ?U :type], f (==> T U)]
  (forall [x y T]
    (==> (equal (f x) (f y))
         (equal x y))))

(definition surjective
  "A surjective function."
  [[?T ?U :type], f (==> T U)]
  (forall [y U] (exists [x T] (equal (f x) y))))

(definition bijective
  "A bijective function."
  [[?T ?U :type], f (==> T U)]
  (and (injective f)
       (surjective f)))

(defthm bijective-is-surjective
  "A bijection is a surjection."
  [[?T ?U :type], f (==> T U)]
  (==> (bijective f)
       (surjective f)))

(proof 'bijective-is-surjective-thm
  (assume [H (bijective f)]
    (have <a> (surjective f) :by (p/and-elim-right H)))
  (qed <a>))

(defthm bijective-is-injective
  "A bijection is an injection."
  [[?T ?U :type], f (==> T U)]
  (==> (bijective f)
       (injective f)))

(proof 'bijective-is-injective-thm
  (assume [H (bijective f)]
    (have <a> (injective f) :by (p/and-elim-left H)))
  (qed <a>))

(defthm compose-injective
  "The composition of two injective functions is injective."
  [[?T ?U ?V :type], f (==> U V), g (==> T U)]
  (==> (injective f)
       (injective g)
       (injective (compose f g))))

(proof 'compose-injective-thm  
  (assume [Hf (injective f)
           Hg (injective g)]
    (assume [x T
             y T
             Hinj (equal ((compose f g) x)
                         ((compose f g) y))]
      (have <a> (equal (f (g x)) (f (g y))) :by Hinj)
      (have <b> (equal (g x) (g y))
            :by (Hf (g x) (g y) <a>))
      (have <c> (equal x y)
            :by (Hg x y <b>))))
  (qed <c>))

(defthm injective-single
  "An injective function has at most one antecedent for each image."
  [[?T ?U :type], f (==> T U)]
  (==> (injective f)
       (forall [y U] (q/single (lambda [x T] (equal (f x) y))))))

(proof 'injective-single-thm   
  (assume [Hf (injective f)]
    (assume [y U]
      (assume [x1 T
               x2 T
               Hx1 (equal (f x1) y)
               Hx2 (equal (f x2) y)]
        (have <a1> (equal y (f x2)) :by (eq/eq-sym Hx2))
        (have  <a> (equal (f x1) (f x2))
               :by (eq/eq-trans Hx1 <a1>))
        (have <b> (equal x1 x2) :by (Hf x1 x2 <a>)))))
  (qed <b>))

(defthm bijective-unique
  "A bijective function has exactly one antecedent for each image."
  [[?T ?U :type], f (==> T U)]
  (==> (bijective f)
       (forall [y U] (q/unique (lambda [x T] (equal (f x) y))))))

(proof 'bijective-unique-thm  
  (assume [Hf (bijective f)]
    (have <a> (injective f)
          :by ((bijective-is-injective f) Hf))
    (have <b> (surjective f)
          :by ((bijective-is-surjective f) Hf))
    (assume [y U]
      (have <c> (q/ex (lambda [x T] (equal (f x) y)))
            :by (<b> y))
      (have <d> (q/single (lambda [x T] (equal (f x) y)))
            :by ((injective-single f) <a> y))
      (have <e> (q/unique (lambda [x T] (equal (f x) y)))
            :by (p/and-intro <c> <d>))))
  (qed <e>))

(definition inverse
  "The inverse of bijective function `f`."
  [[?T ?U :type], f (==> T U), b (bijective f)]
  (lambda [y U]
    (q/the ((bijective-unique f) b y))))

(defthm inverse-prop
  "The basic property of the inverse of a bijective function `f`."
  [[?T ?U :type], f (==> T U), b (bijective f)]
  (forall [y U] (equal (f ((inverse f b) y)) y)))

(proof 'inverse-prop-thm  
  (assume [y U]
    (have <a> (equal (f ((inverse f b) y)) y)
          :by (q/the-prop (((bijective-unique f) b) y))))
  (qed <a>))

(defthm inverse-prop-conv
  "The basic property of the inverse function,
 the converse of [[inverse-prop]]."
  [[?T ?U :type], f (==> T U), b (bijective f)]
  (forall [x T] (equal ((inverse f b) (f x)) x)))

(proof 'inverse-prop-conv-thm  
  (assume [x T]
    (have <a> (equal (f ((inverse f b) (f x))) (f x))
          :by ((inverse-prop f b) (f x)))
    (have <b> (equal ((inverse f b) (f x)) x)
          :by (((bijective-is-injective f) b)
               ((inverse f b) (f x)) x
               <a>)))
  (qed <b>))

(defthm inverse-surjective
  "The inverse function of a bijection, is surjective."
  [[?T ?U :type], f (==> T U), b (bijective f)]
  (surjective (inverse f b)))

(proof 'inverse-surjective-thm 
  (have <a> (injective f) :by ((bijective-is-injective f) b))
  (pose inv-f := (inverse f b))
  (assume [x T]
    (pose y := (f x))
    (have <b> (equal (f (inv-f y)) (f x))
          :by ((inverse-prop f b) (f x)))
    (have <c> (equal (inv-f y) x) :by (<a> (inv-f y) x <b>))
    (have <d> (exists [z U] (equal (inv-f z) x))
          :by ;; ((q/ex-intro (lambda [z U] (equal (inv-f z) x)) y)
              ;;  <c>)
          ((q/ex-intro-rule (λ [y U] (equal ((inv-f) y) x)) y) <c>)
          ;;(q/ex-intro y <c>)
          ))
  (qed <d>))

(defthm inverse-injective
  "The inverse function of a bijection, is injective."
  [[?T ?U :type], f (==> T U), b (bijective f)]
  (injective (inverse f b)))

(proof 'inverse-injective-thm 
  (pose inv-f := (inverse f b))
  (assume [x U
           y U
           Hxy (equal (inv-f x) (inv-f y))]
    (have <a> (equal (f (inv-f x)) (f (inv-f y)))
          :by (eq/eq-cong f Hxy))
    (have <b> (equal (f (inv-f x)) x)
          :by ((inverse-prop f b) x))
    (have <c> (equal x (f (inv-f x)))
          :by (eq/eq-sym <b>))
    (have <d> (equal (f (inv-f y)) y)
          :by ((inverse-prop f b) y))
    (have <e> (equal x (f (inv-f y)))
          :by (eq/eq-trans <c> <a>))
    (have <f> (equal x y)
          :by (eq/eq-trans <e> <d>)))
  (qed <f>))

(defthm inverse-bijective
  "The inverse of a bijection is a bijection."
  [[?T ?U :type], f (==> T U), b (bijective f)]
  (bijective (inverse f b)))

(proof 'inverse-bijective-thm
  (have <a> _ :by (p/and-intro (inverse-injective f b)
                               (inverse-surjective f b)))
  (qed <a>))

