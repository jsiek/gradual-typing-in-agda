open import Types
open import Labels
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)

{-

  This modules defines reduction for the Parameterized Cast Calculus
  and provides a proof of progress. Preservation is guaranteed in the
  way the reduction relation is defined and checked by Agda.

-}


module ParamCastReduction
  (Cast : Type → Set)
  (Inert : ∀{A} → Cast A → Set)
  (Active : ∀{A} → Cast A → Set)  
  (ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c)
  where

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  {-

  Before defining reduction, we first need to define Value.  In cast
  calculi, whether a cast forms a value or not depends on the shape of
  the cast. But here we have parameterized over casts.  So we must add
  more parameters to tell us whether a cast is a value-forming cast or
  not. So we add the parameter Inert to identify the later, and the
  parameter Active to identify casts that need to be reduced. Further,
  we require that all casts (at least, all the well-typed ones) can be
  categorized one of these two ways, which is given by the
  ActiveOrInert parameter.

  The following is the definition of Value. The case for casts, M ⟨ c ⟩,
  requires M to be a value and c to be an inert cast.

  -}
  data Value : ∀ {Γ A} → Γ ⊢ A → Set where

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        -----------
      → Value (ƛ N)

    V-const : ∀ {Γ} {A : Type} {k : rep A} {f : Prim A}
        ------------------------
      → Value {Γ} {A} (($ k){f})

    V-pair : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        -----------------
      → Value (cons V W)

    V-inl : ∀ {Γ A B} {V : Γ ⊢ A}
      → Value V
        --------------------------
      → Value {Γ} {A `⊎ B} (inl V)

    V-inr : ∀ {Γ A B} {V : Γ ⊢ B}
      → Value V
        --------------------------
      → Value {Γ} {A `⊎ B} (inr V)

    V-cast : ∀ {Γ : Context} {A B : Type} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        {i : Inert c}
      → Value V
        ---------------
      → Value (V ⟨ c ⟩)


  {-

  A value of type ⋆ must be of the form M ⟨ c ⟩ where c is inert cast.

  -}
  canonical⋆ : ∀ {Γ} → (M : Γ ⊢ ⋆) → (Value M)
             → Σ[ A ∈ Type ] Σ[ M' ∈ (Γ ⊢ A) ] Σ[ c ∈ (Cast (A ⇒ ⋆)) ]
               Inert c × (M ≡ (M' ⟨ c ⟩))
  canonical⋆ .($ _) (V-const {k = ()})  
  canonical⋆ .(_ ⟨ _ ⟩) (V-cast{Γ}{A}{B}{V}{c}{i} v) =
      ⟨ A , ⟨ V , ⟨ c , ⟨ i , refl ⟩ ⟩ ⟩ ⟩

  {-

   We shall use a kind of shallow evaluation context, called a Frame,
   to collapse all of the ξ rules into a single rule.

  -}

  data Frame : {Γ : Context} → Type → Type → Set where

    F-·₁ : ∀ {Γ A B}
      → Γ ⊢ A
      → Frame {Γ} (A ⇒ B) B

    F-·₂ : ∀ {Γ A B}
      → (M : Γ ⊢ A ⇒ B) → ∀{v : Value {Γ} M}
      → Frame {Γ} A B

    F-if : ∀ {Γ A}
      → Γ ⊢ A
      → Γ ⊢ A    
      → Frame {Γ} (` 𝔹) A

    F-×₁ : ∀ {Γ A B}
      → Γ ⊢ A
      → Frame {Γ} B (A `× B)

    F-×₂ : ∀ {Γ A B}
      → Γ ⊢ B
      → Frame {Γ} A (A `× B)

    F-fst : ∀ {Γ A B}
      → Frame {Γ} (A `× B) A

    F-snd : ∀ {Γ A B}
      → Frame {Γ} (A `× B) B

    F-inl : ∀ {Γ A B}
      → Frame {Γ} A (A `⊎ B)

    F-inr : ∀ {Γ A B}
      → Frame {Γ} B (A `⊎ B)

    F-case : ∀ {Γ A B C}
      → Γ ⊢ A ⇒ C
      → Γ ⊢ B ⇒ C
      → Frame {Γ} (A `⊎ B) C

    F-cast : ∀ {Γ A B}
      → Cast (A ⇒ B)
      → Frame {Γ} A B

  {-

  The plug function inserts an expression into the hole of a frame.

  -}

  plug : ∀{Γ A B} → Γ ⊢ A → Frame {Γ} A B → Γ ⊢ B
  plug L (F-·₁ M)      = L · M
  plug M (F-·₂ L)      = L · M
  plug L (F-if M N)    = if L M N
  plug L (F-×₁ M)      = cons M L
  plug M (F-×₂ L)      = cons M L
  plug M (F-fst)      = fst M
  plug M (F-snd)      = snd M
  plug M (F-inl)      = inl M
  plug M (F-inr)      = inr M
  plug L (F-case M N) = case L M N
  plug M (F-cast c) = M ⟨ c ⟩

  {-

  We need a few more parameters to define reduction in a generic way.
  In particular, we need parameters that say how to reduce casts and
  how to eliminate values wrapped in casts. 
  * The applyCast parameter, applies an Active cast to a value. 
  * The funCast parameter applies a function wrapped in an inert cast
    to an argument.
  * The fstCast and sndCast parameters take the first or second part
    of a pair wrapped in an inert cast.
  * The caseCast performs a case-elimination on a value of sum type (inl or inr)
    that is wrapped in an inert cast.
  * The baseNotInert parameter ensures that every cast to a base type
    is not inert.

  We define a nested module named Reduction with these parameters
  because they all depend on parameters of the outer module, and it
  seems that Agda does not allow parameters to depend on other
  parameters of the same module.

  -}

  module Reduction
    (applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
                 → ∀ {a : Active c} → Γ ⊢ B)
    (funSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂)
    (pairSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' `× B'))) → (i : Inert c)
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂)
    (sumSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' `⊎ B'))) → (i : Inert c)
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂)
    (dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁))
    (cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B'))
    (fstC : ∀{A₁ A₂ B₁ B₂} → (c : Cast ((A₁ `× A₂) ⇒ (B₁ `× B₂))) → Inert c
         → Cast (A₁ ⇒ B₁))
    (sndC : ∀{A₁ A₂ B₁ B₂} → (c : Cast ((A₁ `× A₂) ⇒ (B₁ `× B₂))) → Inert c
         →  Cast (A₂ ⇒ B₂))
    (inlC : ∀{A₁ A₂ B₁ B₂} → (c : Cast ((A₁ `⊎ A₂) ⇒ (B₁ `⊎ B₂))) → Inert c
         → Cast (A₁ ⇒ B₁))
    (inrC : ∀{A₁ A₂ B₁ B₂} → (c : Cast ((A₁ `⊎ A₂) ⇒ (B₁ `⊎ B₂))) → Inert c
         →  Cast (A₂ ⇒ B₂))
    (baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c)
    where
    {- to do : add condition A ≢ ⋆ to baseNotInert -}

    {-

      The following defines the reduction relation for the
      Parameterized Cast Calulus.  The reductions involving casts
      simply dispatch to the appropriate parameters of this
      module. This includes the cast, fun-cast, fst-cast, snd-cast,
      and case-cast rules. To propagate blame to the top of the
      program, we have the ξ-blame rule. All of the usual congruence
      rules are instances of the one ξ rule with the appropriate
      choice of frame. The remaining rules are the usual β and δ
      reduction rules of the STLC.

      The reduction relation has a very specific type signature,
      mapping only well-typed terms to well-typed terms, so
      preservation is guaranteed by construction.

     -}

    infix 2 _—→_
    data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

      ξ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B}
        → M —→ M′
          ---------------------
        → plug M F —→ plug M′ F

      ξ-blame : ∀ {Γ A B} {F : Frame {Γ} A B} {ℓ}
          ---------------------------
        → plug (blame ℓ) F —→ blame ℓ

      β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
        → Value W
          --------------------
        → (ƛ N) · W —→ N [ W ]

      δ : ∀ {Γ : Context} {A B} {f : rep A → rep B} {k : rep A} {ab} {a} {b}
          ---------------------------------------------------
        → ($_ {Γ}{A ⇒ B} f {ab}) · (($ k){a}) —→ ($ (f k)){b}

      β-if-true :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
          -------------------------
        → if (($ true){f}) M N —→ M

      β-if-false :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
          --------------------------
        → if (($ false){f}) M N —→ N

      β-fst :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
        → Value V → Value W
          --------------------
        → fst (cons V W) —→ V

      β-snd :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
        → Value V → Value W
          --------------------
        → snd (cons V W) —→ W

      β-caseL : ∀ {Γ A B C} {V : Γ ⊢ A} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
        → Value V
          --------------------------
        → case (inl V) L M —→ L · V

      β-caseR : ∀ {Γ A B C} {V : Γ ⊢ B} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
        → Value V
          --------------------------
        → case (inr V) L M —→ M · V

      cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        → (v : Value V) → {a : Active c}
          ------------------------------
        → V ⟨ c ⟩ —→ applyCast V v c {a}

      fun-cast : ∀ {Γ A' B' A₁ A₂} {V : Γ ⊢ A₁ ⇒ A₂} {W : Γ ⊢ A'}
          {c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))}
        → (v : Value V) → Value W → {i : Inert c}
          --------------------------------------------------
        → (V ⟨ c ⟩) · W —→ (V · (W ⟨ dom c i ⟩)) ⟨ cod c i ⟩

      fst-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
          {c : Cast ((A `× B) ⇒ (A' `× B'))}
        → Value V → {i : Inert c}
          -------------------------------------
        → fst (V ⟨ c ⟩) —→ (fst V) ⟨ fstC c i ⟩

      snd-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
          {c : Cast ((A `× B) ⇒ (A' `× B'))}
        → Value V → {i : Inert c}
          -------------------------------------
        → snd (V ⟨ c ⟩) —→ (snd V) ⟨ sndC c i ⟩

      case-cast : ∀ {Γ A B A' B' C} {V : Γ ⊢ A `⊎ B}
          {W₁ : Γ ⊢ A' ⇒ C } {W₂ : Γ ⊢ B' ⇒ C}
          {c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))}
        → Value V → {i : Inert c}
          --------------------------------------------
        → case (V ⟨ c ⟩) W₁ W₂ —→
          case V (ƛ ((rename S_ W₁) · ((` Z) ⟨ inlC c i ⟩ )))
                 (ƛ ((rename S_ W₂) · ((` Z) ⟨ inrC c i ⟩ )))

    infix  2 _—↠_
    infixr 2 _—→⟨_⟩_
    infix  3 _∎

    data _—↠_ : ∀{Γ}{A} → Γ ⊢ A → Γ ⊢ A → Set where
      _∎ : ∀ {Γ}{A} (M : Γ ⊢ A)
          ---------
        → M —↠ M

      _—→⟨_⟩_ : ∀ {Γ}{A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
        → L —→ M
        → M —↠ N
          ---------
        → L —↠ N

    data Observe : Set where
      O-const : ∀{A} → rep A → Observe
      O-fun : Observe
      O-pair : Observe
      O-sum : Observe
      O-blame : Label → Observe

    observe : ∀ {Γ A} → (V : Γ ⊢ A) → Value V → Observe
    observe .(ƛ _) V-ƛ = O-fun
    observe {A = A} ($ k) V-const = O-const {A} k
    observe .(cons _ _) (V-pair v v₁) = O-pair
    observe .(inl _) (V-inl v) = O-sum
    observe .(inr _) (V-inr v) = O-sum
    observe (V ⟨ c ⟩) (V-cast v) = observe V v

    data Eval : ∀ {Γ A} → (Γ ⊢ A) → Observe → Set where
      eval : ∀{Γ}{A}{M V : Γ ⊢ A}
           → M —↠ V
           → (v : Value V)
           → Eval M (observe V v)

    {-

     The Progress data type has an additional error case to
     allow for cast errors, i.e., blame. We use the follow
     Error data type to help express the error case.

     -}

    data Error : ∀ {Γ A} → Γ ⊢ A → Set where

      E-blame : ∀ {Γ}{A}{ℓ}
          ---------------------
        → Error{Γ}{A} (blame ℓ)

    data Progress {A} (M : ∅ ⊢ A) : Set where

      step : ∀ {N : ∅ ⊢ A}
        → M —→ N
          -------------
        → Progress M

      done :
          Value M
          ----------
        → Progress M

      error :
          Error M
          ----------
        → Progress M

    {-

     The proof of progress follows the same structure as the one for
     the STLC, by induction on the structure of the expression (or
     equivalently, the typing derivation). In the following, we
     discuss the extra cases that are needed for this cast calculus.

     Each recursive call to progress may result in an error,
     in which case the current expression can take a step
     via the ξ-blame rule with an appropriate frame.

     On the other hand, if the recusive call produces a value, the
     value may be a cast that is inert. In the case for function
     application, the expression takes a step via the fun-cast rule
     (which uses the funCast parameter).  In the case for fst and snd,
     the expression takes a step via fst-cast or snd-cast
     respectively. Regarding the case form, the expression takes a
     step via case-cast.

     Of course, we must add a case for the cast form.
     If the recursive call produces a step, then we step via ξ.
     Likewise, if the recursive call produces an error, we step via ξ-blame.
     Otherwise, the recursive call produces a value.
     We make use of the ActiveOrInert parameter to see which
     kind of cast we are dealing with. If it is active, we reduce
     via the cast rule. Otherwise we form a value using V-cast.

     We must also consider the situations where the subexpression is
     of base type: the argument of a primitive operator and the
     condition of 'if'. In these two cases, the baseNotInert parameter
     ensures that the value not a cast, it is a constant.

     -}

    progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
    progress (` ())
    progress (ƛ M) = done V-ƛ
    progress (_·_ {∅}{A}{B} M₁ M₂)
        with progress M₁
    ... | step R = step (ξ {F = F-·₁ M₂} R)
    ... | error E-blame = step (ξ-blame {F = F-·₁ M₂})
    ... | done V₁
            with progress M₂
    ...     | step R' = step (ξ {F = (F-·₂ M₁){V₁}} R')
    ...     | error E-blame = step (ξ-blame {F = (F-·₂ M₁){V₁}})
    ...     | done V₂ with V₁
    ...         | V-ƛ = step (β V₂)
    ...         | V-cast {∅}{A = A'}{B = A ⇒ B}{V}{c}{i} v
                with funSrc c i
    ...         | ⟨ A₁' , ⟨ A₂' , refl ⟩ ⟩ =
                    step (fun-cast v V₂ {i})
    progress (_·_ {∅}{A}{B} M₁ M₂) | done V₁ | done V₂
                | V-const {k = k₁} {f = f₁} with V₂
    ...             | V-const {k = k₂} {f = f₂} =
                      step (δ {ab = f₁} {a = f₂} {b = P-Fun2 f₁})
    ...             | V-ƛ = contradiction f₁ ¬P-Fun
    ...             | V-pair v w = contradiction f₁ ¬P-Pair
    ...             | V-inl v = contradiction f₁ ¬P-Sum
    ...             | V-inr v = contradiction f₁ ¬P-Sum
    ...             | V-cast {∅}{A'}{A}{W}{c}{i} w =
                       contradiction i (G f₁)
                       where G : Prim (A ⇒ B) → ¬ Inert c
                             G (P-Fun f₁) ic = baseNotInert c ic
    progress ($ k) = done V-const
    progress (if L M N) with progress L
    ... | step {L'} R = step (ξ{F = F-if M N} R)
    ... | error E-blame = step (ξ-blame{F = F-if M N})
    ... | done (V-const {k = true}) = step β-if-true
    ... | done (V-const {k = false}) = step β-if-false
    ... | done (V-cast {c = c} {i = i} v) =
            contradiction i (baseNotInert c)

    progress (_⟨_⟩ {∅}{A}{B} M c) with progress M
    ... | step {N} R = step (ξ{F = F-cast c} R)
    ... | error E-blame = step (ξ-blame{F = F-cast c})
    ... | done v with ActiveOrInert c
    ...    | inj₁ a = step (cast v {a})
    ...    | inj₂ i = done (V-cast {c = c} {i = i} v)
    progress {C₁ `× C₂} (cons M₁ M₂) with progress M₁
    ... | step {N} R = step (ξ {F = F-×₂ M₂} R)
    ... | error E-blame = step (ξ-blame {F = F-×₂ M₂})
    ... | done V with progress M₂
    ...    | step {N} R' = step (ξ {F = F-×₁ M₁} R')
    ...    | done V' = done (V-pair V V')
    ...    | error E-blame = step (ξ-blame{F = F-×₁ M₁})
    progress (fst {Γ}{A}{B} M) with progress M
    ... | step {N} R = step (ξ {F = F-fst} R)
    ... | error E-blame = step (ξ-blame{F = F-fst})
    ... | done V
            with V
    ...     | V-pair {V = V₁}{W = V₂} v w = step {N = V₁} (β-fst v w)
    ...     | V-const {k = ()}
    ...     | V-cast {c = c} {i = i} v
                with pairSrc c i
    ...         | ⟨ A₁' , ⟨ A₂' , refl ⟩ ⟩ =
                  step (fst-cast {c = c} v {i = i})
    progress (snd {Γ}{A}{B} M) with progress M
    ... | step {N} R = step (ξ {F = F-snd} R)
    ... | error E-blame = step (ξ-blame{F = F-snd})
    ... | done V with V
    ...     | V-pair {V = V₁}{W = V₂} v w = step {N = V₂} (β-snd v w)
    ...     | V-const {k = ()}
    ...     | V-cast {c = c} {i = i} v
                with pairSrc c i
    ...         | ⟨ A₁' , ⟨ A₂' , refl ⟩ ⟩ =
                  step (snd-cast {c = c} v {i = i})
    progress (inl M) with progress M
    ... | step R = step (ξ {F = F-inl} R)
    ... | error E-blame = step (ξ-blame {F = F-inl})
    ... | done V = done (V-inl V)

    progress (inr M) with progress M
    ... | step R = step (ξ {F = F-inr} R)
    ... | error E-blame = step (ξ-blame {F = F-inr})
    ... | done V = done (V-inr V)

    progress (case L M N) with progress L
    ... | step R = step (ξ {F = F-case M N} R)
    ... | error E-blame = step (ξ-blame {F = F-case M N})
    ... | done V with V
    ...    | V-const {k = ()}
    ...    | V-inl v = step (β-caseL v)
    ...    | V-inr v = step (β-caseR v)
    ...    | V-cast {c = c} {i = i} v
                with sumSrc c i
    ...         | ⟨ A₁' , ⟨ A₂' , refl ⟩ ⟩ = step (case-cast {c = c} v {i = i})

    progress (blame ℓ) = error E-blame

