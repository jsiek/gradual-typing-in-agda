open import Types
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

  This module provides an alternative reduction relation for the
  Parameterized Cast Calculus that ensures space efficiency.  It
  accomplishes this by merging adjacent casts using a compose
  operation that must be provided by the client of the module.

-}

module EfficientParamCasts
  (Cast : Type → Set)
  (Inert : ∀{A} → Cast A → Set)
  (Active : ∀{A} → Cast A → Set)  
  (ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c)
  where

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  {-

   The notion of Value changes to only allow a single cast in a value.
   So a value is a simple value (no cast) with an optional cast around it.

  -}

  data Value : ∀ {Γ A} → Γ ⊢ A → Set
  
  data SimpleValue : ∀ {Γ A} → Γ ⊢ A → Set where

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        -----------------
      → SimpleValue (ƛ N)

    V-const : ∀ {Γ} {A : Type} {k : rep A} {f : Prim A}
        ------------------------------
      → SimpleValue {Γ} {A} (($ k){f})

    V-pair : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        ----------------------
      → SimpleValue (cons V W)

    V-inl : ∀ {Γ A B} {V : Γ ⊢ A}
      → Value V
        --------------------------------
      → SimpleValue {Γ} {A `⊎ B} (inl V)

    V-inr : ∀ {Γ A B} {V : Γ ⊢ B}
      → Value V
        --------------------------------
      → SimpleValue {Γ} {A `⊎ B} (inr V)


  data Value where
    S-val : ∀ {Γ A}{V : Γ ⊢ A}
      → SimpleValue V
        -------------
      → Value V

    V-cast : ∀ {Γ : Context} {A B : Type} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        {i : Inert c}
      → SimpleValue V
        ---------------
      → Value (V ⟨ c ⟩)

  simple⋆ : ∀ {Γ A} → (M : Γ ⊢ A) → (SimpleValue M) → A ≢ ⋆
  simple⋆ .(ƛ _) V-ƛ = λ ()
  simple⋆ ((ParamCastCalculus.$ k) {P-Nat}) V-const = λ ()
  simple⋆ ((ParamCastCalculus.$ k) {P-Bool}) V-const = λ ()
  simple⋆ ((ParamCastCalculus.$ k) {P-Fun x f}) V-const = λ ()
  simple⋆ .(cons _ _) (V-pair x x₁) = λ ()
  simple⋆ .(inl _) (V-inl x) = λ ()
  simple⋆ .(inr _) (V-inr x) = λ ()

  canonical⋆ : ∀ {Γ} → (M : Γ ⊢ ⋆) → (Value M)
             → Σ[ A ∈ Type ] Σ[ M' ∈ (Γ ⊢ A) ] Σ[ c ∈ (Cast (A ⇒ ⋆)) ]
                 Inert c × (M ≡ (M' ⟨ c ⟩)) × A ≢ ⋆
  canonical⋆ .($ _) (S-val (V-const {f = ()}))
  canonical⋆ (M ⟨ _ ⟩) (V-cast{A = A}{B = B}{V = V}{c = c}{i = i} v) =
    ⟨ A , ⟨ V , ⟨ c , ⟨ i , ⟨ refl , simple⋆ M v ⟩ ⟩ ⟩ ⟩ ⟩

  simple-base : ∀ {Γ A} → (M : Γ ⊢ A) → SimpleValue M → Base A
     → Σ[ k ∈ rep A ] Σ[ f ∈ Prim A ] M ≡ ($ k){f}
  simple-base (ƛ _) V-ƛ ()
  simple-base (($ k){f}) V-const b = ⟨ k , ⟨ f , refl ⟩ ⟩
  simple-base .(cons _ _) (V-pair x x₁) ()
  simple-base .(inl _) (V-inl x) ()
  simple-base .(inr _) (V-inr x) ()
  
  {-

   The Reduction inner module has an additional parameter, the compose
   function.

   -}

  module Reduction
    (applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
               → ∀ {a : Active c} → Γ ⊢ B)
    (funCast : ∀{Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
             → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B')
    (fstCast : ∀{Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
             → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A')
    (sndCast : ∀{Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
             → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B')
    (caseCast : ∀{Γ A A' B' C} → (L : Γ ⊢ A) → SimpleValue L
              → (c : Cast (A ⇒ (A' `⊎ B')))
              → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C)
    (baseNotInert : ∀ {A B} → (c : Cast (A ⇒ B)) → Base B → A ≢ ⋆ → ¬ Inert c)
    (compose : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
             → Cast (A ⇒ C))
    where

    {-

    The definition of Frame does not include a constructor for casts,
    but is otherwise the same as in ParamCastReduction.  Casts will be
    given special treatment.

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
        → Frame {Γ} 𝔹 A

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

    {-

     We parameterize the reduction relation according to whether the
     congruence rule for casts, ξ-cast, may be used in the current
     context or not. In particular, we want to disallow reduction
     under a sequence of two or more casts. So the ξ-cast rule
     requires the parameter to be 'allow', and it changes the
     parameter 'disallow' for reducing the subexpression. We include a
     kind of subsumption rule, named switch, that implicitly changes
     from 'allow' to 'disallow'. (The other direction would ruin space
     efficiency.) The rest of the reduction rules are given the
     'disallow' parameter, which means that they can fire in both
     allow and disallow contexts thanks to the switch rule.

     -}

    data BypassCast : Set where
      allow : BypassCast
      disallow : BypassCast

    infix 2 _/_—→_
    data _/_—→_ : ∀ {Γ A} → BypassCast → (Γ ⊢ A) → (Γ ⊢ A) → Set where

      switch : ∀ {Γ A} {M M′ : Γ ⊢ A} 
        → disallow / M —→ M′
          ------------------
        → allow / M —→ M′       

      ξ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B}
        → allow / M —→ M′
          ---------------------
        → disallow / plug M F —→ plug M′ F

      ξ-cast : ∀ {Γ A B} {c : Cast (A ⇒ B)} {M M′ : Γ ⊢ A}
        → disallow / M —→ M′
          -----------------------------
        → allow / (M ⟨ c ⟩) —→ M′ ⟨ c ⟩

      ξ-blame : ∀ {Γ A B} {F : Frame {Γ} A B} {ℓ}
          ---------------------------
        → disallow / plug (blame ℓ) F —→ blame ℓ

      ξ-cast-blame : ∀ {Γ A B} {c : Cast (A ⇒ B)} {ℓ}
          ----------------------------------------------
        → allow / ((blame {Γ}{A} ℓ) ⟨ c ⟩) —→ blame ℓ

      β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
        → Value W
          -------------------------------
        → disallow / (ƛ N) · W —→ N [ W ]

      δ : ∀ {Γ : Context} {A B} {f : rep A → rep B} {k : rep A} {ab} {a} {b}
          --------------------------------------------
        → disallow / ($_ {Γ} f {ab}) · (($ k){a}) —→ ($ (f k)){b}

      β-if-true : ∀{Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
          --------------------------------------
        → disallow / if (($ true){f}) M N —→ M

      β-if-false : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
          ---------------------
        → disallow / if (($ false){f}) M N —→ N

      β-fst : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
        → Value V → Value W
          --------------------
        → disallow / fst (cons V W) —→ V

      β-snd :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
        → Value V → Value W
          --------------------
        → disallow / snd (cons V W) —→ W

      β-caseL : ∀ {Γ A B C} {V : Γ ⊢ A} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
        → Value V
          --------------------------
        → disallow / case (inl V) L M —→ L · V

      β-caseR : ∀ {Γ A B C} {V : Γ ⊢ B} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
        → Value V
          --------------------------
        → disallow / case (inr V) L M —→ M · V

      cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        → (v : Value V) → {a : Active c}
          ----------------------------
        → disallow / V ⟨ c ⟩ —→ applyCast V v c {a}

      fun-cast : ∀ {Γ A A' B'} {V : Γ ⊢ A} {W : Γ ⊢ A'}
          {c : Cast (A ⇒ (A' ⇒ B'))}
        → (v : SimpleValue V) → Value W → {i : Inert c}
          -----------------------------------------------
        → disallow / (V ⟨ c ⟩) · W —→ funCast V v c {i} W 

      fst-cast : ∀ {Γ A A' B'} {V : Γ ⊢ A}
          {c : Cast (A ⇒ (A' `× B'))}
        → (v : SimpleValue V) → {i : Inert c}
          --------------------------------------------
        → disallow / fst (V ⟨ c ⟩) —→ fstCast V v c {i}

      snd-cast : ∀ {Γ A A' B'} {V : Γ ⊢ A}
          {c : Cast (A ⇒ (A' `× B'))}
        → (v : SimpleValue V) → {i : Inert c}
          ---------------------------------------------
        → disallow / snd (V ⟨ c ⟩) —→ sndCast V v c {i}

      case-cast : ∀ { Γ A A' B' C} {V : Γ ⊢ A}
          {W : Γ ⊢ A' ⇒ C } {W' : Γ ⊢ B' ⇒ C}
          {c : Cast (A ⇒ (A' `⊎ B'))}
        → (v : SimpleValue V) → {i : Inert c}
          ---------------------------------------------------------
        → disallow / case (V ⟨ c ⟩) W W' —→ caseCast V v c {i} W W'

      compose-casts : ∀{Γ A B C} {M : Γ ⊢ A }
          {c : Cast (A ⇒ B)} {d : Cast (B ⇒ C)}
          ------------------------------------------
        → disallow / (M ⟨ c ⟩) ⟨ d ⟩ —→ M ⟨ compose c d ⟩


    data Error : ∀ {Γ A} → Γ ⊢ A → Set where

      E-blame : ∀ {Γ}{A}{ℓ}
          ---------------------
        → Error{Γ}{A} (blame ℓ)

    {-

     For the proof of progress, we split 'step' into two cases, one
     for an 'disallow' reduction, 'step-d' and one for an 'allow'
     reduction, 'step-a'.

    -}

    data Progress {A} (M : ∅ ⊢ A) : Set where

      step-d : ∀ {N : ∅ ⊢ A}
        → disallow / M —→ N
          -------------
        → Progress M

      step-a : ∀ {N : ∅ ⊢ A}
        → allow / M —→ N
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

    For the proof of progress, each recursive call may now result
    in a step-d or a step-a (in addition to error and done).
    However, the proofs for the two cases are the same except
    for a use of 'switch' in the step-d case.

    The most important changes occur in the case for casts.  We
    consider the possible results from progress applied to the
    subexpression. 

    * If it does a step-d, that is, performs a step that did not go
      under a cast, then the current expression can reduce via step-a
      and ξ-cast.

    * If it does a step-a, we have three cases two consider.

       - The reduction was via 'switch', so the underlying reduction
         was in a disallow context. We can again reduce via step-a and
         ξ-cast.

       - The reduction was via ξ-cast. This is the most important
         case, as we have two adjacent casts. We ignore the underlying
         reduction and instead take a step-d via compose-casts.

       - The reduction was via ξ-cast-blame. Again we have two
         adjacent casts so we compose-casts.

    -}

    progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
    progress (` ())
    progress (ƛ M) = done (S-val V-ƛ)
    progress (_·_ {∅}{A}{B} M₁ M₂) with progress M₁
    ... | step-d R = step-d (ξ {F = F-·₁ M₂} (switch R))
    ... | step-a R = step-d (ξ {F = F-·₁ M₂} R)
    ... | error E-blame = step-d (ξ-blame {F = F-·₁ M₂})
    ... | done V₁ with progress M₂
    ...     | step-d R' = step-d (ξ {F = (F-·₂ M₁){V₁}} (switch R'))
    ...     | step-a R' = step-d (ξ {F = (F-·₂ M₁){V₁}} R')
    ...     | error E-blame = step-d (ξ-blame {F = (F-·₂ M₁){V₁}})
    ...     | done V₂ with V₁
    ...         | S-val V-ƛ = step-d (β V₂)
    ...         | V-cast {∅}{A = A'}{B = A ⇒ B}{V}{c}{i} v =
                    step-d (fun-cast{∅}{A'}{A}{B}{V}{M₂}{c} v V₂ {i})
    ...         | S-val (V-const {k = k₁} {f = f₁}) with V₂
    ...             | S-val (V-const {k = k₂} {f = f₂}) =
                      step-d (δ {ab = f₁} {a = f₂} {b = P-Fun2 f₁})
    ...             | S-val V-ƛ = contradiction f₁ ¬P-Fun
    ...             | S-val (V-pair v w) = contradiction f₁ ¬P-Pair
    ...             | S-val (V-inl v) = contradiction f₁ ¬P-Sum
    ...             | S-val (V-inr v) = contradiction f₁ ¬P-Sum
    ...             | V-cast {∅}{A'}{A}{W}{c}{i} w =
                         contradiction i (baseNotInert c (P-Fun1 f₁)
                            (simple⋆ W w))
    progress ($ k) = done (S-val V-const)
    progress (if L M N) with progress L
    ... | step-d R = step-d (ξ{F = F-if M N} (switch R))
    ... | step-a R = step-d (ξ{F = F-if M N} R)
    ... | error E-blame = step-d (ξ-blame{F = F-if M N})
    ... | done (S-val (V-const {k = true})) = step-d β-if-true
    ... | done (S-val (V-const {k = false})) = step-d β-if-false
    ... | done (V-cast {V = V} {c = c} {i = i} v) =
            contradiction i (baseNotInert c B-Bool (simple⋆ V v))
    progress (_⟨_⟩ {∅}{A}{B} M c) with progress M
    ... | step-d {N} R = step-a (ξ-cast R)
    ... | step-a (switch R) = step-a (ξ-cast R)
    ... | step-a (ξ-cast R) = step-d compose-casts
    ... | step-a (ξ-cast-blame) = step-d compose-casts
    ... | error E-blame = step-a ξ-cast-blame
    ... | done v with ActiveOrInert c
    ...    | inj₁ a = step-d (cast v {a})
    ...    | inj₂ i
           with v
    ...    | S-val v' = done (V-cast {c = c} {i = i} v')
    ...    | V-cast{A = A'}{B = A} {c = c'} v' = step-d compose-casts
    progress {C₁ `× C₂} (cons M₁ M₂) with progress M₁
    ... | step-d R = step-d (ξ {F = F-×₂ M₂} (switch R))
    ... | step-a R = step-d (ξ {F = F-×₂ M₂} R)
    ... | error E-blame = step-d (ξ-blame {F = F-×₂ M₂})
    ... | done V with progress M₂
    ...    | step-d {N} R' = step-d (ξ {F = F-×₁ M₁} (switch R'))
    ...    | step-a R' = step-d (ξ {F = F-×₁ M₁} R')
    ...    | done V' = done (S-val (V-pair V V'))
    ...    | error E-blame = step-d (ξ-blame{F = F-×₁ M₁})
    progress (fst {Γ}{A}{B} M) with progress M
    ... | step-d R = step-d (ξ {F = F-fst} (switch R))
    ... | step-a R = step-d (ξ {F = F-fst} R)
    ... | error E-blame = step-d (ξ-blame{F = F-fst})
    ... | done V with V
    ...     | V-cast {c = c} {i = i} v =
              step-d (fst-cast {c = c} v {i = i})
    ...     | S-val (V-pair {V = V₁}{W = V₂} v w) =
              step-d {N = V₁} (β-fst v w)
    ...     | S-val (V-const {k = k}) with k
    ...        | ()
    progress (snd {Γ}{A}{B} M) with progress M
    ... | step-d R = step-d (ξ {F = F-snd} (switch R))
    ... | step-a R = step-d (ξ {F = F-snd} R)
    ... | error E-blame = step-d (ξ-blame{F = F-snd})
    ... | done V with V
    ...     | V-cast {c = c} {i = i} v =
              step-d (snd-cast {c = c} v {i = i})
    ...     | S-val (V-pair {V = V₁}{W = V₂} v w) =
              step-d {N = V₂} (β-snd v w)
    ...     | S-val (V-const {k = k}) with k
    ...        | ()
    progress (inl M) with progress M
    ... | step-d R = step-d (ξ {F = F-inl} (switch R))
    ... | step-a R = step-d (ξ {F = F-inl} R)
    ... | error E-blame = step-d (ξ-blame {F = F-inl})
    ... | done V = done (S-val (V-inl V))

    progress (inr M) with progress M
    ... | step-d R = step-d (ξ {F = F-inr} (switch R))
    ... | step-a R = step-d (ξ {F = F-inr} R)
    ... | error E-blame = step-d (ξ-blame {F = F-inr})
    ... | done V = done (S-val (V-inr V))

    progress (case L M N) with progress L
    ... | step-d R = step-d (ξ {F = F-case M N} (switch R))
    ... | step-a R = step-d (ξ {F = F-case M N} R)
    ... | error E-blame = step-d (ξ-blame {F = F-case M N})
    ... | done V with V
    ...    | V-cast {c = c} {i = i} v =
             step-d (case-cast {c = c} v {i = i})
    ...    | S-val (V-const {k = k}) = ⊥-elim k
    ...    | S-val (V-inl v) = step-d (β-caseL v)
    ...    | S-val (V-inr v) = step-d (β-caseR v)

    progress (blame ℓ) = error E-blame


