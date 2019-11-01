open import Types
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_; Dec; yes; no)
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
  simple⋆ ((ParamCastCalculus.$ k) {P-Base}) V-const = λ ()
  simple⋆ ((ParamCastCalculus.$ k) {P-Fun f}) V-const = λ ()
  simple⋆ .(cons _ _) (V-pair x x₁) = λ ()
  simple⋆ .(inl _) (V-inl x) = λ ()
  simple⋆ .(inr _) (V-inr x) = λ ()

  canonical⋆ : ∀ {Γ} → (M : Γ ⊢ ⋆) → (Value M)
             → Σ[ A ∈ Type ] Σ[ M' ∈ (Γ ⊢ A) ] Σ[ c ∈ (Cast (A ⇒ ⋆)) ]
                 Inert c × (M ≡ (M' ⟨ c ⟩)) × A ≢ ⋆
  canonical⋆ .($ _) (S-val (V-const {f = ()}))
  canonical⋆ (M ⟨ _ ⟩) (V-cast{A = A}{B = B}{V = V}{c = c}{i = i} v) =
    ⟨ A , ⟨ V , ⟨ c , ⟨ i , ⟨ refl , simple⋆ M v ⟩ ⟩ ⟩ ⟩ ⟩

  simple-base : ∀ {Γ ι} → (M : Γ ⊢ ` ι) → SimpleValue M 
     → Σ[ k ∈ rep-base ι ] Σ[ f ∈ Prim (` ι) ] M ≡ ($ k){f}
  simple-base (($ k){f}) V-const = ⟨ k , ⟨ f , refl ⟩ ⟩
  
  {-

   The Reduction inner module has an additional parameter, the compose
   function.

   -}

  module Reduction
    (applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
               → ∀ {a : Active c} → Γ ⊢ B)
    (funSrc : ∀{A A' B' Γ}
            → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → (M : Γ ⊢ A) → SimpleValue M
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂)
    (dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁))
    (cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B'))
    (fstCast : ∀{Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
             → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A')
    (sndCast : ∀{Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
             → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B')
    (caseCast : ∀{Γ A A' B' C} → (L : Γ ⊢ A) → SimpleValue L
              → (c : Cast (A ⇒ (A' `⊎ B')))
              → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C)
    (baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → A ≢ ⋆ → ¬ Inert c)
    (compose : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
             → Cast (A ⇒ C))
    where

    {-

    The definition of Frame does not include a constructor for casts,
    but is otherwise the same as in ParamCastReduction.  Casts will be
    given special treatment.

    -}

    data Frame : {Γ : Context} → Type → Type → Set 

    data EFrame : {Γ : Context} → Type → Type → Set where
    
      E-F : ∀ {Γ}{A B} → Frame {Γ} A B → EFrame {Γ} A B
      
      E-Cast : ∀ {Γ}{A B} → Cast (A ⇒ B) → EFrame {Γ} A B

    data Frame where

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

    plug-e : ∀{Γ A B} → Γ ⊢ A → EFrame {Γ} A B → Γ ⊢ B
    plug-e M (E-F f) = plug M f
    plug-e M (E-Cast c) = M ⟨ c ⟩
    
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

    data ReductionCtx : Set where
      e_ctx : ReductionCtx
      f_ctx : ReductionCtx

    infix 2 _/_—→_
    data _/_—→_ : ∀ {Γ A} → ReductionCtx → (Γ ⊢ A) → (Γ ⊢ A) → Set where

      ξ-F : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B}
        → f_ctx / M —→ M′
          ---------------------------
        → e_ctx / plug M F —→ plug M′ F

      ξ-FE : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B}
        → e_ctx / M —→ M′
          ---------------------------
        → e_ctx / plug M F —→ plug M′ F

      ξ-E : ∀ {Γ A B} {M M′ : Γ ⊢ A} {E : EFrame A B}
        → e_ctx / M —→ M′
          ---------------------------------
        → f_ctx / plug-e M E —→ plug-e M′ E

      ξ-blame : ∀ {Γ A B} {E : EFrame {Γ} A B} {ℓ} 
          -------------------------------------
        → e_ctx / plug-e (blame ℓ) E —→ blame ℓ

      β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A} 
        → Value W
          -------------------------------
        → e_ctx / (ƛ N) · W —→ N [ W ]

      δ : ∀ {Γ}{A B}{f : rep A → rep B}{k : rep A}{ab}{a}{b}
          ---------------------------------------------------------
        → e_ctx / ($_ {Γ}{A ⇒ B} f {ab}) · (($ k){a}) —→ ($ (f k)){b}

      β-if-true : ∀{Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
          -------------------------------
        → e_ctx / if (($ true){f}) M N —→ M

      β-if-false : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
          ---------------------
        → e_ctx / if (($ false){f}) M N —→ N

      β-fst : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
        → Value V → Value W
          --------------------
        → e_ctx / fst (cons V W) —→ V

      β-snd :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
        → Value V → Value W
          --------------------
        → e_ctx / snd (cons V W) —→ W

      β-caseL : ∀ {Γ A B C} {V : Γ ⊢ A} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
        → Value V
          --------------------------
        → e_ctx / case (inl V) L M —→ L · V

      β-caseR : ∀ {Γ A B C} {V : Γ ⊢ B} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
        → Value V
          --------------------------
        → e_ctx / case (inr V) L M —→ M · V

      cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        → (v : Value V) → {a : Active c}
          ----------------------------
        → f_ctx / V ⟨ c ⟩ —→ applyCast V v c {a}

      fun-cast : ∀ {Γ A' B' A₁ A₂} {V : Γ ⊢ A₁ ⇒ A₂} {W : Γ ⊢ A'}
          {c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))} 
        → (v : SimpleValue V) → Value W → {i : Inert c}
          -------------------------------------------------------------
        → e_ctx / (V ⟨ c ⟩) · W —→ (V · (W ⟨ dom c i ⟩)) ⟨ cod c i ⟩

      fst-cast : ∀ {Γ A A' B'} {V : Γ ⊢ A} 
          {c : Cast (A ⇒ (A' `× B'))} 
        → (v : SimpleValue V) → {i : Inert c}
          --------------------------------------------
        → e_ctx / fst (V ⟨ c ⟩) —→ fstCast V v c {i}

      snd-cast : ∀ {Γ A A' B'} {V : Γ ⊢ A}
          {c : Cast (A ⇒ (A' `× B'))} 
        → (v : SimpleValue V) → {i : Inert c}
          ---------------------------------------------
        → e_ctx / snd (V ⟨ c ⟩) —→ sndCast V v c {i}

      case-cast : ∀ { Γ A A' B' C} {V : Γ ⊢ A}
          {W : Γ ⊢ A' ⇒ C } {W' : Γ ⊢ B' ⇒ C}
          {c : Cast (A ⇒ (A' `⊎ B'))} 
        → (v : SimpleValue V) → {i : Inert c}
          ---------------------------------------------------------
        → e_ctx / case (V ⟨ c ⟩) W W' —→ caseCast V v c {i} W W'

      compose-casts : ∀{Γ A B C} {M : Γ ⊢ A }
          {c : Cast (A ⇒ B)} {d : Cast (B ⇒ C)} 
          ------------------------------------------
        → f_ctx / (M ⟨ c ⟩) ⟨ d ⟩ —→ M ⟨ compose c d ⟩


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

      step : ∀ {N : ∅ ⊢ A} {ctx : ReductionCtx}
        → ctx / M —→ N
          -------------------
        → Progress M

      done :
          Value M
          ----------
        → Progress M

      error :
          Error M
          ----------
        → Progress M


    data IsCast : ∀{Γ}{A} → Γ ⊢ A → Set where
      isCast : ∀{Γ}{A B}{M : Γ ⊢ A} {c : Cast (A ⇒ B)} → IsCast (M ⟨ c ⟩)

    is-cast? : ∀{Γ}{A} → (M : Γ ⊢ A) → Dec (IsCast M)
    is-cast? (` x) = no λ ()
    is-cast? (ƛ M) = no λ ()
    is-cast? (M · M₁) = no λ ()
    is-cast? ($ x) = no λ ()
    is-cast? (if M M₁ M₂) = no λ ()
    is-cast? (cons M M₁) = no λ ()
    is-cast? (fst M) = no λ ()
    is-cast? (snd M) = no λ ()
    is-cast? (inl M) = no λ ()
    is-cast? (inr M) = no λ ()
    is-cast? (case M M₁ M₂) = no λ ()
    is-cast? (M ⟨ x ⟩) = yes isCast
    is-cast? (blame x) = no λ ()

{-
    f-red-is-cast : ∀ {Γ A} {M M′ : Γ ⊢ A}
        → f_ctx / M —→ M′
        → IsCast M
    f-red-is-cast (cast v) = isCast
    f-red-is-cast compose-casts = isCast
    f-red-is-cast (ξ-E x) = ?
-}  

    switch-back : ∀ {Γ A} {M M′ : Γ ⊢ A}
        → ¬ IsCast M
        → f_ctx / M —→ M′
          ------------------
        → e_ctx / M —→ M′
    switch-back nc (ξ-E {E = E-F F} R) = ξ-FE {F = F} R
    switch-back nc (ξ-E {E = E-Cast c} R) = contradiction isCast nc
    switch-back nc (cast v) = contradiction isCast nc
    switch-back nc compose-casts = contradiction isCast nc
{-
    switch-back nc (ξ-cast R) = contradiction isCast nc
    switch-back nc ξ-cast-blame = contradiction isCast nc
    switch-back nc (cast v) = contradiction isCast nc
    switch-back nc compose-casts = contradiction isCast nc
-}

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
    progress (ƛ M) = done (S-val V-ƛ)
    progress {A} (_·_ {Γ}{A₁}{A} M₁ M₂)
        with progress M₁
    ... | step {N = N} {ctx = e_ctx } R =
          step {N = N · M₂} {ctx = f_ctx} (ξ-E {E = E-F (F-·₁ M₂)} R)
    ... | step {ctx = f_ctx } R = step (ξ-F {F = F-·₁ M₂} R)
    ... | error E-blame = step (ξ-blame {A = A₁ ⇒ A}{E = E-F (F-·₁ M₂)})
    progress {A} (M₁ · M₂) | done V₁
          with progress M₂
    ...   | step {ctx = f_ctx} R = step (ξ-F {F = F-·₂ M₁ {V₁}} R)
    ...   | step {ctx = e_ctx} R = step (ξ-E {E = E-F (F-·₂ M₁ {V₁})} R)
    ...   | error E-blame = step (ξ-blame {E = E-F (F-·₂ M₁ {V₁})})
    progress {A} (_·_ {A = A₁} M₁ M₂) | done V₁ | done V₂
            with V₁
    ...     | S-val V-ƛ  = step (β V₂)
    ...     | S-val (V-const {k = k₁}{f = f₁})
              with V₂
    ...       | S-val (V-const {k = k₂}{f = f₂}) =
                step (δ {ab = f₁}{a = f₂}{b = P-Fun2 f₁})
    ...       | V-cast {V = W}{c}{i} sW =
                contradiction i (G f₁)
                where G : Prim (A₁ ⇒ A) → ¬ Inert c
                      G (P-Fun p) ic = baseNotInert c (simple⋆ W sW) ic
    progress {A} (M₁ · M₂) | done V₁ | done V₂
            | V-cast {V = V}{c}{i} v
              with funSrc c i V v
    ...       | ⟨ B , ⟨ C , refl ⟩ ⟩ = step (fun-cast v V₂ {i})
    progress ($ k) = done (S-val V-const)
    progress (if L M N)
        with progress L
    ... | step {ctx = f_ctx} R = step (ξ-F {F = F-if M N} R)
    ... | step {ctx = e_ctx} R = step (ξ-E {E = E-F (F-if M N)} R)
    ... | error E-blame = step (ξ-blame {E = E-F (F-if M N)})
    ... | done (S-val (V-const {k = true})) = step β-if-true
    ... | done (S-val (V-const {k = false})) = step β-if-false
    ... | done (V-cast {V = V}{c}{i} v) =
          contradiction i (baseNotInert c (simple⋆ V v))
    progress (cons M₁ M₂)
        with progress M₁
    ... | step {ctx = f_ctx} R = step (ξ-F {F = F-×₂ M₂} R)
    ... | step {ctx = e_ctx} R = step (ξ-E {E = E-F (F-×₂ M₂)} R)
    ... | error E-blame = step (ξ-blame {E = E-F (F-×₂ M₂)})
    ... | done V with progress M₂
    ...    | step {ctx = f_ctx} R = step (ξ-F {F = F-×₁ M₁} R)
    ...    | step {ctx = e_ctx} R = step (ξ-E {E = E-F (F-×₁ M₁)} R)
    ...    | done V' = done (S-val (V-pair V V'))
    ...    | error E-blame = step (ξ-blame {E = E-F (F-×₁ M₁)})
    progress (fst M)
        with progress M
    ... | step {ctx = f_ctx} R = step (ξ-F {F = F-fst} R)
    ... | step {ctx = e_ctx} R = step (ξ-E {E = E-F F-fst} R)
    ... | error E-blame = step (ξ-blame {E = E-F F-fst})
    ... | done V with V
    ...     | V-cast {c = c} {i = i} v = step (fst-cast {c = c} v {i = i})
    ...     | S-val (V-pair {V = V₁}{W = V₂} v w) = step (β-fst v w)
    ...     | S-val (V-const {k = k}) with k
    ...        | ()
    progress (snd M)
        with progress M
    ... | step {ctx = f_ctx} R = step (ξ-F {F = F-snd} R)
    ... | step {ctx = e_ctx} R = step (ξ-E {E = E-F F-snd} R)
    ... | error E-blame = step (ξ-blame{E = E-F F-snd})
    ... | done V with V
    ...     | V-cast {c = c} {i = i} v = step (snd-cast {c = c} v {i = i})
    ...     | S-val (V-pair {V = V₁}{W = V₂} v w) = step (β-snd v w)
    ...     | S-val (V-const {k = k}) with k
    ...        | ()
    progress (inl M)
        with progress M
    ... | step {ctx = f_ctx} R = step (ξ-F {F = F-inl} R)
    ... | step {ctx = e_ctx} R = step (ξ-E {E = E-F F-inl} R)
    ... | error E-blame = step (ξ-blame {E = E-F F-inl})
    ... | done V = done (S-val (V-inl V))
    progress (inr M)
        with progress M
    ... | step {ctx = f_ctx} R = step (ξ-F {F = F-inr} R)
    ... | step {ctx = e_ctx} R = step (ξ-E {E = E-F F-inr} R)
    ... | error E-blame = step (ξ-blame {E = E-F F-inr})
    ... | done V = done (S-val (V-inr V))
    progress (case L M N)
        with progress L
    ... | step {ctx = f_ctx} R = step (ξ-F {F = F-case M N} R)
    ... | step {ctx = e_ctx} R = step (ξ-E {E = E-F (F-case M N)} R)
    ... | error E-blame = step (ξ-blame {E = E-F (F-case M N)})
    ... | done V with V
    ...    | V-cast {c = c} {i = i} v =
             step (case-cast {c = c} v {i = i})
    ...    | S-val (V-inl v) = step (β-caseL v)
    ...    | S-val (V-inr v) = step (β-caseR v)
    progress (blame ℓ) = error E-blame
    progress (M ⟨ c ⟩)
        with progress M
    ... | step {ctx = e_ctx} R = step (ξ-E {E = E-Cast c} R)
    ... | step {ctx = f_ctx} R
          with is-cast? M
    ...   | yes isCast = step compose-casts
    ...   | no ncM =
            step (ξ-E {E = E-Cast c} (switch-back ncM R))
    progress (M ⟨ c ⟩)
        | error E-blame = step (ξ-blame {E = E-Cast c})
    progress (M ⟨ c ⟩)
        | done V
          with ActiveOrInert c
    ...   | inj₁ a = step (cast V {a})
    ...   | inj₂ i
            with V
    ...     | S-val sV = done (V-cast {i = i} sV)
    ...     | V-cast {c = c'} V' = step compose-casts

{-
    determinism : ∀{A} {M N N′ : ∅ ⊢ A} {ctx : ReductionCtx}
                → ctx / M —→ N
                → ctx / M —→ N′
                → N ≡ N′
    determinism (ξ R) R′ = {!!}
    determinism (ξ-cast R) R′ = {!!}
    determinism ξ-blame R′ = {!!}
    determinism ξ-cast-blame R′ = {!!}
    determinism (β x) R′ = {!!}
    determinism δ R′ = {!!}
    determinism β-if-true R′ = {!!}
    determinism β-if-false R′ = {!!}
    determinism (β-fst x x₁) R′ = {!!}
    determinism (β-snd x x₁) R′ = {!!}
    determinism (β-caseL x) R′ = {!!}
    determinism (β-caseR x) R′ = {!!}
    determinism (cast v) R′ = {!!}
    determinism (fun-cast v x) R′ = {!!}
    determinism (fst-cast v) R′ = {!!}
    determinism (snd-cast v) R′ = {!!}
    determinism (case-cast v) R′ = {!!}
    determinism compose-casts R′ = {!!}
            
-}
