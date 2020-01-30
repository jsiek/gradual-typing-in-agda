open import Types
open import CastStructure
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

module EfficientParamCasts (ecs : EfficientCastStruct) where

  open EfficientCastStruct ecs

  import ParamCastCalculus
  open ParamCastCalculus Cast

  import EfficientParamCastAux
  open EfficientParamCastAux precast
  
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

  {-

   We parameterize the reduction relation according to whether 
   the reduction can take place in any context or whether 
   it can only take place in non-cast contexts, that is,
   the immediately enclosing term cannot be a cast.
   To prevent reducing under a pair of casts, the
   congruence rule for casts, ξ-cast, requires a non-cast context.
   Further, the inner reduction must be OK with any context.
   The congruence rule for all other language features, ξ,
   can fire in any context and the inner reduction can require
   either any context or non-cast contexts.
   The rule for composing two casts can fire in a non-cast context,
   which enforces an outside-in strategy for compressing sequences
   of casts.
   All other reduction rules can fire in any context.

   -}

  data ReductionCtx : Set where
    any_ctx : ReductionCtx
    non_cast_ctx : ReductionCtx

  infix 2 _/_—→_
  data _/_—→_ : ∀ {Γ A} → ReductionCtx → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    ξ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B} {ctx : ReductionCtx}
      → ctx / M —→ M′
        ---------------------------
      → any_ctx / plug M F —→ plug M′ F

    ξ-cast : ∀ {Γ A B} {c : Cast (A ⇒ B)} {M M′ : Γ ⊢ A}
      → any_ctx / M —→ M′
        --------------------------------------
      → non_cast_ctx / (M ⟨ c ⟩) —→ M′ ⟨ c ⟩

    ξ-blame : ∀ {Γ A B} {F : Frame {Γ} A B} {ℓ} 
        ---------------------------------
      → any_ctx / plug (blame ℓ) F —→ blame ℓ

    ξ-cast-blame : ∀ {Γ A B} {c : Cast (A ⇒ B)} {ℓ}
        ----------------------------------------------------
      → non_cast_ctx / ((blame {Γ}{A} ℓ) ⟨ c ⟩) —→ blame ℓ

    β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A} 
      → Value W
        -------------------------------
      → any_ctx / (ƛ N) · W —→ N [ W ]

    δ : ∀ {Γ}{A B}{f : rep A → rep B}{k : rep A}{ab}{a}{b}
        ---------------------------------------------------------
      → any_ctx / ($_ {Γ}{A ⇒ B} f {ab}) · (($ k){a}) —→ ($ (f k)){b}

    β-if-true : ∀{Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
        -------------------------------
      → any_ctx / if (($ true){f}) M N —→ M

    β-if-false : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
        ---------------------
      → any_ctx / if (($ false){f}) M N —→ N

    β-fst : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        --------------------
      → any_ctx / fst (cons V W) —→ V

    β-snd :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        --------------------
      → any_ctx / snd (cons V W) —→ W

    β-caseL : ∀ {Γ A B C} {V : Γ ⊢ A} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
      → Value V
        --------------------------
      → any_ctx / case (inl V) L M —→ L · V

    β-caseR : ∀ {Γ A B C} {V : Γ ⊢ B} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
      → Value V
        --------------------------
      → any_ctx / case (inr V) L M —→ M · V

    cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
      → (v : Value V) → {a : Active c}
        ----------------------------
      → non_cast_ctx / V ⟨ c ⟩ —→ applyCast V v c {a}

    fun-cast : ∀ {Γ A' B' A₁ A₂} {V : Γ ⊢ A₁ ⇒ A₂} {W : Γ ⊢ A'}
        {c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))} 
      → (v : SimpleValue V) → Value W → {x : Cross c}
        -------------------------------------------------------------
      → any_ctx / (V ⟨ c ⟩) · W —→ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩

    fst-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B} 
        {c : Cast ((A `× B) ⇒ (A' `× B'))} 
      → (v : SimpleValue V) → {x : Cross c}
        -----------------------------------------------
      → any_ctx / fst (V ⟨ c ⟩) —→ (fst V) ⟨ fstC c x ⟩

    snd-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
        {c : Cast ((A `× B) ⇒ (A' `× B'))} 
      → (v : SimpleValue V) → {x : Cross c}
        -----------------------------------------------
      → any_ctx / snd (V ⟨ c ⟩) —→ (snd V) ⟨ sndC c x ⟩

    case-cast : ∀ { Γ A B A' B' C} {V : Γ ⊢ A `⊎ B}
        {W₁ : Γ ⊢ A' ⇒ C } {W₂ : Γ ⊢ B' ⇒ C}
        {c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))} 
      → (v : SimpleValue V) → {x : Cross c}
        ---------------------------------------------------------
      → any_ctx / case (V ⟨ c ⟩) W₁ W₂ —→
                  case V (ƛ ((rename S_ W₁) · ((` Z) ⟨ inlC c x ⟩ )))
                         (ƛ ((rename S_ W₂) · ((` Z) ⟨ inrC c x ⟩ )))


    compose-casts : ∀{Γ A B C} {M : Γ ⊢ A }
        {c : Cast (A ⇒ B)} {d : Cast (B ⇒ C)} 
        ------------------------------------------
      → non_cast_ctx / (M ⟨ c ⟩) ⟨ d ⟩ —→ M ⟨ compose c d ⟩


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

  switch-back : ∀ {Γ A} {M M′ : Γ ⊢ A}
      → ¬ IsCast M
      → non_cast_ctx / M —→ M′
        ------------------
      → any_ctx / M —→ M′
  switch-back nc (ξ-cast R) = contradiction isCast nc
  switch-back nc ξ-cast-blame = contradiction isCast nc
  switch-back nc (cast v) = contradiction isCast nc
  switch-back nc compose-casts = contradiction isCast nc

  {-

  UPDATE ME

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
  ... | step R = step (ξ {F = F-·₁ M₂} R)
  ... | error E-blame = step (ξ-blame {A = A₁ ⇒ A}{F = F-·₁ M₂})
  progress {A} (M₁ · M₂) | done V₁
        with progress M₂
  ...   | step R = step (ξ {F = F-·₂ M₁ {V₁}} R)
  ...   | error E-blame = step (ξ-blame {F = F-·₂ M₁ {V₁}})
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
                    G (P-Fun f) ic = baseNotInert c ic
  progress {A} (M₁ · M₂) | done V₁ | done V₂
          | V-cast {V = V}{c}{i} v
            with Inert-Cross⇒ c i 
  ...       | ⟨ x , ⟨ B , ⟨ C , refl ⟩ ⟩ ⟩ = step (fun-cast v V₂ {x})
  progress ($ k) = done (S-val V-const)
  progress (if L M N)
      with progress L
  ... | step R = step (ξ {F = F-if M N} R)
  ... | error E-blame = step (ξ-blame {F = F-if M N})
  ... | done (S-val (V-const {k = true})) = step β-if-true
  ... | done (S-val (V-const {k = false})) = step β-if-false
  ... | done (V-cast {V = V}{c}{i} v) =
        contradiction i (baseNotInert c)
  progress (cons M₁ M₂)
      with progress M₁
  ... | step R = step (ξ {F = F-×₂ M₂} R)
  ... | error E-blame = step (ξ-blame {F = F-×₂ M₂})
  ... | done V with progress M₂
  ...    | step R = step (ξ {F = F-×₁ M₁} R)
  ...    | done V' = done (S-val (V-pair V V'))
  ...    | error E-blame = step (ξ-blame{F = F-×₁ M₁})
  progress (fst M)
      with progress M
  ... | step R = step (ξ {F = F-fst} R)
  ... | error E-blame = step (ξ-blame{F = F-fst})
  ... | done V
          with V
  ...     | S-val (V-pair {V = V₁}{W = V₂} v w) = step (β-fst v w)
  ...     | S-val (V-const {k = ()})
  ...     | V-cast {V = V'} {c = c} {i = i} v
            with Inert-Cross× c i
  ...       | ⟨ x , ⟨ B , ⟨ C , refl ⟩ ⟩ ⟩ = step (fst-cast {c = c} v {x})
  progress (snd M)
      with progress M
  ... | step R = step (ξ {F = F-snd} R)
  ... | error E-blame = step (ξ-blame{F = F-snd})
  ... | done V
          with V
  ...     | S-val (V-pair {V = V₁}{W = V₂} v w) = step (β-snd v w)
  ...     | S-val (V-const {k = ()})
  ...     | V-cast {V = V'}{c = c} {i = i} v
            with Inert-Cross× c i
  ...       | ⟨ x , ⟨ B , ⟨ C , refl ⟩ ⟩ ⟩ = step (snd-cast {c = c} v {x})
  progress (inl M)
      with progress M
  ... | step R = step (ξ {F = F-inl} R)
  ... | error E-blame = step (ξ-blame {F = F-inl})
  ... | done V = done (S-val (V-inl V))
  progress (inr M)
      with progress M
  ... | step R = step (ξ {F = F-inr} R)
  ... | error E-blame = step (ξ-blame {F = F-inr})
  ... | done V = done (S-val (V-inr V))
  progress (case L M N)
      with progress L
  ... | step R = step (ξ {F = F-case M N} R)
  ... | error E-blame = step (ξ-blame {F = F-case M N})
  ... | done V
         with V
  ...    | S-val (V-inl v) = step (β-caseL v)
  ...    | S-val (V-inr v) = step (β-caseR v)
  ...    | V-cast {V = V'} {c = c} {i = i} v 
             with Inert-Cross⊎ c i
  ...        | ⟨ x , ⟨ B , ⟨ C , refl ⟩ ⟩ ⟩ = step (case-cast {c = c} v {x})
  progress (blame ℓ) = error E-blame
  progress (M ⟨ c ⟩)
      with progress M
  ... | step {ctx = any_ctx} R = step (ξ-cast R)
  ... | step {ctx = non_cast_ctx} R
        with is-cast? M
  ...   | yes (isCast {M = M′}{c = d}) = step compose-casts
  ...   | no ncM = step (ξ-cast (switch-back ncM R))
  progress (M ⟨ c ⟩)
      | error E-blame = step ξ-cast-blame
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
