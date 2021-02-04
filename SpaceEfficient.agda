open import Types hiding (_⊔_)
open import Variables
open import CastStructure
import EfficientParamCasts
open import Data.Nat using (ℕ; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
open Data.Nat.Properties.≤-Reasoning

{-

  A proof that the Efficient Parameterized Cast Calculus
  is indeed space efficient.

-}

module SpaceEfficient (ecs : EfficientCastStruct) where

  open EfficientCastStruct ecs
  open EfficientParamCasts ecs

  import ParamCastCalculus
  open ParamCastCalculus Cast
  
  c-height : ∀{Γ A} (M : Γ ⊢ A) → ℕ
  c-height (` x) = 0
  c-height (ƛ M) = c-height M
  c-height (L · M) = c-height L ⊔ c-height M
  c-height ($ x) = 0
  c-height (if L M N) = c-height L ⊔ c-height M ⊔ c-height N
  c-height (cons M N) = c-height M ⊔ c-height N
  c-height (fst M) = c-height M
  c-height (snd M) = c-height M
  c-height (inl M) = c-height M
  c-height (inr M) = c-height M
  c-height (case L M N) = c-height L ⊔ c-height M ⊔ c-height N
  c-height (M ⟨ c ⟩) = c-height M ⊔ height c
  c-height (blame ℓ) = 0

  plug-height : ∀ {Γ A B} (M : Γ ⊢ A) (M′ : Γ ⊢ A) (F : Frame A B)
      → c-height M′ ≤ c-height M
      → c-height (plug M′ F) ≤ c-height (plug M F)
  plug-height M M′ F M′≤M  = {!!}

  subst-height : ∀ {Γ A B} (N : Γ , A ⊢ B) (W : Γ ⊢ A)
      → c-height (N [ W ]) ≤ c-height N ⊔ c-height W
  subst-height N W = {!!}

  preserve-height : ∀ {Γ A} {M M′ : Γ ⊢ A} {ctx : ReductionCtx}
       → ctx / M —→ M′ → c-height M′ ≤ c-height M
  preserve-height (ξ {M = M₁}{M₁′}{F} M₁—→M₁′) =
    let IH = preserve-height M₁—→M₁′ in plug-height M₁ M₁′ F IH
  preserve-height (ξ-cast {M = M₁}{M₁′} M₁—→M₁′) =
    let IH = preserve-height M₁—→M₁′ in ⊔-mono-≤ IH ≤-refl
  preserve-height ξ-blame = z≤n
  preserve-height ξ-cast-blame = z≤n
  preserve-height (β{N = N}{W = W} vW) = subst-height N W
  preserve-height δ = z≤n
  preserve-height β-if-true = m≤m⊔n _ _
  preserve-height β-if-false = n≤m⊔n _ _
  preserve-height (β-fst vV vW) = m≤m⊔n _ _
  preserve-height (β-snd vV vW) = n≤m⊔n _ _
  preserve-height (β-caseL {V = V}{L}{M} vV) =
    begin
      c-height L ⊔ c-height V               ≤⟨ ≤-reflexive (⊔-comm _ _) ⟩ 
      c-height V ⊔ c-height L               ≤⟨ {!!} ⟩ 
      c-height V ⊔ c-height L ⊔ c-height M
    ∎ 
    
  preserve-height (β-caseR vV) = {!!}
  preserve-height (cast v) = {!!}
  preserve-height (fun-cast v x) = {!!}
  preserve-height (fst-cast v) = {!!}
  preserve-height (snd-cast v) = {!!}
  preserve-height (case-cast v) = {!!}
  preserve-height compose-casts = {!!}
