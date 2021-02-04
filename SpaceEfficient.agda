open import Types hiding (_⊔_)
open import CastStructure
import EfficientParamCasts
open import Data.Nat using (ℕ; _≤_; _⊔_)

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

  preserve-height : ∀ {Γ A} {M M′ : Γ ⊢ A} {ctx : ReductionCtx}
       → ctx / M —→ M′ → c-height M′ ≤ c-height M
  preserve-height (ξ M—→M′) = {!!}
  preserve-height (ξ-cast M—→M′) = {!!}
  preserve-height ξ-blame = {!!}
  preserve-height ξ-cast-blame = {!!}
  preserve-height (β x) = {!!}
  preserve-height δ = {!!}
  preserve-height β-if-true = {!!}
  preserve-height β-if-false = {!!}
  preserve-height (β-fst x x₁) = {!!}
  preserve-height (β-snd x x₁) = {!!}
  preserve-height (β-caseL x) = {!!}
  preserve-height (β-caseR x) = {!!}
  preserve-height (cast v) = {!!}
  preserve-height (fun-cast v x) = {!!}
  preserve-height (fst-cast v) = {!!}
  preserve-height (snd-cast v) = {!!}
  preserve-height (case-cast v) = {!!}
  preserve-height compose-casts = {!!}
