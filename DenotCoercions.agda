module DenotCoercions where

open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Types hiding (_⊔_)
open import GroundCoercions renaming (Value to SValue)

open import ValueConst
open import GraphModel
open import Primitives hiding  (_⇒_)
import Labels

blame! : Label → Value
blame! ℓ = const {Blame} ℓ

cvt-label : Labels.Label → Label
cvt-label (Labels.pos n) = label n
cvt-label (Labels.neg n) = label n

cvt-base : Types.Base → Primitives.Base
cvt-base Nat = Nat
cvt-base Int = Int
cvt-base 𝔹 = 𝔹
cvt-base Unit = Unit
cvt-base ⊥ = Void
cvt-base Blame = Blame

𝐵 : Types.Base → Value → Labels.Label → Value
𝐵 b ⊥ ℓ = ⊥  {- ??? -}
𝐵 b (const {b'} k) ℓ
    with Primitives.base-eq? (cvt-base b) b'
... | yes eq = const {b'} k
... | no neq = blame! (cvt-label ℓ)
𝐵 b (v ↦ w) ℓ = blame! (cvt-label ℓ)
𝐵 b (u ⊔ v) ℓ = (𝐵 b u ℓ) ⊔ (𝐵 b v ℓ)

𝐶 : ∀ {A B} → Cast (A ⇒ B) → Value → Value
𝐶 id v = v
𝐶 (inj _) v = v
𝐶 (proj (` b) ℓ {G-Base}) v = 𝐵 b v ℓ
𝐶 (proj (⋆ ⇒ ⋆) ℓ {G-Fun}) v = {!!}
𝐶 (proj (⋆ `× ⋆) ℓ {G-Pair}) v = {!!}
𝐶 (proj (⋆ `⊎ ⋆) ℓ {G-Sum}) v = {!!}
𝐶 (cfun c₁ c₂) ⊥ = ⊥
𝐶 (cfun c₁ c₂) (const k) = ⊥ {- Can't happen... -}
𝐶 (cfun c₁ c₂) (v ↦ w) = (𝐶 c₁ v) ↦ (𝐶 c₂ w)
𝐶 (cfun c₁ c₂) (u ⊔ v) = (𝐶 (cfun c₁ c₂) u) ⊔ (𝐶 (cfun c₁ c₂) v)
𝐶 (cpair c₁ c₂) v = {!!}
𝐶 (csum c₁ c₂) v = {!!}
𝐶 (cseq c₁ c₂) v = 𝐶 c₂ (𝐶 c₁ v)

{- Semantics of Coercions,  𝒞 = \McC -}
𝒞 : ∀ {A B} → Cast (A ⇒ B) → 𝒫 Value → 𝒫 Value
𝒞 c d v = Σ[ u ∈ Value ] d u × v ≡ 𝐶 c u

