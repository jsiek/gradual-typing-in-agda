open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Data.List hiding ([_])
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product
  using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Types
open import Labels
open import CastStructureWithPrecisionABT

open import Utils


module ParamGradualGuaranteeABT (csp : CastStructWithPrecision) where

open CastStructWithPrecision csp

open import ParamCastCalculusABT precast
open import ParamCastAuxABT precast
open import ParamCastReductionABT cs
open import ParamCCPrecisionABT pcsp
{- We've already proven the simlulation lemmas. -}
-- open import ParamGradualGuaranteeSim csp

{- Here is the statement of the gradual guarantee! -}
gradual-guarantee : ∀ {A A′} {M₁ M₁′ M₂′ : Term}
  → [] ⊢ M₁  ⦂ A
  → [] ⊢ M₁′ ⦂ A′
  → [] , [] ⊢ M₁ ⊑ M₁′
  → M₁′ —→ M₂′
    --------------------------------------------
  → ∃[ M₂ ] (M₁ —↠ M₂) × ([] , [] ⊢ M₂ ⊑ M₂′)

gradual-guarantee-plug : ∀ {A A′} {F : Frame} {M₁ M₂ M₁′ M₂′ : Term}
  → [] ⊢ M₁ ⦂ A
  → [] ⊢ plug M₁′ F ⦂ A′
  → [] , [] ⊢ M₁ ⊑ plug M₁′ F
  → M₁′ —→ M₂′
  → ∃[ M₂ ] (M₁ —↠ M₂) × [] , [] ⊢ M₂ ⊑ plug M₂′ F

gradual-guarantee-plug {F = F-·₁ M′} {L · M} (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· ⊢M₁′ _ 𝐶⊢-·) (⊑-· L⊑M₁′ M⊑M′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ R* , L₂⊑ ⟩ ⟩  → ⟨ L₂ · M , ⟨ plug-cong (F-·₁ M) R* , ⊑-· L₂⊑ M⊑M′ ⟩ ⟩
gradual-guarantee-plug {F = F-·₂ V x} ⊢M₁ ⊢plugN′F (⊑-· L⊑M₁′ M⊑M′) R = {!!}
gradual-guarantee-plug {F = F-if M N} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-×₁ V x} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-×₂ M} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-fst} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-snd} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-inl B} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-inr A} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-case A B M N} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-cast x} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F-wrap c x} ⊢M₁ ⊢plugN′F M₁⊑ R = {!!}
gradual-guarantee-plug {F = F} {M₁′ = M₁′} {M₂′}
  (⊢cast c ⊢M 𝐶⊢-cast) _ (⊑-castl {A′ = A′} A⊑A′ B⊑A′ ⊢M′ M⊑) R =
    case gradual-guarantee ⊢M ⊢M′ M⊑ (ξ R) of λ where
      ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
        ⟨ M₂ ⟨ c ⟩ , ⟨ plug-cong (F-cast c) R* ,
          ⊑-castl A⊑A′ B⊑A′ (preserve ⊢M′ (ξ R)) M₂⊑ ⟩ ⟩
gradual-guarantee-plug ⊢M₁ ⊢plugN′F (⊑-wrapl x x₁ M₁⊑) R = {!!}

gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (ξ {F = F} R) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ ξ-blame = ⟨ _ , ⟨ _ ∎ , ⊑-blame ⟩ ⟩
gradual-guarantee ⊢M₁ ⊢M₁′ (⊑-· M₁⊑ M₁⊑₁) (β w) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ δ = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ β-if-true = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ β-if-false = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-fst x x₁) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-snd x x₁) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-caseL x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-caseR x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (cast v) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (wrap v) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (fun-cast x x₁) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (fst-cast x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (snd-cast x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (case-cast x) = {!!}
gradual-guarantee (⊢cast c ⊢M 𝐶⊢-cast) _ (⊑-castl A⊑A′ B⊑A′ ⊢M′ M⊑) R =
  case gradual-guarantee ⊢M ⊢M′ M⊑ R of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ⟩ , ⟨ plug-cong (F-cast c) R* ,
        ⊑-castl A⊑A′ B⊑A′ (preserve ⊢M′ R) M₂⊑ ⟩ ⟩
gradual-guarantee ⊢M₁ ⊢M₁′ (⊑-wrapl lpit ⊢M′ M⊑) R = {!!}
