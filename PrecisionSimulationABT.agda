open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Types
open import Labels
open import CastStructureWithPrecisionABT

open import Utils
open import Syntax


module PrecisionSimulationABT (csp : CastStructWithPrecision) where

open CastStructWithPrecision csp

open import ParamCastCalculusABT precast
open import ParamCastAuxABT precast
open import ParamCastReductionABT cs
open import ParamCCPrecisionABT pcsp

{- Catching up on the less precise side. -}
catchup : ∀ {Γ Γ′} {M V′ : Term}
  → Value V′
  → Γ , Γ′ ⊢ M ⊑ V′
    -----------------------------------------------------
  → ∃[ V ] Value V × (M —↠ V) × Γ , Γ′ ⊢ V ⊑ V′
catchup v′ ⊑-$ =
  ⟨ _  , ⟨ V-const , ⟨ _ ∎ , ⊑-$ ⟩ ⟩ ⟩
catchup v′ (⊑-ƛ A⊑ N⊑) =
  ⟨ _ , ⟨ V-ƛ , ⟨ _ ∎ , ⊑-ƛ A⊑ N⊑ ⟩ ⟩ ⟩
catchup (V-pair v′₁ v′₂) (⊑-cons M₁⊑ M₂⊑) =
  case ⟨ catchup v′₁ M₁⊑ , catchup v′₂ M₂⊑ ⟩ of λ where
    ⟨ ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ₘ , Vₘ⊑ ⟩ ⟩ ⟩ , ⟨ Vₙ , ⟨ vₙ , ⟨ rd⋆ₙ , Vₙ⊑ ⟩ ⟩ ⟩ ⟩ →
      ⟨ ⟦ Vₘ , Vₙ ⟧ , ⟨ V-pair vₘ vₙ ,
        ⟨ ↠-trans (plug-cong (F-×₂ _) rd⋆ₘ) (plug-cong (F-×₁ _ vₘ) rd⋆ₙ) ,
          ⊑-cons Vₘ⊑ Vₙ⊑ ⟩ ⟩ ⟩
catchup (V-inl v′) (⊑-inl B⊑ M⊑)
  with catchup v′ M⊑
... | ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ , Vₘ⊑ ⟩ ⟩ ⟩ =
  ⟨ inl Vₘ other _ , ⟨ V-inl vₘ , ⟨ plug-cong (F-inl _) rd⋆ , ⊑-inl B⊑ Vₘ⊑ ⟩ ⟩ ⟩
catchup (V-inr v′) (⊑-inr A⊑ M⊑)
  with catchup v′ M⊑
... | ⟨ Vₘ , ⟨ vₘ , ⟨ rd* , Vₘ⊑ ⟩ ⟩ ⟩ =
  ⟨ inr Vₘ other _ , ⟨ V-inr vₘ , ⟨ plug-cong (F-inr _) rd* , ⊑-inr A⊑ Vₘ⊑ ⟩ ⟩ ⟩
catchup v′ (⊑-castl {c = c} A⊑A′ B⊑A′ ⊢M′ M⊑) = {!!}
--   with catchup v′ lpM
-- ... | ⟨ V , ⟨ vV , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
--   -- this is the more involved case so we prove it in a separate lemma
--   with cast-catchup {c = c} vV v′ lp1 lp2 lpV
-- ...   | ⟨ W , ⟨ vW , ⟨ rd*₂ , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ ↠-trans (plug-cong (F-cast _) rd*₁) rd*₂ , lpW ⟩ ⟩ ⟩
-- just recur in all 3 wrap cases
catchup (V-wrap v′ i′) (⊑-wrap {c = c} {i = i} lpii M⊑ imp)
  with catchup v′ M⊑
... | ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ =
  ⟨ W ⟨ c ₍ i ₎⟩ , ⟨ V-wrap w i , ⟨ plug-cong (F-wrap _ _) rd* , ⊑-wrap lpii W⊑ imp ⟩ ⟩ ⟩
catchup v′ (⊑-wrapl {c = c} {i = i} lpit ⊢M′ M⊑)
  with catchup v′ M⊑
... | ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ =
  ⟨ W ⟨ c ₍ i ₎⟩ , ⟨ V-wrap w i , ⟨ plug-cong (F-wrap _ _) rd* , ⊑-wrapl lpit ⊢M′ W⊑ ⟩ ⟩ ⟩
catchup (V-wrap v′ i′) (⊑-wrapr lpti ⊢M₁ M⊑ nd)
  with catchup v′ M⊑
... | ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ =
  ⟨ W , ⟨ w , ⟨ rd* , ⊑-wrapr lpti (preserve-multi ⊢M₁ rd*) W⊑ nd ⟩ ⟩ ⟩
