open import Data.Nat using (ℕ; zero; suc)
open import Data.List hiding ([_])
open import Data.Nat.Properties using (suc-injective)
open import Data.Bool
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
open import Syntax


module PrecisionSimulationABT (csp : CastStructWithPrecision) where

open CastStructWithPrecision csp

open import ParamCastCalculusABT precast
open import ParamCastAuxABT precast
open import ParamCastReductionABT cs
open import ParamCCPrecisionABT pcsp
open import PreservePrecisionABT pcsp

{- Catching up on the less precise side. -}
catchup : ∀ {Γ Γ′ A} {M V′ : Term}
  → Γ ⊢ M ⦂ A
  → Value V′
  → Γ , Γ′ ⊢ M ⊑ V′
    ----------------------------------------------
  → ∃[ V ] Value V × (M —↠ V) × Γ , Γ′ ⊢ V ⊑ V′
catchup ⊢M v′ ⊑-$ =
  ⟨ _  , ⟨ V-const , ⟨ _ ∎ , ⊑-$ ⟩ ⟩ ⟩
catchup ⊢M v′ (⊑-ƛ A⊑ N⊑) =
  ⟨ _ , ⟨ V-ƛ , ⟨ _ ∎ , ⊑-ƛ A⊑ N⊑ ⟩ ⟩ ⟩
catchup (⊢cons ⊢M₁ ⊢M₂ 𝐶⊢-cons) (V-pair v′₁ v′₂) (⊑-cons M₁⊑ M₂⊑) =
  case ⟨ catchup ⊢M₁ v′₁ M₁⊑ , catchup ⊢M₂ v′₂ M₂⊑ ⟩ of λ where
    ⟨ ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ₘ , Vₘ⊑ ⟩ ⟩ ⟩ , ⟨ Vₙ , ⟨ vₙ , ⟨ rd⋆ₙ , Vₙ⊑ ⟩ ⟩ ⟩ ⟩ →
      ⟨ ⟦ Vₘ , Vₙ ⟧ , ⟨ V-pair vₘ vₙ ,
        ⟨ ↠-trans (plug-cong (F-×₂ _) rd⋆ₘ) (plug-cong (F-×₁ _ vₘ) rd⋆ₙ) ,
          ⊑-cons Vₘ⊑ Vₙ⊑ ⟩ ⟩ ⟩
catchup (⊢inl B ⊢M 𝐶⊢-inl) (V-inl v′) (⊑-inl B⊑ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ , Vₘ⊑ ⟩ ⟩ ⟩ →
      ⟨ inl Vₘ other _ , ⟨ V-inl vₘ ,
        ⟨ plug-cong (F-inl _) rd⋆ , ⊑-inl B⊑ Vₘ⊑ ⟩ ⟩ ⟩
catchup (⊢inr A ⊢M 𝐶⊢-inr) (V-inr v′) (⊑-inr A⊑ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ Vₘ , ⟨ vₘ , ⟨ rd* , Vₘ⊑ ⟩ ⟩ ⟩ →
      ⟨ inr Vₘ other _ , ⟨ V-inr vₘ ,
        ⟨ plug-cong (F-inr _) rd* , ⊑-inr A⊑ Vₘ⊑ ⟩ ⟩ ⟩
catchup (⊢cast c ⊢M 𝐶⊢-cast) v′ (⊑-castl A⊑A′ B⊑A′ ⊢M′ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    -- M —↠ V
    ⟨ V , ⟨ v , ⟨ rd*₁ , V⊑ ⟩ ⟩ ⟩ →
      case ActiveOrInert c of λ where
        (inj₁ a) →
          case applyCast-catchup a (preserve-multi ⊢M rd*₁) ⊢M′ v v′ A⊑A′ B⊑A′ V⊑ of λ where
            ⟨ W , ⟨ w , ⟨ rd*₂ , W⊑ ⟩ ⟩ ⟩ →
              ⟨ W , ⟨ w ,
                ⟨ ↠-trans (plug-cong (F-cast c) rd*₁) (_ —→⟨ cast v ⟩ rd*₂) ,
                  W⊑ ⟩ ⟩ ⟩
        (inj₂ i) →
          ⟨ V ⟨ c ₍ i ₎⟩ , ⟨ V-wrap v i ,
            ⟨ ↠-trans (plug-cong (F-cast c) rd*₁) (_ —→⟨ wrap v ⟩ _ ∎) ,
              ⊑-wrapl (⊑→lpit i A⊑A′ B⊑A′) ⊢M′ V⊑ ⟩ ⟩ ⟩
-- just recur in all 3 wrap cases
catchup (⊢wrap c i ⊢M 𝐶⊢-wrap) (V-wrap v′ i′) (⊑-wrap lpii M⊑ imp) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W ⟨ c ₍ i ₎⟩ , ⟨ V-wrap w i ,
        ⟨ plug-cong (F-wrap _ _) rd* , ⊑-wrap lpii W⊑ imp ⟩ ⟩ ⟩
catchup (⊢wrap c i ⊢M 𝐶⊢-wrap) v′ (⊑-wrapl {c = c} {i = i} lpit ⊢M′ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W ⟨ c ₍ i ₎⟩ , ⟨ V-wrap w i ,
        ⟨ plug-cong (F-wrap _ _) rd* , ⊑-wrapl lpit ⊢M′ W⊑ ⟩ ⟩ ⟩
catchup ⊢M (V-wrap v′ i′) (⊑-wrapr lpti ⊢M₁ M⊑ nd) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W , ⟨ w , ⟨ rd* , ⊑-wrapr lpti (preserve-multi ⊢M₁ rd*) W⊑ nd ⟩ ⟩ ⟩


sim-β : ∀ {A A′ B B′} {V W N′ W′ : Term}
  → [] ⊢ V ⦂ A ⇒ B
  → [] ⊢ W ⦂ A
  → A′ ∷ [] ⊢ N′ ⦂ B′
  → [] ⊢ W′ ⦂ A′
  → Value V → Value W → Value W′
  → [] , [] ⊢ V ⊑ ƛ A′ ˙ N′
  → [] , [] ⊢ W ⊑ W′
    --------------------------------------------------
  → ∃[ M ] (V · W —↠ M) × ([] , [] ⊢ M ⊑ N′ [ W′ ])
sim-β {V = ƛ A ˙ N} {W} (⊢ƛ .A ⊢N 𝐶⊢-ƛ) ⊢W ⊢N′ ⊢W′ V-ƛ w w′ (⊑-ƛ A⊑ N⊑) W⊑ =
  ⟨ N [ W ] , ⟨ _ —→⟨ β w ⟩ _ ∎ , substitution-pres-⊑ ⊢N ⊢N′ ⊢W ⊢W′ N⊑ W⊑ ⟩ ⟩
sim-β (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢W ⊢N′ ⊢W′ (V-wrap v .i) w w′ V⊑ W′ = {!!}
