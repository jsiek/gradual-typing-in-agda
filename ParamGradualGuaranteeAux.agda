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
open import Variables
open import Labels
open import PreCastStructureWithPrecision

module ParamGradualGuaranteeAux (pcsp : PreCastStructWithPrecision) where

open PreCastStructWithPrecision pcsp

open import ParamCastCalculus Cast Inert
open import ParamCastAux precast
open import ParamCCPrecision pcsp

{- Various inversion lemmas about `wrap` being on either or both sides. -}
value-⊑-wrap-inv : ∀ {A′} {V : ∅ ⊢ ⋆} {V′ : ∅ ⊢ A′} {c′ : Cast (A′ ⇒ ⋆)} {i′ : Inert c′}
  → Value V → Value (V′ ⟪ i′ ⟫)
  → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
    -----------------------
  → ∅ , ∅ ⊢ V ⊑ᶜ V′
value-⊑-wrap-inv v (V-wrap v′ i′) (⊑ᶜ-wrap lpii lpW)
  with lpii→⊑ lpii
... | ⟨ lp , unk⊑ ⟩ = ⊑ᶜ-wrapl (⊑→lpit _ lp unk⊑) lpW
value-⊑-wrap-inv (V-wrap v i) (V-wrap v′ i′) (⊑ᶜ-wrapl lpit lpV)
  with lpit→⊑ lpit
... | ⟨ unk⊑ , unk⊑ ⟩ = contradiction i (idNotInert A-Unk _)
value-⊑-wrap-inv v (V-wrap v′ i′) (⊑ᶜ-wrapr lpti lpV A≢⋆) = ⊥-elim (A≢⋆ refl) {- contradiction lpti (⋆-⋢-inert _) -}

wrap-⊑-value-inv : ∀ {A A′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ ⋆)} {i : Inert c}
  → A′ ≢ ⋆
  → Value (V ⟪ i ⟫) → Value V′
  → ∅ , ∅ ⊢ V ⟪ i ⟫ ⊑ᶜ V′
    ----------------------
  → ∅ , ∅ ⊢ V ⊑ᶜ V′
wrap-⊑-value-inv nd v w (⊑ᶜ-wrap lpii lpV) with inj-⊑-inj _ _ lpii
... | ⟨ refl , refl ⟩ = contradiction refl nd
wrap-⊑-value-inv nd v w (⊑ᶜ-wrapl _ lpV) = lpV
wrap-⊑-value-inv nd v w (⊑ᶜ-wrapr lpti lpV A≢⋆) = ⊥-elim (A≢⋆ refl) {- contradiction lpti (⋆-⋢-inert _) -}

wrap-⊑-wrap-inv : ∀ {A A′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ ⋆)} {c′ : Cast (A′ ⇒ ⋆)}
                    {i : Inert c} {i′ : Inert c′}
  → Value (V ⟪ i ⟫) → Value (V′ ⟪ i′ ⟫)
  → ∅ , ∅ ⊢ V ⟪ i ⟫ ⊑ᶜ V′ ⟪ i′ ⟫
    -----------------------------
  → ∅ , ∅ ⊢ V ⊑ᶜ V′
wrap-⊑-wrap-inv (V-wrap v i) (V-wrap v′ i′) (⊑ᶜ-wrap _ lpV) = lpV
wrap-⊑-wrap-inv (V-wrap v i) (V-wrap v′ i′) (⊑ᶜ-wrapl lpit lpV)
  with lpit→⊑ lpit
... | ⟨ unk⊑ , unk⊑ ⟩ = contradiction i (idNotInert A-Unk _)
wrap-⊑-wrap-inv (V-wrap v i) (V-wrap v′ i′) (⊑ᶜ-wrapr lpti lpV A≢⋆) = ⊥-elim (A≢⋆ refl) {- contradiction lpti (⋆-⋢-inert _) -}
