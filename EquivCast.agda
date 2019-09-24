open import Types
open import CastStructure

open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)

module EquivCast
  (CastCalc₁ : CastStruct)
  (CastCalc₂ : CastStruct)
  where

  module CC₁ = CastCalc CastCalc₁
  module CC₂ = CastCalc CastCalc₂
  open CC₁ using (`_; _·_) renaming (_⊢_ to _⊢₁_; ƛ_ to ƛ₁_)
  open CC₂ using ()
     renaming (_⊢_ to _⊢₂_; `_ to ``_; ƛ_ to ƛ₂_; _·_ to _●_)

  data _≈_ : ∀{Γ A} → Γ ⊢₁ A → Γ ⊢₂ A → Set where
    ≈-var : ∀ {Γ}{A}{x : Γ ∋ A} → (` x) ≈ (`` x)
    ≈-lam : ∀ {Γ}{A B}{M₁ : Γ , A ⊢₁ B}{M₂ : Γ , A ⊢₂ B}
          → M₁ ≈ M₂ → (ƛ₁ M₁) ≈ (ƛ₂ M₂)
    ≈-app : ∀ {Γ}{A B}{L₁ : Γ ⊢₁ A ⇒ B}{L₂ : Γ ⊢₂ A ⇒ B}
              {M₁ : Γ ⊢₁ A}{M₂ : Γ ⊢₂ A}
          → L₁ ≈ L₂ → M₁ ≈ M₂ → (L₁ · M₁) ≈ (L₂ ● M₂)
