{-# OPTIONS --rewriting #-}
module PolyBlame.Gradual where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Data.Sum using (_⊎_)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)

open import PolyBlame.Types
open import PolyBlame.Variables

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

infix  5 ƛ_
infixl 7 _·_
infixl 7 _◯_
infix  9 `_
infix  9 #_

{----------- Well-Typed Terms ---------------------------------}

infix 4 _⊢_⏵_
data _⊢_⏵_ : (Δ : TyCtx) → Type Δ → Type Δ → Set where
  ⏵-⇒-⇒ : ∀{Δ A B} → Δ ⊢ (A ⇒ B) ⏵ (A ⇒ B)
  ⏵-★-⇒ : ∀{Δ} → Δ ⊢ ★ ⏵ (★ ⇒ ★)
  ⏵-∀-∀ : ∀{Δ A} → Δ ⊢ (`∀ A) ⏵ (`∀ A)
  ⏵-A-∀ : ∀{Δ A}
      → (∀ B → A ≢ `∀ B)
      → Δ ⊢ A ⏵ (`∀ (⇑ᵗ A))

infix 4 _∣_⊢ᵍ_
data _∣_⊢ᵍ_ : (Δ : TyCtx) → Ctx Δ → Type Δ → Set
  where
  `_ : ∀{Δ Γ A}
     → Γ ∋ A
       ---------
     → Δ ∣ Γ ⊢ᵍ A
     
  #_ : ∀{Δ Γ}
     → ℕ
       -----------
     → Δ ∣ Γ ⊢ᵍ `ℕ
     
  ƛ_ : ∀{Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → Δ ∣ (Γ ▷ A) ⊢ᵍ B
       --------------------
     → Δ ∣ Γ ⊢ᵍ A ⇒ B
     
  _·_ : ∀{Δ}{Γ : Ctx Δ}{A B C D : Type Δ}
     → Δ ∣ Γ ⊢ᵍ A
     → Δ ∣ Γ ⊢ᵍ B
     → Δ ⊢ A ⏵ C ⇒ D
     → Δ ∣ mt Δ ⊢ B ∼ C
       -----------------
     → Δ ∣ Γ ⊢ᵍ D
     
  Λ_ : ∀{Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
     → (Δ ,typ) ∣ ⟰ Γ ⊢ᵍ A
       --------------------------
     → Δ ∣ Γ ⊢ᵍ `∀ A
     
  _◯_ : ∀{Δ}{Γ : Ctx Δ}{A : Type Δ}{B : Type (Δ ,typ)}
     → Δ ∣ Γ ⊢ᵍ A
     → Δ ⊢ A ⏵ `∀ B
     → (C : Type Δ)
       --------------------
     → Δ ∣ Γ ⊢ᵍ B [ C ]ˢ
     

