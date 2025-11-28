{-# OPTIONS --rewriting #-}

module PolyBlame.ConsistentSubtyping where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.List.Properties using (map-∘)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (_∨_; _≤_)
open import Data.Bool.Properties
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Bool
open import Relation.Nullary using (¬_)

import Relation.Binary.PropositionalEquality as Eq
--open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import PolyBlame.Types
open import PolyBlame.TypePrecision

{-- Consistent Subtyping --}

infixr 6 _∣_⊢_≲_
data _∣_⊢_≲_ : (Δ : TyCtx) → BindCtx Δ → Type Δ → Type Δ → Set where
  ℕ≲ℕ : ∀{Δ}{Σ}
      ------------------
     → Δ ∣ Σ ⊢ `ℕ ≲ `ℕ
     
  X≲X : ∀{Δ}{Σ}{X}
      --------------------
     → Δ ∣ Σ ⊢ ` X ≲ ` X

  ★≲★ : ∀{Δ}{Σ}
      ----------------
     → Δ ∣ Σ ⊢ ★ ≲ ★

  ★≲X : ∀{Δ}{Σ}{X : TyVar Δ}
     → Σ ∋ X := ★
      ------------------
     → Δ ∣ Σ ⊢ ★ ≲ ` X

  X≲★ : ∀{Δ}{Σ}{X : TyVar Δ}
     → Σ ∋ X := ★
      -----------------
     → Δ ∣ Σ ⊢ ` X ≲ ★

  ★≲ℕ : ∀{Δ}{Σ}
     --------------------
     → Δ ∣ Σ ⊢ ★ ≲ `ℕ

  ℕ≲★ : ∀{Δ}{Σ}
     ------------------
     → Δ ∣ Σ ⊢ `ℕ ≲ ★

  ⇒≲★ : ∀{Δ}{Σ}{A B}
     → Δ ∣ Σ ⊢ ★ ≲ A
     → Δ ∣ Σ ⊢ B ≲ ★
       ------------------
     → Δ ∣ Σ ⊢ A ⇒ B ≲ ★

  ★≲⇒ : ∀{Δ}{Σ}{A B}
     → Δ ∣ Σ ⊢ A ≲ ★
     → Δ ∣ Σ ⊢ ★ ≲ B
       ------------------
     → Δ ∣ Σ ⊢ ★ ≲ A ⇒ B

  ⇒≲⇒ : ∀{Δ}{Σ}{A B C D}
     →  Δ ∣ Σ ⊢ C ≲ A
     →  Δ ∣ Σ ⊢ B ≲ D
      ------------------------
     → Δ ∣ Σ ⊢ A ⇒ B ≲ C ⇒ D

  ∀≲∀ : ∀{Δ}{Σ}{A B}
     → (Δ ,typ) ∣ (⤊ Σ) ⊢ A ≲ B
      --------------------------------
     → Δ ∣ Σ ⊢ `∀ A ≲ `∀ B

  ≲∀ : ∀{Δ}{Σ}{A B}
     → (Δ ,typ) ∣ (⤊ Σ) ⊢ ⇑ᵗ A ≲ B
      -----------------------------
     → Δ ∣ Σ ⊢ A ≲ `∀ B

  ∀≲ : ∀{Δ}{Σ}{A B}
     → (Δ ,typ) ∣ ((Zᵗ , ★) ∷ ⤊ Σ) ⊢ A ≲ ⇑ᵗ B
      ----------------------------------------
     → Δ ∣ Σ ⊢ `∀ A ≲ B

