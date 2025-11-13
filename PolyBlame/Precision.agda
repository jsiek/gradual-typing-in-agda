{-# OPTIONS --rewriting #-}

module PolyBlame.Precision where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.List.Properties using (map-∘)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Data.Fin
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Bool

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import PolyBlame.Types

data SubCtx : (Δ : TyCtx) → Set where
  ∅ : SubCtx ∅
  _,_ : ∀{Δ} → SubCtx Δ → Bool → SubCtx (Δ ,typ)

data _∋_ : ∀{Δ} → SubCtx Δ → TyVar Δ → Set where
  Zˢ : ∀{Δ}{Ψ : SubCtx Δ} → (Ψ , true) ∋ Zᵗ
  Sˢ : ∀{Δ}{Ψ : SubCtx Δ}{b}{x}
     → Ψ ∋ x
     → (Ψ , b) ∋ Sᵗ x

infixr 6 _∣_⊢_⊑_
data _∣_⊢_⊑_ : (Δ : TyCtx) → SubCtx Δ → Type Δ → Type Δ → Set where
  ℕ⊑ : ∀{Δ}{Ψ}
      ------------------
     → Δ ∣ Ψ ⊢ `ℕ ⊑ `ℕ
     
  X⊑X : ∀{Δ}{Ψ}{X}
      --------------------
     → Δ ∣ Ψ ⊢ ` X ⊑ ` X

  ★⊑★ : ∀{Δ}{Ψ}
      ----------------
     → Δ ∣ Ψ ⊢ ★ ⊑ ★

  ★⊑X : ∀{Δ}{Ψ}{X : TyVar Δ}
     → Ψ ∋ X
      --------------------
     → Δ ∣ Ψ ⊢ ★ ⊑ ` X

  ★⊑ℕ : ∀{Δ}{Ψ}
     --------------------
     → Δ ∣ Ψ ⊢ ★ ⊑ `ℕ

  ★⊑⇒ : ∀{Δ}{Ψ}{A B}
     → Δ ∣ Ψ ⊢ ★ ⊑ A
     → Δ ∣ Ψ ⊢ ★ ⊑ B
       ------------------
     → Δ ∣ Ψ ⊢ ★ ⊑ A ⇒ B
  
  ⇒⊑⇒ : ∀{Δ}{Ψ}{A B C D}
     →  Δ ∣ Ψ ⊢ A ⊑ C
     →  Δ ∣ Ψ ⊢ B ⊑ D
      ------------------------
     → Δ ∣ Ψ ⊢ A ⇒ B ⊑ C ⇒ D

  ∀⊑∀ : ∀{Δ}{Ψ}{A B}
     → (Δ ,typ) ∣ (Ψ , false) ⊢ A ⊑ B
      --------------------------------
     → Δ ∣ Ψ ⊢ `∀ A ⊑ `∀ B

  ⊑∀ : ∀{Δ}{Ψ}{A B}
     → (Δ ,typ) ∣ (Ψ , true) ⊢ ⇑ᵗ A ⊑ B
      ----------------------------------
     → Δ ∣ Ψ ⊢ A ⊑ `∀ B

