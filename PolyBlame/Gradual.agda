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
open import Agda.Builtin.Bool

open import PolyBlame.Types
open import PolyBlame.TypeSubst
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
     → (C : Type Δ)
     → Δ ⊢ A ⏵ `∀ B
       --------------------
     → Δ ∣ Γ ⊢ᵍ B [ C ]ˢ
     

postulate
  subˢ-prec : ∀{Δ}{A B : Type (Δ ,typ)}{C C′ : Type Δ}
    → (Δ ,typ) ∣ mt Δ , false ⊢ A ⊑ B
    → Δ ∣ mt Δ ⊢ C ⊑ C′
    → Δ ∣ mt Δ ⊢ A [ C ]ˢ ⊑ (B [ C′ ]ˢ)

postulate
  ⏵∀-⊑ : ∀{Δ}{A A′ : Type Δ}{B B′ : Type (Δ ,typ)}
       → Δ ⊢ A ⏵ (`∀ B)
       → Δ ⊢ A′ ⏵ (`∀ B′)
       → Δ ∣ mt Δ ⊢ A ⊑ A′
       → (Δ ,typ) ∣ (mt Δ , false) ⊢ B ⊑ B′


infix 3 _∣_⊢ᵍ_⊑_⦂_
data _∣_⊢ᵍ_⊑_⦂_ : ∀(Δ : TyCtx){A B : Type Δ}{Γ Γ′ : Ctx Δ}
  → PrecCtx Γ Γ′ → (Δ ∣ Γ ⊢ᵍ A) → (Δ ∣ Γ′ ⊢ᵍ B)
  → Δ ∣ mt Δ ⊢ A ⊑ B → Set  where

  ⊑-var : ∀{Δ}{A B}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
     → (x : ⊢ Φ ∋ A ⊑ B)
       ---------------------------------------------------------
     → Δ ∣ Φ ⊢ᵍ (` proj-left x) ⊑ (` proj-right x) ⦂ get-⊑ x

  ⊑-nat : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{k : ℕ}
     → Δ ∣ Φ ⊢ᵍ (# k) ⊑ (# k) ⦂ ℕ⊑ℕ

  ⊑-lam : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
      {A B C D : Type Δ}{N : Δ ∣ (Γ ▷ A) ⊢ᵍ B} {N′ : Δ ∣ (Γ′ ▷ C) ⊢ᵍ D}
      {c : Δ ∣ mt Δ ⊢ A ⊑ C}{d : Δ ∣ mt Δ ⊢ B ⊑ D}
     → Δ ∣ (Φ , c) ⊢ᵍ N ⊑ N′ ⦂ d
       ---------------------------------
     → Δ ∣ Φ ⊢ᵍ ƛ N ⊑ ƛ N′ ⦂ ⇒⊑⇒ c d
  
  ⊑-app : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
       {A B A′ B′ C D C′ D′ : Type Δ}
       {L : Δ ∣ Γ ⊢ᵍ A}    {M : Δ ∣ Γ ⊢ᵍ B}
       {L′ : Δ ∣ Γ′ ⊢ᵍ A′}  {M′ : Δ ∣ Γ′ ⊢ᵍ B′}
       {a : Δ ∣ mt Δ ⊢ A ⊑ A′}
       {b : Δ ∣ mt Δ ⊢ B ⊑ B′}
       {d : Δ ∣ mt Δ ⊢ D ⊑ D′}
       {f : Δ ⊢ A ⏵ C ⇒ D}
       {bc : Δ ∣ mt Δ ⊢ B ∼ C}
       {f′ : Δ ⊢ A′ ⏵ C′ ⇒ D′}
       {bc′ : Δ ∣ mt Δ ⊢ B′ ∼ C′}
     → Δ ∣ Φ ⊢ᵍ L ⊑ L′ ⦂ a
     → Δ ∣ Φ ⊢ᵍ M ⊑ M′ ⦂ b
       --------------------------------------------
     → Δ ∣ Φ ⊢ᵍ (L · M) f bc ⊑ (L′ · M′) f′ bc′ ⦂ d

  ⊑-Λ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
       {A A′ : Type (Δ ,typ)}
       {N : Δ ,typ ∣ ⟰ Γ ⊢ᵍ A}
       {N′ : Δ ,typ ∣ ⟰ Γ′ ⊢ᵍ A′}
       {a : (Δ ,typ) ∣ mt (Δ ,typ) ⊢ A ⊑ A′}
    → Δ ,typ ∣ ⟰ᵖ Φ ⊢ᵍ N ⊑ N′ ⦂ a
     --------------------------------
    → Δ ∣ Φ ⊢ᵍ (Λ N) ⊑ (Λ N′) ⦂ ∀⊑∀ a

  ⊑-◯ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
       {A A′ C C′ : Type Δ}
       {B B′ : Type (Δ ,typ)}
       {M : Δ ∣ Γ ⊢ᵍ A}
       {M′ : Δ ∣ Γ′ ⊢ᵍ A′}
       {c : Δ ⊢ A ⏵ `∀ B}
       {c′ : Δ ⊢ A′ ⏵ `∀ B′}
       {a : Δ ∣ mt Δ ⊢ A ⊑ A′}
       {cc : Δ ∣ mt Δ ⊢ C ⊑ C′}
    → Δ ∣ Φ ⊢ᵍ M ⊑ M′ ⦂ a
     ---------------------------------------
    → Δ ∣ Φ ⊢ᵍ (M ◯ C) c ⊑ (M′ ◯ C′) c′ ⦂ subˢ-prec (⏵∀-⊑ c c′ a) cc

    
