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
--open import Data.Fin
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Bool

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import PolyBlame.Types
open import PolyBlame.Terms

data SubCtx : (Δ : TyCtx) → Set where
  ∅ : SubCtx ∅
  _,_ : ∀{Δ} → SubCtx Δ → Bool → SubCtx (Δ ,typ)

mt : (Δ : TyCtx) → SubCtx Δ
mt ∅ = ∅
mt (Δ ,typ) = (mt Δ) , false

data _∋ˢ_ : ∀{Δ} → SubCtx Δ → TyVar Δ → Set where
  Zˢ : ∀{Δ}{Ψ : SubCtx Δ} → (Ψ , true) ∋ˢ Zᵗ
  Sˢ : ∀{Δ}{Ψ : SubCtx Δ}{b}{x}
     → Ψ ∋ˢ x
     → (Ψ , b) ∋ˢ Sᵗ x

infixr 6 _∣_⊢_⊑_
data _∣_⊢_⊑_ : (Δ : TyCtx) → SubCtx Δ → Type Δ → Type Δ → Set where
  ℕ⊑ℕ : ∀{Δ}{Ψ}
      ------------------
     → Δ ∣ Ψ ⊢ `ℕ ⊑ `ℕ
     
  X⊑X : ∀{Δ}{Ψ}{X}
      --------------------
     → Δ ∣ Ψ ⊢ ` X ⊑ ` X

  ★⊑★ : ∀{Δ}{Ψ}
      ----------------
     → Δ ∣ Ψ ⊢ ★ ⊑ ★

  ★⊑X : ∀{Δ}{Ψ}{X : TyVar Δ}
     → Ψ ∋ˢ X
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

Refl⊑ : ∀{Δ}{Ψ : SubCtx Δ} → (A : Type Δ) → Δ ∣ Ψ ⊢ A ⊑ A
Refl⊑ {Δ} {Ψ} `ℕ = ℕ⊑ℕ
Refl⊑ {Δ} {Ψ} ★ = ★⊑★
Refl⊑ {Δ} {Ψ} (` X) = X⊑X
Refl⊑ {Δ} {Ψ} (A ⇒ B) = ⇒⊑⇒ (Refl⊑ A) (Refl⊑ B)
Refl⊑ {Δ} {Ψ} (`∀ A) = ∀⊑∀ (Refl⊑ A)

-- ren-⊑ : ∀{Δ₁ Δ₂}{Ψ : SubCtx Δ₁}{A B : Type Δ₁}
--   → (ρ : Δ₁ ⇒ᵗ Δ₂)
--   → Δ₁ ∣ Ψ ⊢ A ⊑ B
--   → Δ₂ ∣ ren-sub-ctx ρ Ψ ⊢ ren-type ρ A ⊑ ren-type ρ B 
-- ren-⊑ ρ A⊑B = ?

data PrecCtx : ∀{Δ}(Γ Γ′ : Ctx Δ) → Set where
  ∅ : PrecCtx{∅} ∅ ∅
  _,_ : ∀{Δ}{Γ Γ′ : Ctx Δ}{A B : Type Δ}
        → PrecCtx Γ Γ′
        → Δ ∣ mt Δ ⊢ A ⊑ B
          ------------------------
        → PrecCtx (Γ ▷ A) (Γ′ ▷ B)

data _∋_⊑_ : ∀{Δ}{Γ Γ′ : Ctx Δ} → PrecCtx Γ Γ′ → Type Δ → Type Δ → Set where

  Zᵖ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B : Type Δ}
      {p : Δ ∣ mt Δ ⊢ A ⊑ B}
      ----------------------
    → (Φ , p) ∋ A ⊑ B
    
  Sᵖ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B C D : Type Δ}
      {p : Δ ∣ mt Δ ⊢ C ⊑ D}
    → Φ ∋ A ⊑ B
      -------------------
    → (Φ , p) ∋ A ⊑ B

get-⊑ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B : Type Δ}
  → (x : Φ ∋ A ⊑ B) → Δ ∣ mt Δ ⊢ A ⊑ B
get-⊑ (Zᵖ{p = p}) = p
get-⊑ (Sᵖ x) = get-⊑ x

proj-left : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B : Type Δ}
  → (x : Φ ∋ A ⊑ B) → Γ ∋ A
proj-left Zᵖ = Z
proj-left (Sᵖ x) = S proj-left x

proj-right : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B : Type Δ}
  → (x : Φ ∋ A ⊑ B) → Γ′ ∋ B
proj-right Zᵖ = Z
proj-right (Sᵖ x) = S proj-right x

postulate
  ⟰ᵖ : ∀ {Δ}{Γ Γ′ : Ctx Δ}
    → PrecCtx Γ Γ′
    → PrecCtx (⟰ Γ) (⟰ Γ′)
--⟰ᵖ Φ = {!!}

postulate
  subᵗ-prec : ∀{Δ}{A B : Type (Δ ,typ)}{X}
    → (Δ ,typ) ∣ mt Δ , false ⊢ A ⊑ B
    → Δ ∣ mt Δ ⊢ A [ X ]ᵗ ⊑ (B [ X ]ᵗ)



infix 3 _∣_∣_⊩_⊑_⦂_
data _∣_∣_⊩_⊑_⦂_ : ∀{Δ}(Σ Σ′ : BindCtx Δ){A B : Type Δ}{Γ Γ′ : Ctx Δ}
  → PrecCtx Γ Γ′ → (Δ ∣ Σ ∣ Γ ⊢ A) → (Δ ∣ Σ′ ∣ Γ′ ⊢ B)
  → Δ ∣ mt Δ ⊢ A ⊑ B → Set  where
  
  ⊑-var : ∀{Δ}{Σ Σ′ : BindCtx Δ}{A B}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
     → (x : Φ ∋ A ⊑ B)
       ---------------------------------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ (` proj-left x) ⊑ (` proj-right x) ⦂ get-⊑ x

  ⊑-nat : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{k : ℕ}
     → Σ ∣ Σ′ ∣ Φ ⊩ (# k) ⊑ (# k) ⦂ ℕ⊑ℕ

  ⊑-lam : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
      {A B C D : Type Δ}{N : Δ ∣ Σ ∣ (Γ ▷ A) ⊢ B} {N′ : Δ ∣ Σ′ ∣ (Γ′ ▷ C) ⊢ D}
      {c : Δ ∣ mt Δ ⊢ A ⊑ C}{d : Δ ∣ mt Δ ⊢ B ⊑ D}
     → Σ ∣ Σ′ ∣ (Φ , c) ⊩ N ⊑ N′ ⦂ d
       ---------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ ƛ N ⊑ ƛ N′ ⦂ ⇒⊑⇒ c d
  
  ⊑-app : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
       {A B C D : Type Δ} {L : Δ ∣ Σ ∣ Γ ⊢ A ⇒ B} {M : Δ ∣ Σ ∣ Γ ⊢ A}
       {L′ : Δ ∣ Σ′ ∣ Γ′ ⊢ C ⇒ D} {M′ : Δ ∣ Σ′ ∣ Γ′ ⊢ C}
       {c : Δ ∣ mt Δ ⊢ A ⊑ C}{d : Δ ∣ mt Δ ⊢ B ⊑ D}
     → Σ ∣ Σ′ ∣ Φ ⊩ L ⊑ L′ ⦂ (⇒⊑⇒ c d)
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ c
       --------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ L · M ⊑ L′ · M′ ⦂ d
  
  ⊑-Λ : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
      {A B : Type (Δ ,typ)}{N : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A}
      {N′ : (Δ ,typ) ∣ ⤊ Σ′ ∣ ⟰ Γ′ ⊢ B}
      {c : (Δ ,typ) ∣ mt (Δ ,typ) ⊢ A ⊑ B}
     → ⤊ Σ ∣ ⤊ Σ′ ∣ ⟰ᵖ Φ ⊩ N ⊑ N′ ⦂ c
       --------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ Λ N ⊑ Λ N′ ⦂ ∀⊑∀ c
      
  
  ⊑-◯ : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
        {A B : Type (Δ ,typ)}{M : Δ ∣ Σ ∣ Γ ⊢ `∀ A}
        {M′ : Δ ∣ Σ′  ∣ Γ′ ⊢ `∀ B}{X}
        {c : (Δ ,typ) ∣ mt (Δ ,typ) ⊢ A ⊑ B}
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ ∀⊑∀ c
       ----------------------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ (M ◯ X) ⊑ (M′ ◯ X) ⦂ subᵗ-prec c

  ⊑-blame : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
        {A : Type Δ}{M : Δ ∣ Σ ∣ Γ ⊢ A}{M : Δ ∣ Σ ∣ Γ ⊢ A}
       --------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ blame ⦂ Refl⊑ A

  
