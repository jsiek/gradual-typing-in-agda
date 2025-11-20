{-# OPTIONS --rewriting #-}
module PolyBlame.Variables where

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

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

infixl 5 _▷_

{--- Contexts for Term Variables ---}

data Ctx : (Δ : TyCtx) → Set where
  ∅ : ∀{Δ} → Ctx Δ
  _▷_ : ∀{Δ : TyCtx} → Ctx Δ → Type Δ → Ctx Δ

ren-ctx : ∀{Δ₁ Δ₂} → (ρ : Δ₁ ⇒ᵗ Δ₂) → Ctx Δ₁ → Ctx Δ₂
ren-ctx ρ ∅ = ∅
ren-ctx ρ (Γ ▷ A) = ren-ctx ρ Γ ▷ renᵗ ρ A

⟰ : ∀{Δ} → Ctx Δ → Ctx (Δ ,typ)
⟰ Γ = ren-ctx Sᵗ Γ

ext-suc-ctx : ∀{Δ₁ Δ₂ : TyCtx}{Γ : Ctx Δ₁}{ρ  : Δ₁ ⇒ᵗ Δ₂}
     → ren-ctx (extᵗ ρ) (⟰ Γ) ≡ ⟰ (ren-ctx ρ Γ)
ext-suc-ctx {Γ = ∅} {ρ} = refl
ext-suc-ctx {Γ = Γ ▷ A} {ρ} = cong₂ _▷_ ext-suc-ctx refl
{-# REWRITE ext-suc-ctx #-}

ren-ctx-∘ : ∀{Δ₁ Δ₂ Δ₃}{Γ : Ctx Δ₁} → (ρ₁ : Δ₁ ⇒ᵗ Δ₂) → (ρ₂ : Δ₂ ⇒ᵗ Δ₃)
  → ((ren-ctx ρ₂) ∘ (ren-ctx ρ₁)) Γ ≡ (ren-ctx (ρ₁ ⨟ᵗ ρ₂)) Γ
ren-ctx-∘ {Γ = ∅} ρ₁ ρ₂ = refl
ren-ctx-∘ {Γ = Γ ▷ A} ρ₁ ρ₂ = cong₂ _▷_ (ren-ctx-∘ {Γ = Γ} ρ₁ ρ₂) refl
{-# REWRITE ren-ctx-∘ #-}

ren-ctx-id : ∀{Δ} (Γ : Ctx Δ)
  → ren-ctx idᵗ Γ ≡ Γ
ren-ctx-id ∅ = refl
ren-ctx-id (Γ ▷ A) = cong₂ _▷_ (ren-ctx-id Γ) refl
{-# REWRITE ren-ctx-id #-}

{--- Term Variables ---}

infix  4 _∋_
data _∋_ : ∀{Δ} → Ctx Δ → Type Δ → Set where
  Z : ∀{Δ}{Γ : Ctx Δ}{A : Type Δ}
     → Γ ▷ A ∋ A
  S_ : ∀{Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → Γ ∋ A
     → Γ ▷ B ∋ A

ren-var : ∀{Δ₁ Δ₂}{Γ : Ctx Δ₁}{A : Type Δ₁}
  → (ρ : Δ₁ ⇒ᵗ Δ₂) 
  → Γ ∋ A
  → ren-ctx ρ Γ ∋ renᵗ ρ A
ren-var {Δ₁} {Δ₂} {Γ ▷ B} {A} ρ Z = Z
ren-var {Δ₁} {Δ₂} {Γ ▷ B} {A} ρ (S x) = S ren-var ρ x

_⇨ᵣ_ : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Γ ⇨ᵣ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A

ext : ∀ {Δ : TyCtx}{Γ Γ′ : Ctx Δ}{A : Type Δ}
  → Γ ⇨ᵣ Γ′
  → (Γ ▷ A) ⇨ᵣ (Γ′ ▷ A)
ext ρ Z = Z
ext ρ (S x) = S ρ x

ren-ctx-∋ : ∀ {Δ Δ′}{Γ : Ctx Δ}{A : Type Δ′}{B : Type Δ}{r : Δ ⇒ᵗ Δ′}
  → ren-ctx r Γ ∋ A
  → Σ[ B ∈ Type Δ ] A ≡ renᵗ r B × Γ ∋ B
ren-ctx-∋ {Δ}{Δ′} {Γ ▷ C} Z = C , refl , Z
ren-ctx-∋ {Δ}{Δ′}{Γ ▷ C}{A}{B} (S x)
    with ren-ctx-∋{Δ}{Δ′}{Γ}{A}{B} x
... | C , refl , y = C , refl , (S y)

rename-ctx : ∀ {Δ₁ Δ₂ : TyCtx}{r : Δ₁ ⇒ᵗ Δ₂}{Γ : Ctx Δ₁}{Γ′ : Ctx Δ₁}
  → Γ ⇨ᵣ Γ′
  → ren-ctx r Γ ⇨ᵣ ren-ctx r Γ′
rename-ctx {Δ₁} {Δ₂} {r} {Γ ▷ A} {Γ′} ρ {B} Z = ren-var r (ρ Z)
rename-ctx {Δ₁} {Δ₂} {r} {Γ ▷ A} {Γ′} ρ {B} (S x)
    with ren-ctx-∋{Δ₁}{Δ₂}{Γ}{B = A} {r = r} x
... | C , refl , Γ∋C = ren-var r (ρ (S Γ∋C))

data PrecCtx : ∀{Δ}(Γ Γ′ : Ctx Δ) → Set where
  ∅ : PrecCtx{∅} ∅ ∅
  _,_ : ∀{Δ}{Γ Γ′ : Ctx Δ}{A B : Type Δ}
        → PrecCtx Γ Γ′
        → Δ ∣ mt Δ ⊢ A ⊑ B
          ------------------------
        → PrecCtx (Γ ▷ A) (Γ′ ▷ B)

data ⊢_∋_⊑_ : ∀{Δ}{Γ Γ′ : Ctx Δ} → PrecCtx Γ Γ′ → Type Δ → Type Δ → Set where

  Zᵖ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B : Type Δ}
      {p : Δ ∣ mt Δ ⊢ A ⊑ B}
      ----------------------
    → ⊢ (Φ , p) ∋ A ⊑ B
    
  Sᵖ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B C D : Type Δ}
      {p : Δ ∣ mt Δ ⊢ C ⊑ D}
    → ⊢ Φ ∋ A ⊑ B
      -------------------
    → ⊢ (Φ , p) ∋ A ⊑ B

get-⊑ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B : Type Δ}
  → (x : ⊢ Φ ∋ A ⊑ B) → Δ ∣ mt Δ ⊢ A ⊑ B
get-⊑ (Zᵖ{p = p}) = p
get-⊑ (Sᵖ x) = get-⊑ x

proj-left : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B : Type Δ}
  → (x : ⊢ Φ ∋ A ⊑ B) → Γ ∋ A
proj-left Zᵖ = Z
proj-left (Sᵖ x) = S proj-left x

proj-right : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{A B : Type Δ}
  → (x : ⊢ Φ ∋ A ⊑ B) → Γ′ ∋ B
proj-right Zᵖ = Z
proj-right (Sᵖ x) = S proj-right x

postulate
  ⟰ᵖ : ∀ {Δ}{Γ Γ′ : Ctx Δ}
    → PrecCtx Γ Γ′
    → PrecCtx (⟰ Γ) (⟰ Γ′)
