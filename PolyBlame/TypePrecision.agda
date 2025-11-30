{-# OPTIONS --rewriting #-}

module PolyBlame.TypePrecision where

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

{-- Precision --}

{-
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
-}

infixr 6 _∣_⊢_⊑_
data _∣_⊢_⊑_ : (Δ : TyCtx) → BindCtx Δ → Type Δ → Type Δ → Set where
  ℕ⊑ℕ : ∀{Δ}{Σ}
      ------------------
     → Δ ∣ Σ ⊢ `ℕ ⊑ `ℕ
     
  X⊑X : ∀{Δ}{Σ}{X}
      --------------------
     → Δ ∣ Σ ⊢ ` X ⊑ ` X

  ★⊑★ : ∀{Δ}{Σ}
      ----------------
     → Δ ∣ Σ ⊢ ★ ⊑ ★

  ★⊑X : ∀{Δ}{Σ}{X : TyVar Δ}
     → Σ ∋ X := ★
      --------------------
     → Δ ∣ Σ ⊢ ★ ⊑ ` X

  ★⊑ℕ : ∀{Δ}{Σ}
     --------------------
     → Δ ∣ Σ ⊢ ★ ⊑ `ℕ

  ★⊑⇒ : ∀{Δ}{Σ}{A B}
     → Δ ∣ Σ ⊢ ★ ⊑ A
     → Δ ∣ Σ ⊢ ★ ⊑ B
       ------------------
     → Δ ∣ Σ ⊢ ★ ⊑ A ⇒ B
  
  ⇒⊑⇒ : ∀{Δ}{Σ}{A B C D}
     →  Δ ∣ Σ ⊢ A ⊑ C
     →  Δ ∣ Σ ⊢ B ⊑ D
      ------------------------
     → Δ ∣ Σ ⊢ A ⇒ B ⊑ C ⇒ D

  ∀⊑∀ : ∀{Δ}{Σ}{A B}
     → (Δ ,typ) ∣ (⤊ Σ) ⊢ A ⊑ B
      --------------------------
     → Δ ∣ Σ ⊢ `∀ A ⊑ `∀ B

  ⊑∀ : ∀{Δ}{Σ}{A B}
     → (Δ ,typ) ∣ ((Zᵗ , ★) ∷ ⤊ Σ) ⊢ ⇑ᵗ A ⊑ B
      -----------------------------------------
     → Δ ∣ Σ ⊢ A ⊑ `∀ B

Refl⊑ : ∀{Δ}{Σ : BindCtx Δ} → (A : Type Δ) → Δ ∣ Σ ⊢ A ⊑ A
Refl⊑ {Δ} {Σ} `ℕ = ℕ⊑ℕ
Refl⊑ {Δ} {Σ} ★ = ★⊑★
Refl⊑ {Δ} {Σ} (` X) = X⊑X
Refl⊑ {Δ} {Σ} (A ⇒ B) = ⇒⊑⇒ (Refl⊑ A) (Refl⊑ B)
Refl⊑ {Δ} {Σ} (`∀ A) = ∀⊑∀ (Refl⊑ A)

≤-or-left : ∀ b b′ → b ≤ (b ∨ b′)
≤-or-left false false = _≤_.b≤b
≤-or-left false true = _≤_.f≤t
≤-or-left true false = _≤_.b≤b
≤-or-left true true = _≤_.b≤b

≤-or-right : ∀ b b′ → b′ ≤ (b ∨ b′)
≤-or-right false false = _≤_.b≤b
≤-or-right false true = _≤_.b≤b
≤-or-right true false = _≤_.f≤t
≤-or-right true true = _≤_.b≤b

or-≤-left : ∀{a b c : Bool}
  → a ∨ b ≤ c
  → a ≤ c
or-≤-left {false} {false} {true} _≤_.f≤t = _≤_.f≤t
or-≤-left {false} {false} {b} _≤_.b≤b = _≤_.b≤b
or-≤-left {false} {true} {b} _≤_.b≤b = _≤_.f≤t
or-≤-left {true} {b} {c} _≤_.b≤b = _≤_.b≤b

or-≤-right : ∀{a b c : Bool}
  → a ∨ b ≤ c
  → b ≤ c
or-≤-right {false} {false} {true} _≤_.f≤t = _≤_.f≤t
or-≤-right {false} {false} {b} _≤_.b≤b = _≤_.b≤b
or-≤-right {false} {true} {b} _≤_.b≤b = _≤_.b≤b
or-≤-right {true} {false} {c} _≤_.b≤b = _≤_.f≤t
or-≤-right {true} {true} {c} _≤_.b≤b = _≤_.b≤b

≤-∨-≤ : ∀{x y z : Bool}
  → x ≤ z
  → y ≤ z
  → x ∨ y ≤ z
≤-∨-≤ {false} {false} {z} _≤_.f≤t _≤_.f≤t = _≤_.f≤t
≤-∨-≤ {false} {false} {z} _≤_.b≤b y≤z = y≤z
≤-∨-≤ {false} {true} {z} x≤z y≤z = y≤z
≤-∨-≤ {true} {y} {z} x≤z y≤z = x≤z

-- single : ∀{Δ} → (X : TyVar Δ) → SubCtx Δ
-- single {Δ ,typ} Zᵗ = mt Δ , true
-- single {Δ ,typ} (Sᵗ X) = single X , false

-- single-∋ : ∀{Δ} → (X : TyVar Δ)
--   → single X ∋ˢ X
-- single-∋ Zᵗ = Zˢ
-- single-∋ (Sᵗ X) = Sˢ (single-∋ X)

-- _∪_ : ∀{Δ}(Ψ₁ : SubCtx Δ) (Ψ₂ : SubCtx Δ) → SubCtx Δ
-- ∅ ∪ ∅ = ∅
-- (Ψ₁ , a) ∪ (Ψ₂ , b) = (Ψ₁ ∪ Ψ₂) , (a ∨ b)

-- ⤋ : ∀{Δ} → SubCtx (Δ ,typ) → SubCtx Δ
-- ⤋ {Δ} (Ψ , b) = Ψ

-- FV : ∀{Δ} → (B : Type Δ) → SubCtx Δ
-- FV{Δ} `ℕ = mt Δ
-- FV{Δ} ★ = mt Δ
-- FV{Δ} (` X) = single X
-- FV{Δ} (B₁ ⇒ B₂) = FV B₁ ∪ FV B₂
-- FV{Δ} (`∀ B) = ⤋ (FV B)

-- _⊆_ : ∀{Δ} → SubCtx Δ → SubCtx Δ → Set
-- ∅ ⊆ Ψ₂ = ⊤
-- (Ψ₁ , a) ⊆ (Ψ₂ , b) = Ψ₁ ⊆ Ψ₂ × a ≤ b

-- mt-⊆ : ∀{Δ}{Ψ : SubCtx Δ}
--   → mt Δ ⊆ Ψ
-- mt-⊆ {∅} {Ψ} = tt
-- mt-⊆ {Δ ,typ} {Ψ , false} = mt-⊆ , _≤_.b≤b
-- mt-⊆ {Δ ,typ} {Ψ , true} = mt-⊆ , _≤_.f≤t

-- ⊆-∋ : ∀{Δ}{Ψ₁ Ψ₂ : SubCtx Δ}{X : TyVar Δ}
--   → Ψ₁ ⊆ Ψ₂
--   → Ψ₁ ∋ˢ X
--   → Ψ₂ ∋ˢ X
-- ⊆-∋ {Δ ,typ} {Ψ₁ , a} {Ψ₂ , b} {Zᵗ} (Ψ₁⊆Ψ₂ , _≤_.b≤b) Zˢ = Zˢ
-- ⊆-∋ {Δ ,typ} {Ψ₁ , a} {Ψ₂ , b} {Sᵗ X} (Ψ₁⊆Ψ₂ , lt) (Sˢ Ψ₁∋ˢX) = Sˢ (⊆-∋ Ψ₁⊆Ψ₂ Ψ₁∋ˢX)

-- ∪-⊆ : ∀{Δ}{Ψ₁ Ψ₂ Ψ₃ : SubCtx Δ}
--   → (Ψ₁ ∪ Ψ₂) ⊆ Ψ₃
--   → Ψ₁ ⊆ Ψ₃ × Ψ₂ ⊆ Ψ₃
-- ∪-⊆ {∅} {∅} {∅} {∅} Y123 = tt , tt
-- ∪-⊆ {Δ ,typ} {Ψ₁ , a} {Ψ₂ , b} {Ψ₃ , c} (Y123 , abc) =
--   (∪-⊆ Y123 .proj₁ , or-≤-left abc) , (∪-⊆ Y123 .proj₂ , or-≤-right abc)

-- ⊆-∪ : ∀{Δ}{Ψ₁ Ψ₂ Ψ₃ : SubCtx Δ}
--   → Ψ₁ ⊆ Ψ₃
--   → Ψ₂ ⊆ Ψ₃
--   → (Ψ₁ ∪ Ψ₂) ⊆ Ψ₃
-- ⊆-∪ {Δ} {∅} {∅} {Ψ₃} Ψ₁⊆Ψ₃ Ψ₂⊆Ψ₃ = tt
-- ⊆-∪ {Δ} {Ψ₁ , x} {Ψ₂ , y} {Ψ₃ , z} (Ψ₁⊆Ψ₃ , x≤z) (Ψ₂⊆Ψ₃ , y≤z) =
--   (⊆-∪ Ψ₁⊆Ψ₃ Ψ₂⊆Ψ₃) , ≤-∨-≤ x≤z y≤z

-- ∋-single-⊆ : ∀{Δ : TyCtx}{Ψ : SubCtx Δ}{X : TyVar Δ}
--   → Ψ ∋ˢ X
--   → single X ⊆ Ψ
-- ∋-single-⊆ {Δ} {Ψ} {X} Zˢ = mt-⊆ , _≤_.b≤b
-- ∋-single-⊆ {Δ ,typ} {Ψ , false} {Sᵗ X} (Sˢ Ψ∋X) = ∋-single-⊆ Ψ∋X , _≤_.b≤b
-- ∋-single-⊆ {Δ ,typ} {Ψ , true} {Sᵗ X} (Sˢ Ψ∋X) = ∋-single-⊆ Ψ∋X , _≤_.f≤t

-- ⤋-⊆ : ∀{Δ}{Ψ₁ : SubCtx (Δ ,typ)}{Ψ₂ : SubCtx Δ}
--   → (⤋ Ψ₁) ⊆ Ψ₂
--   → Ψ₁ ⊆ (Ψ₂ , true)
-- ⤋-⊆ {Δ} {Ψ₁ , false} {Ψ₂} Ψ₁⊆Ψ₂ = Ψ₁⊆Ψ₂ , _≤_.f≤t
-- ⤋-⊆ {Δ} {Ψ₁ , true} {Ψ₂} Ψ₁⊆Ψ₂ = Ψ₁⊆Ψ₂ , _≤_.b≤b

-- ⊆-⤋ : ∀{Δ}{Ψ₁ : SubCtx (Δ ,typ)}{Ψ₂ : SubCtx Δ}{b : Bool}
--   → Ψ₁ ⊆ (Ψ₂ , b)
--   → (⤋ Ψ₁) ⊆ Ψ₂
-- ⊆-⤋ {Δ} {Ψ₁ , x} {Ψ₂} Ψ₁⊆Ψ₂ = Ψ₁⊆Ψ₂ .proj₁

-- ★-⊑ : ∀{Δ}{Ψ : SubCtx Δ} → (B : Type Δ)
--   → FV B ⊆ Ψ
--   → Δ ∣ Ψ ⊢ ★ ⊑ B
-- ★-⊑ `ℕ B⊆Ψ = ★⊑ℕ
-- ★-⊑ ★ B⊆Ψ = ★⊑★
-- ★-⊑ (` X) B⊆Ψ = ★⊑X (⊆-∋ B⊆Ψ (single-∋ X))
-- ★-⊑ (B₁ ⇒ B₂) B⊆Ψ =
--   ★⊑⇒ (★-⊑ B₁ (∪-⊆ B⊆Ψ .proj₁)) (★-⊑ B₂ (∪-⊆ B⊆Ψ .proj₂))
-- ★-⊑ (`∀ B) B⊆Ψ = ⊑∀ (★-⊑ B (⤋-⊆ B⊆Ψ))

postulate
  ⊑-⇑ᵗ : ∀{Δ}{Σ : BindCtx Δ} → (A B : Type Δ)
    → Δ ∣ Σ ⊢ A ⊑ B
    → (Δ ,typ) ∣ ⤊ Σ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
