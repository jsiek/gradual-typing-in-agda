{-# OPTIONS --rewriting #-}
module PolyBlame.Intrinsic where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)

open import PolyBlame.Rename

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

infix  5 ƛ_
infixl 7 _·_
infixl 7 _◯_
infix  9 `_
infix  9 #_

infixl 5 _▷_

data Ctx : (Δ : TyCtx) → Set where
  ∅ : ∀{Δ} → Ctx Δ
  _▷_ : ∀{Δ : TyCtx}
      → Ctx Δ
      → Type Δ
      → Ctx Δ

infix  4 _∋_
data _∋_ : ∀{Δ} → Ctx Δ → Type Δ → Set where
  Z : ∀{Δ}{Γ : Ctx Δ}{A : Type Δ}
     → Γ ▷ A ∋ A
  S_ : ∀{Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → Γ ∋ A
     → Γ ▷ B ∋ A

⟰ : ∀{Δ} → Ctx Δ → Ctx (Δ ,typ)
⟰ ∅ = ∅
⟰ (Γ ▷ A) = (⟰ Γ) ▷ ren-ty sucʳ A

⟰ᵇ : ∀{Δ B} → Ctx Δ → Ctx (Δ ,= B)
⟰ᵇ ∅ = ∅
⟰ᵇ (Γ ▷ A) = (⟰ᵇ Γ) ▷ ren-ty sucᵇ A

data _∣_⊢_ : (Δ : TyCtx) → Ctx Δ → Type Δ → Set where
  `_ : ∀{Δ Γ A}
     → Γ ∋ A
       ---------
     → Δ ∣ Γ ⊢ A
     
  #_ : ∀{Δ Γ}
     → ℕ
       -----------
     → Δ ∣ Γ ⊢ `ℕ
     
  ƛ_ : ∀{Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → Δ ∣ (Γ ▷ A) ⊢ B
       ---------------
     → Δ ∣ Γ ⊢ (A ⇒ B)
     
  _·_ : ∀{Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → Δ ∣ Γ ⊢ (A ⇒ B)
     → Δ ∣ Γ ⊢ A
       ---------------
     → Δ ∣ Γ ⊢ B
     
  Λ_ : ∀{Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
     → (Δ ,typ) ∣ ⟰ Γ ⊢ A
     → Δ ∣ Γ ⊢ (`∀ A)
     
  _◯_ : ∀{Δ Γ A}
     → Δ ∣ Γ ⊢ (`∀ A)
     → (X : TyVar Δ)
       -----------------------------
     → Δ ∣ Γ ⊢ ren-type (X •ᵗ idᵗ) A
     
  _⟨_⟩ : ∀{Δ Γ A B}
     → Δ ∣ Γ ⊢ A
     → Δ ⊢ A ⇒ B
       ----------
     → Δ ∣ Γ ⊢ B
     
  blame : ∀{Δ Γ A} → Δ ∣ Γ ⊢ A
  
  ν_·_ : ∀{Δ}{Γ : Ctx Δ}{B : Type Δ}
    → (A : Type Δ)
    → (Δ ,= A) ∣ ⟰ᵇ Γ ⊢ ren-ty sucᵇ B
    → Δ ∣ Γ ⊢ B

ren-ctx : ∀{Δ₁ Δ₂} → (ρ : Δ₁ ⇒ᵣ Δ₂) → Ctx Δ₁ → Ctx Δ₂
ren-ctx ρ ∅ = ∅
ren-ctx ρ (Γ ▷ A) = ren-ctx ρ Γ ▷ ren-type ρ A

ren-var : ∀{Δ₁ Δ₂}{Γ : Ctx Δ₁}{A : Type Δ₁}
  → (ρ : Δ₁ ⇒ᵣ Δ₂) 
  → Γ ∋ A
  → ren-ctx ρ Γ ∋ ren-type ρ A
ren-var {Δ₁} {Δ₂} {Γ ▷ B} {A} ρ Z = Z
ren-var {Δ₁} {Δ₂} {Γ ▷ B} {A} ρ (S x) = S ren-var ρ x


ext-suc-ctx : ∀{Δ₁ Δ₂ : TyCtx}{Γ : Ctx Δ₁}{ρ  : Δ₁ ⇒ᵣ Δ₂}
     → ren-ctx (extᵗ ρ) (⟰ Γ) ≡ ⟰ (ren-ctx ρ Γ)
ext-suc-ctx {Γ = ∅} {ρ} = refl
ext-suc-ctx {Γ = Γ ▷ A} {ρ} = cong₂ _▷_ ext-suc-ctx refl

{-# REWRITE ext-suc-ctx #-}

rename-ty : ∀{Δ₁ Δ₂}{Γ : Ctx Δ₁}{A : Type Δ₁}
  → (ρ : Δ₁ ⇒ᵣ Δ₂) → Δ₁ ∣ Γ ⊢ A → Δ₂ ∣ (ren-ctx ρ Γ) ⊢ ren-type ρ A
rename-ty ρ (` x) = ` ren-var ρ x
rename-ty ρ (# k) = # k
rename-ty ρ (ƛ M) = ƛ rename-ty ρ M
rename-ty ρ (L · M) = rename-ty ρ L · rename-ty ρ M
rename-ty ρ (Λ N) = Λ (rename-ty (extᵗ ρ) N)
rename-ty ρ (M ◯ X) =
  let M′ = rename-ty ρ M in
  -- NTS:
  --   ren-type (ρ X •ᵗ idᵗ) (ren-type (extᵗ ρ) A)
  -- ≡ ren-type ρ (ren-type (X •ᵗ idᵗ) A)
  {!!} ◯ (ρ X)
rename-ty ρ (M ⟨ x ⟩) = {!!}
rename-ty ρ blame = {!!}
rename-ty ρ (ν A · N) = {!!}
