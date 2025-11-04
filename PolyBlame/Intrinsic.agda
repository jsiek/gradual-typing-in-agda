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
open import Function using (_∘_)

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

ren-ctx : ∀{Δ₁ Δ₂} → (ρ : Δ₁ ⇒ᵣ Δ₂) → Ctx Δ₁ → Ctx Δ₂
ren-ctx ρ ∅ = ∅
ren-ctx ρ (Γ ▷ A) = ren-ctx ρ Γ ▷ ren-type ρ A

⟰ : ∀{Δ} → Ctx Δ → Ctx (Δ ,typ)
⟰ Γ = ren-ctx Styp Γ

data _∣_∣_⊢_ : (Δ : TyCtx) → BindCtx Δ → Ctx Δ → Type Δ → Set where
  `_ : ∀{Δ Σ Γ A}
     → Γ ∋ A
       ---------
     → Δ ∣ Σ ∣ Γ ⊢ A
     
  #_ : ∀{Δ Σ Γ}
     → ℕ
       -----------
     → Δ ∣ Σ ∣ Γ ⊢ `ℕ
     
  ƛ_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → Δ ∣ Σ ∣ (Γ ▷ A) ⊢ B
       --------------------
     → Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)
     
  _·_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)
     → Δ ∣ Σ ∣ Γ ⊢ A
       -------------------
     → Δ ∣ Σ ∣ Γ ⊢ B
     
  Λ_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
     → (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A
     → Δ ∣ Σ ∣ Γ ⊢ (`∀ A)
     
  _◯_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
     → Δ ∣ Σ ∣ Γ ⊢ (`∀ A)
     → (X : TyVar Δ)
       -----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ren-type (X •ᵗ idᵗ) A
     
  _⟨_⟩ : ∀{Δ Σ Γ A B}
     → Δ ∣ Σ ∣ Γ ⊢ A
     → Δ ∣ Σ ⊢ A ⇒ B
       --------------
     → Δ ∣ Σ ∣ Γ ⊢ B
     
  blame : ∀{Δ Σ Γ A} → Δ ∣ Σ ∣ Γ ⊢ A
  
  ν_·_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{B : Type Δ}
    → (A : Type Δ)
    → (Δ ,typ) ∣ (Ztyp , ren-type Styp A) ∷ ⤊ Σ ∣ ⟰ Γ ⊢ ren-type Styp B
    → Δ ∣ Σ ∣ Γ ⊢ B

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

rename-ty : ∀{Δ₁ Δ₂}{Σ : BindCtx Δ₁}{Γ : Ctx Δ₁}{A : Type Δ₁}
  → (ρ : Δ₁ ⇒ᵣ Δ₂)
  → Δ₁ ∣ Σ ∣ Γ ⊢ A
  → Δ₂ ∣ map (ren-pair ρ) Σ ∣ (ren-ctx ρ Γ) ⊢ ren-type ρ A
rename-ty ρ (` x) = ` ren-var ρ x
rename-ty ρ (# k) = # k
rename-ty ρ (ƛ M) = ƛ rename-ty ρ M
rename-ty ρ (L · M) = rename-ty ρ L · rename-ty ρ M
rename-ty ρ (Λ N) =
  let IH = rename-ty (extᵗ ρ) N
  in Λ IH
rename-ty{Δ₁}{Δ₂}{Γ}{A} ρ (_◯_{A = B} M X) =
  (rename-ty ρ M) ◯ (ρ X)
rename-ty ρ (M ⟨ c ⟩) =
  rename-ty ρ M ⟨ rename-crcn ρ c ⟩
rename-ty ρ blame = blame
rename-ty ρ (ν A · N) =
  let N′ = rename-ty (extᵗ ρ) N in
  ν (ren-type ρ A) · N′

ren-pair-∘ : ∀{Δ₁ Δ₂ Δ₃}{x : TyVar Δ₁ × Type Δ₁} → (ρ₁ : Δ₁ ⇒ᵣ Δ₂) → (ρ₂ : Δ₂ ⇒ᵣ Δ₃)
  → ((ren-pair ρ₂) ∘ (ren-pair ρ₁)) x ≡ (ren-pair (ρ₁ ⨟ᵗ ρ₂)) x
ren-pair-∘ {Δ₁}{Δ₂}{Δ₃}{x} ρ₁ ρ₂ = refl

map-ren-pair-id : ∀{Δ} (Σ : BindCtx Δ)
  → map (ren-pair idᵗ) Σ ≡ Σ
map-ren-pair-id [] = refl
map-ren-pair-id ((X , A) ∷ Σ) = cong₂ _∷_ refl (map-ren-pair-id Σ)
{-# REWRITE map-ren-pair-id #-}

ren-ctx-∘ : ∀{Δ₁ Δ₂ Δ₃}{Γ : Ctx Δ₁} → (ρ₁ : Δ₁ ⇒ᵣ Δ₂) → (ρ₂ : Δ₂ ⇒ᵣ Δ₃)
  → ((ren-ctx ρ₂) ∘ (ren-ctx ρ₁)) Γ ≡ (ren-ctx (ρ₁ ⨟ᵗ ρ₂)) Γ
ren-ctx-∘ {Γ = ∅} ρ₁ ρ₂ = refl
ren-ctx-∘ {Γ = Γ ▷ A} ρ₁ ρ₂ = cong₂ _▷_ (ren-ctx-∘ {Γ = Γ} ρ₁ ρ₂) refl
{-# REWRITE ren-ctx-∘ #-}

ren-ctx-id : ∀{Δ} (Γ : Ctx Δ)
  → ren-ctx idᵗ Γ ≡ Γ
ren-ctx-id ∅ = refl
ren-ctx-id (Γ ▷ A) = cong₂ _▷_ (ren-ctx-id Γ) refl
{-# REWRITE ren-ctx-id #-}

{- Reduction -}

ext-suc-cons : ∀{Δ₁}{A : Type Δ₁} → extᵗ{Δ₁ = Δ₁} Styp ⨟ᵗ (Ztyp •ᵗ idᵗ) ≡ idᵗ
ext-suc-cons = refl

sandbox : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}{B : Type Δ}
            {V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
            {c : (Δ ,typ) ∣ ((Ztyp , ★) ∷ ⤊ Σ) ⊢ A ⇒ (ren-type Styp B)} → Set
sandbox {Δ}{Σ}{Γ}{A}{B}{V}{c} =
  let lhs : Δ ∣ Σ ∣ Γ ⊢ B
      lhs = V ⟨ ℐ{B = B} c ⟩ in
  let V′  : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ (`∀ ren-type (extᵗ Styp) A)
      V′ = rename-ty Styp V in
  -- TODO: need a weakening lemma for Σ! (for terms and coercions)
  let V″ : (Δ ,typ) ∣ (Ztyp , ★) ∷ ⤊ Σ ∣ ⟰ Γ ⊢ (`∀ ren-type (extᵗ Styp) A)
      V″ = {!!} in

  let rhs : Δ ∣ Σ ∣ Γ ⊢ B
      rhs = (ν ★ · ((V″ ◯ Ztyp) ⟨ c ⟩)) in
  ⊤

infix 2 _—→_
data _—→_ : ∀ {Δ Σ Γ A} → (Δ ∣ Σ ∣ Γ ⊢ A) → (Δ ∣ Σ ∣ Γ ⊢ A) → Set where

  -- (ΛX.V)[Y]             —→  V[Y/X]
  β-Λ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
          {V : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A}
          {Y : TyVar Δ}
    →  (Λ V) ◯ Y —→ (let rhs = rename-ty (Y •ᵗ idᵗ) V in rhs)
       -- strange that the `let` is needed.

  -- V⟨∀X.c⟩[Y]            —→  V[Y]⟨c[Y/X]⟩
  β-⟨∀⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type (Δ ,typ)}
            {V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
            {c : Δ ,typ ∣ ⤊ Σ ⊢ A ⇒ B}
            {Y : TyVar Δ}
    → V ⟨ `∀ c ⟩ ◯ Y —→ (V ◯ Y) ⟨ rename-crcn (Y •ᵗ idᵗ) c ⟩

  -- V⟨𝒢 X.c⟩[Y]           —→ V⟨c[Y/X]⟩
  β-⟨𝒢⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}{B : Type (Δ ,typ)}
            {V : Δ ∣ Σ ∣ Γ ⊢ A}
            {c : Δ ,typ ∣ ⤊ Σ ⊢ (ren-type Styp A) ⇒ B}
            {Y : TyVar Δ}
    → V ⟨ 𝒢 c ⟩ ◯ Y —→ V ⟨ rename-crcn (Y •ᵗ idᵗ) c ⟩

  -- V⟨ℐ X.c⟩             —→  νX=★. V[X]⟨c⟩
  -- β-⟨ℐ⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}{B : Type Δ}
  --           {V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
  --           {c : Δ ,typ ∣ (Ztyp , ★) ∷ ⤊ Σ ⊢ A ⇒ (ren-type Styp B)}
  --   → (V ⟨ ℐ c ⟩) —→ (ν ★ · (((rename-ty Styp V) ◯ Ztyp) ⟨ c ⟩))
    
