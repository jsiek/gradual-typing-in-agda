{-# OPTIONS --rewriting #-}

module PolyBlame.Coercions where

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

data Crcn : ∀(Δ : TyCtx) → BindCtx Δ → Type Δ → Type Δ → Set where
 id : ∀{Δ}{Σ}{A : Type Δ} → Crcn Δ Σ A A
 _↦_ : ∀{Δ}{Σ}{A B C D : Type Δ}
   → Crcn Δ Σ C A
   → Crcn Δ Σ B D
   → Crcn Δ Σ (A ⇒ B) (C ⇒ D)
 _⨟_ : ∀{Δ}{Σ}{A B C : Type Δ}
   → Crcn Δ Σ A B
   → Crcn Δ Σ B C
   → Crcn Δ Σ A C
 `∀_ : ∀{Δ}{Σ}{A B : Type (Δ ,typ)}
   → Crcn (Δ ,typ) (⤊ Σ) A B
   → Crcn Δ Σ (`∀ A) (`∀ B)
 𝒢 : ∀{Δ}{Σ}{A : Type Δ} {B : Type (Δ ,typ)}
   → Crcn (Δ ,typ) (⤊ Σ) (⇑ᵗ A) B
   → Crcn Δ Σ A (`∀ B)
 ℐ : ∀{Δ}{Σ}{A : Type (Δ ,typ)} {B : Type Δ}
   → Crcn (Δ ,typ) ((Zᵗ , ★) ∷ ⤊ Σ) A (⇑ᵗ B)
   → Crcn Δ Σ (`∀ A) B
 _↓ : ∀{Δ}{Σ}{A : Type Δ}{X : TyVar Δ}
   → Σ ∋ X := A
   → Crcn Δ Σ A (` X)
 _↑ : ∀{Δ}{Σ}{A : Type Δ}{X : TyVar Δ}
   → Σ ∋ X := A
   → Crcn Δ Σ (` X) A
 _! : ∀{Δ}{Σ}
   → (G : Grnd Δ)
   → Crcn Δ Σ ⌈ G ⌉ ★
 _`? : ∀{Δ}{Σ}
   → (H : Grnd Δ)
   → Crcn Δ Σ ★ ⌈ H ⌉

infix 4 _∣_⊢_⇒_
_∣_⊢_⇒_ : ∀(Δ : TyCtx) → BindCtx Δ → Type Δ → Type Δ → Set
Δ ∣ Σ ⊢ A ⇒ B = Crcn Δ Σ A B

extr-suc-commute : ∀{Δ₁ Δ₂}{ρ : Δ₁ ⇒ᵣ Δ₂}{A}
  → (ren-type (extᵗ ρ) (⇑ᵗ A)) ≡ (⇑ᵗ (ren-type ρ A))
extr-suc-commute = refl

ren-bind : ∀{Δ₁ Δ₂ : TyCtx}{Σ : BindCtx Δ₁}{ρ : Δ₁ ⇒ᵣ Δ₂}
    {X : TyVar Δ₁}{A : Type Δ₁}
  → Σ ∋ X := A
  → map (ren-pair ρ) Σ ∋ ρ X := ren-type ρ A
ren-bind {Δ₁} {Δ₂} {Σ} {ρ} {X} {A} Zᵇ = Zᵇ
ren-bind {Δ₁} {Δ₂} {Σ} {ρ} {X} {A} (Sᵇ ∋α) = Sᵇ (ren-bind ∋α)

from-grnd-ren : ∀{Δ₁ Δ₂} (ρ : Δ₁ ⇒ᵣ Δ₂)(G : Grnd Δ₁)
  → ⌈ ren-grnd ρ G ⌉ ≡ ren-type ρ ⌈ G ⌉ 
from-grnd-ren ρ ★⇒★ = refl
from-grnd-ren ρ `ℕ = refl
from-grnd-ren ρ (` X) = refl
{-# REWRITE from-grnd-ren #-}

map-fusion : ∀ {A B C : Set}{xs : List A}{f : A → B}{g : B → C}
  → map g (map f xs) ≡ map (g ∘ f) xs
map-fusion {xs = xs} = sym (map-∘ xs)
{-# REWRITE map-fusion #-}

rename-crcn : ∀{Δ₁ Δ₂}{Σ}{A B}
  → (ρ : Δ₁ ⇒ᵣ Δ₂)
  → Δ₁ ∣ Σ ⊢ A ⇒ B
  → Δ₂ ∣ map (ren-pair ρ) Σ ⊢ (ren-type ρ A) ⇒ (ren-type ρ B)
rename-crcn ρ id = id
rename-crcn ρ (c ↦ d) = rename-crcn ρ c ↦ rename-crcn ρ d
rename-crcn ρ (c ⨟ d) = rename-crcn ρ c ⨟ rename-crcn ρ d
rename-crcn{Δ₁}{Δ₂}{Σ}{`∀ A}{`∀ B} ρ (`∀ c) =
  let IH = rename-crcn (extᵗ ρ) c in `∀ IH
rename-crcn {Δ₁}{Δ₂}{Σ}{A}{`∀ B} ρ (𝒢{Δ₁}{Σ}{A}{B} c) =
  let IH = rename-crcn (extᵗ ρ) c in 𝒢 IH
rename-crcn {Δ₁}{Δ₂}{Σ}{`∀ A}{B} ρ (ℐ c) =
  let IH = rename-crcn (extᵗ ρ) c in ℐ IH
rename-crcn {Δ₁}{Δ₂}{Σ} ρ (∋α ↓)  = (ren-bind ∋α) ↓
rename-crcn ρ (∋α ↑) = (ren-bind ∋α) ↑
rename-crcn ρ (G !) = ren-grnd ρ G !
rename-crcn ρ (H `?) = ren-grnd ρ H `?

infix 6 _[_]ᶜ
_[_]ᶜ : ∀{Δ}{Σ}{A}{B} → (Δ ,typ) ∣ Σ ⊢ A ⇒ B
  → (X : TyVar Δ)
  → Δ ∣ map (ren-pair (X •ᵗ idᵗ)) Σ ⊢ ren-type (X •ᵗ idᵗ) A ⇒ ren-type (X •ᵗ idᵗ) B
c [ X ]ᶜ = rename-crcn (X •ᵗ idᵗ) c

{- Renaming Bind Variables -}

infixr 7 _⇒ᵇ_
_⇒ᵇ_ : ∀{Δ} → BindCtx Δ → BindCtx Δ → Set
Σ₁ ⇒ᵇ Σ₂ = ∀{X A} → Σ₁ ∋ X := A → Σ₂ ∋ X := A

extᵇ : ∀{Δ}{Σ₁ Σ₂ : BindCtx Δ}
  → Σ₁ ⇒ᵇ Σ₂
  → ⤊ Σ₁ ⇒ᵇ ⤊ Σ₂
extᵇ {Δ} {(X , B) ∷ Σ₁} {Σ₂} ρ Zᵇ =
    ren-bind{ρ = Sᵗ} (ρ Zᵇ)
extᵇ {Δ} {(X , B) ∷ Σ₁} {Σ₂} ρ (Sᵇ ∋X) =
    extᵇ (λ {X = X₂} {A = A₁} z → ρ (Sᵇ z)) ∋X

extᶜ : ∀{Δ}{Σ₁ Σ₂ : BindCtx Δ}{X A}
  → Σ₁ ⇒ᵇ Σ₂
  → ((X , A) ∷ Σ₁) ⇒ᵇ ((X , A) ∷ Σ₂)
extᶜ {Δ} {Σ₁} {Σ₂} {X} {A} ρ Zᵇ = Zᵇ
extᶜ {Δ} {Σ₁} {Σ₂} {X} {A} ρ (Sᵇ ∋X) = Sᵇ (ρ ∋X)

rename-crcn-bind : ∀{Δ}{Σ₁ Σ₂ : BindCtx Δ}{A B}
  → (ρ : Σ₁ ⇒ᵇ Σ₂)
  → Δ ∣ Σ₁ ⊢ A ⇒ B
  → Δ ∣ Σ₂ ⊢ A ⇒ B
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ id = id
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (c ↦ d) =
   rename-crcn-bind ρ c ↦ rename-crcn-bind ρ d
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (c ⨟ d) =
   rename-crcn-bind ρ c ⨟ rename-crcn-bind ρ d
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (`∀ c) =
   `∀ (rename-crcn-bind (extᵇ ρ) c)
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (𝒢 c) =
   𝒢 (rename-crcn-bind (extᵇ ρ) c)
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (ℐ c) =
   ℐ (rename-crcn-bind (extᶜ (extᵇ ρ)) c)
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (X ↓) = ρ X ↓
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (X ↑) = ρ X ↑
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (G !) = (G !)
rename-crcn-bind {Δ} {Σ₁} {Σ₂} {A} {B} ρ (H `?) = H `?
