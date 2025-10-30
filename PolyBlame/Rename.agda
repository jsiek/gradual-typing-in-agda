module PolyBlame.Rename where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Data.Fin

Var = Fin

TyCtx = ℕ

data Type : TyCtx → Set where
  `ℕ  : ∀{Δ} → Type Δ
  ★   : ∀{Δ} → Type Δ
  `_ : ∀{Δ} → (x : Fin Δ) → Type Δ
  _⇒_ : ∀{Δ} → Type Δ → Type Δ → Type Δ
  `∀_  : ∀{Δ} → Type (suc Δ) → Type Δ

data TyRen : TyCtx → TyCtx → Set where
  idr : ∀{Δ} → TyRen zero Δ
  extr : ∀{Δ₁ Δ₂}
    → (ρ : TyRen Δ₁ Δ₂)
    → TyRen (suc Δ₁) (suc Δ₂)
  sucr : ∀{Δ}
    → TyRen Δ (suc Δ)

ren-var : ∀{Δ₁ Δ₂} → TyRen Δ₁ Δ₂ → Fin Δ₁ → Fin Δ₂
ren-var (extr ρ) zero = zero
ren-var (extr ρ) (suc x) = suc (ren-var ρ x)
ren-var sucr x = suc x

ren-ty : ∀{Δ₁ Δ₂} → TyRen Δ₁ Δ₂ → Type Δ₁ → Type Δ₂
ren-ty ρ (A ⇒ B) = (ren-ty ρ A) ⇒ (ren-ty ρ B)
ren-ty ρ `ℕ = `ℕ
ren-ty ρ ★ = ★
ren-ty ρ (`∀ A) = `∀ (ren-ty (extr ρ) A)
ren-ty ρ (` X) = ` (ren-var ρ X)

data TyBinds : TyCtx → Set where
  nilb : ∀{Δ} → TyBinds Δ
  typ-b : ∀{Δ}
     → TyBinds Δ
     → TyBinds (suc Δ)
  bind-b : ∀{Δ}
     → Type (suc Δ)
     → TyBinds Δ
     → TyBinds (suc Δ)

ren-binds : ∀{Δ₁ Δ₂} → TyRen Δ₁ Δ₂ → TyBinds Δ₁ → TyBinds Δ₂
ren-binds ρ nilb = nilb
ren-binds ρ (typ-b Σ) =
  let xx = ren-binds {!!} Σ in
  xx
ren-binds ρ (bind-b A Σ) = {!!}

get : ∀{Δ} → Var Δ → TyBinds Δ → Maybe (Type Δ)
get {Δ} X nilb = nothing
get {suc Δ} zero (typ-b Σ) = nothing
get {suc Δ} (suc X) (typ-b Σ)
    with get X Σ
... | nothing = nothing
... | just A = just (ren-ty sucr A)
get {suc Δ} zero (bind-b A Σ) = just A
get {suc Δ} (suc X) (bind-b A Σ)
    with get X Σ
... | nothing = nothing
... | just A = just (ren-ty sucr A)

data Grnd : TyCtx → Set where
  ★⇒★ : ∀{Δ} → Grnd Δ
  `ℕ  : ∀{Δ} → Grnd Δ
  `_ : ∀{Δ} → Var Δ → Grnd Δ

⌈_⌉ : ∀{Δ} → Grnd Δ → Type Δ
⌈ ★⇒★ ⌉ = ★ ⇒ ★
⌈ `ℕ ⌉ = `ℕ
⌈ ` X ⌉ = ` X

data Crcn : ∀(Δ : TyCtx) (Σ : TyBinds Δ) → Type Δ → Type Δ → Set where
 id : ∀{Δ}{Σ}{A : Type Δ} → Crcn Δ Σ A A
 _↦_ : ∀{Δ}{Σ}{A B C D : Type Δ}
   → Crcn Δ Σ C A
   → Crcn Δ Σ B D
   → Crcn Δ Σ (A ⇒ B) (C ⇒ D)
 _⨟_ : ∀{Δ}{Σ}{A B C : Type Δ}
   → Crcn Δ Σ A B
   → Crcn Δ Σ B C
   → Crcn Δ Σ A C
 `∀_ : ∀{Δ}{Σ}{A B : Type (suc Δ)}
   → Crcn (suc Δ) (typ-b Σ) A B
   → Crcn Δ Σ (`∀ A) (`∀ B)
 𝒢_ : ∀{Δ}{Σ : TyBinds Δ}{A : Type Δ} {B : Type (suc Δ)}
   → Crcn (suc Δ) (typ-b Σ) (ren-ty sucr A) B
   → Crcn Δ Σ A (`∀ B)
 ℐ_ : ∀{Δ}{Σ : TyBinds Δ}{A : Type (suc Δ)} {B : Type Δ}
   → Crcn (suc Δ) (typ-b Σ) A (ren-ty sucr B)
   → Crcn Δ Σ (`∀ A) B
 _↓ : ∀{Δ}{Σ : TyBinds Δ}{A : Type Δ}
   → (X : Var Δ)
   → get X Σ ≡ just A
   → Crcn Δ Σ A (` X)
 _↑ : ∀{Δ}{Σ : TyBinds Δ}{A : Type Δ}
   → (X : Var Δ)
   → get X Σ ≡ just A
   → Crcn Δ Σ (` X) A
 _! : ∀{Δ}{Σ : TyBinds Δ}
   → (G : Grnd Δ)
   → Crcn Δ Σ ⌈ G ⌉ ★
 _`? : ∀{Δ}{Σ : TyBinds Δ}
   → (H : Grnd Δ)
   → Crcn Δ Σ ★ ⌈ H ⌉

rename-crcn : ∀{Δ₁ Δ₂}{Σ₁ : TyBinds Δ₁}{Σ₂ : TyBinds Δ₂}{A B}
  → (ρ : TyRen Δ₁ Δ₂) → Crcn Δ₁ Σ₁ A B → Crcn Δ₂ Σ₂ (ren-ty ρ A) (ren-ty ρ B)
rename-crcn ρ id = id
rename-crcn ρ (c ↦ d) = rename-crcn ρ c ↦ rename-crcn ρ d
rename-crcn ρ (c ⨟ d) = rename-crcn ρ c ⨟ rename-crcn ρ d
rename-crcn ρ (`∀ c) = `∀ rename-crcn (extr ρ) c
rename-crcn ρ (𝒢 c) = 𝒢 {!!}
rename-crcn ρ (ℐ c) = ℐ {!!}
rename-crcn {Δ₁}{Δ₂} ρ ((X ↓) X:=A) =
  let Y : Var Δ₂
      Y = ren-var ρ X
  in {!!}
rename-crcn ρ ((X ↑) X:=A) = {!!}
rename-crcn ρ (G !) = {!!}
rename-crcn ρ (H `?) = {!!}
