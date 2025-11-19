{-# OPTIONS --rewriting #-}

module PolyBlame.TypeSubst where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.List.Properties using (map-∘)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (_∨_; _≤_)
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
--open import Data.Fin
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Bool
open import Relation.Nullary using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import PolyBlame.Types

{-- Substituting type variables in types -}

infixr 7 _→ᵗ_
_→ᵗ_ : TyCtx → TyCtx → Set
Δ₁ →ᵗ Δ₂ = TyVar Δ₁ → Type Δ₂

extsᵗ : ∀{Δ₁ Δ₂} → (Δ₁ →ᵗ Δ₂) → ((Δ₁ ,typ) →ᵗ (Δ₂ ,typ))
extsᵗ σ Zᵗ = ` Zᵗ
extsᵗ σ (Sᵗ X) = ⇑ᵗ (σ X)

subᵗ : ∀{Δ₁ Δ₂} → (Δ₁ →ᵗ Δ₂) → Type Δ₁ → Type Δ₂
subᵗ σ `ℕ = `ℕ
subᵗ σ ★ = ★
subᵗ σ (` X) = σ X
subᵗ σ (A ⇒ B) = subᵗ σ A ⇒ subᵗ σ B
subᵗ σ (`∀ A) = `∀ subᵗ (extsᵗ σ) A

ids : ∀{Δ} → Δ →ᵗ Δ
ids = `_

infixr 6 _•ˢ_
_•ˢ_ : ∀{Δ₁ Δ₂} → Type Δ₂ → (Δ₁ →ᵗ Δ₂) → ((Δ₁ ,typ) →ᵗ Δ₂)
(A •ˢ σ) Zᵗ = A
(A •ˢ σ) (Sᵗ X) = σ X

infix 6 _[_]ˢ
_[_]ˢ : ∀{Δ} → Type (Δ ,typ) → Type Δ → Type Δ
A [ B ]ˢ = subᵗ (B •ˢ ids) A

abstract
  infixr 5 _⨟ᵀ_
  _⨟ᵀ_ : ∀{Δ₁ Δ₂ Δ₃ : TyCtx} → (Δ₁ →ᵗ Δ₂) → (Δ₂ →ᵗ Δ₃) → (Δ₁ →ᵗ Δ₃)
  (σ ⨟ᵀ τ) x = subᵗ τ (σ x)

  seqᵗ-def : ∀{Δ₁ Δ₂ Δ₃} (σ : Δ₁ →ᵗ Δ₂) → (τ : Δ₂ →ᵗ Δ₃) (x : TyVar Δ₁)
    → (σ ⨟ᵀ τ) x ≡ subᵗ τ (σ x)
  seqᵗ-def σ τ x = refl
  {-# REWRITE seqᵗ-def #-}

abstract
  r2s : ∀{Δ Δ′} → (Δ ⇒ᵗ Δ′) → (Δ →ᵗ Δ′)
  r2s ρ = λ X → ` ρ X

  r2s-def : ∀{Δ Δ′}{ρ : Δ ⇒ᵗ Δ′}{X : TyVar Δ}
    → (r2s ρ) X ≡ ` ρ X
  r2s-def = refl
  {-# REWRITE r2s-def #-}

exts-r2s : ∀{Δ Δ′}{ρ : Δ ⇒ᵗ Δ′} → extsᵗ (r2s ρ) ≡ r2s (extᵗ ρ)
exts-r2s{Δ}{Δ′}{ρ} = extensionality aux
  where aux : (x : TyVar (Δ ,typ)) → extsᵗ (r2s ρ) x ≡ r2s (extᵗ ρ) x
        aux Zᵗ = refl
        aux (Sᵗ x) = refl
{-# REWRITE exts-r2s #-}

ren-r2s : ∀{Δ Δ′}{ρ : Δ ⇒ᵗ Δ′ }{A} → renᵗ ρ A ≡ subᵗ (r2s ρ) A
ren-r2s {A = `ℕ} = refl
ren-r2s {A = ★} = refl
ren-r2s {A = ` X} = refl
ren-r2s {A = A ⇒ B} = cong₂ _⇒_ (ren-r2s{A = A}) (ren-r2s{A = B})
ren-r2s {ρ = ρ}{A = `∀ A} = cong `∀_ (ren-r2s{ρ = extᵗ ρ}{A = A})
{-# REWRITE ren-r2s #-}

exts-r2s-sub : ∀{Δ₁ Δ₂ Δ₃}{ρ : Δ₁ ⇒ᵗ Δ₂}{τ : Δ₂ →ᵗ Δ₃}
  → extsᵗ (r2s ρ) ⨟ᵀ extsᵗ τ ≡ extsᵗ (r2s ρ ⨟ᵀ τ)
exts-r2s-sub{Δ₁}{Δ₂}{Δ₃} {ρ}{τ} = extensionality (aux{ρ}{τ})
  where
  aux : ∀{ρ : Δ₁ ⇒ᵗ Δ₂}{τ : Δ₂ →ᵗ Δ₃}(X : TyVar (Δ₁ ,typ)) →
         (extsᵗ (r2s ρ) ⨟ᵀ extsᵗ τ) X ≡ extsᵗ (r2s ρ ⨟ᵀ τ) X
  aux Zᵗ = refl
  aux (Sᵗ X) = refl
{-# REWRITE exts-r2s-sub #-}

ren-subᵗ : ∀{Δ₁ Δ₂ Δ₃} {ρ : Δ₁ ⇒ᵗ Δ₂ }{τ : Δ₂ →ᵗ Δ₃}{A : Type Δ₁}
  → subᵗ τ (subᵗ (r2s ρ) A) ≡ subᵗ (r2s ρ ⨟ᵀ τ) A
ren-subᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {τ} {`ℕ} = refl
ren-subᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {τ} {★} = refl
ren-subᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {τ} {` X} = refl
ren-subᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {τ} {A ⇒ B} =
  cong₂ _⇒_ (ren-subᵗ{Δ₁} {Δ₂} {Δ₃} {ρ} {τ} {A})
            (ren-subᵗ{Δ₁} {Δ₂} {Δ₃} {ρ} {τ} {B})
ren-subᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {τ} {`∀ A} =
  cong `∀_ (ren-subᵗ{ρ = extᵗ ρ}{τ = extsᵗ τ}{A = A})
{-# REWRITE ren-subᵗ #-}

exts-seq-r2s : ∀{Δ₁ Δ₂ Δ₃}{σ : Δ₁ →ᵗ Δ₂}{ρ : Δ₂ ⇒ᵗ Δ₃}
  → extsᵗ σ ⨟ᵀ r2s (extᵗ ρ) ≡ extsᵗ (σ ⨟ᵀ r2s ρ)
exts-seq-r2s{Δ₁}{Δ₂}{Δ₃}{σ}{ρ} = extensionality (aux{σ}{ρ})
  where
  aux : ∀{σ : Δ₁ →ᵗ Δ₂}{ρ : Δ₂ ⇒ᵗ Δ₃}(x : TyVar (Δ₁ ,typ)) →
      subᵗ (λ z → ` extᵗ ρ z) (extsᵗ σ x) ≡ extsᵗ (σ ⨟ᵀ r2s ρ) x
  aux Zᵗ = refl
  aux (Sᵗ x) = refl
{-# REWRITE exts-seq-r2s #-}

sub-renᵗ : ∀{Δ₁ Δ₂ Δ₃}{ρ : Δ₂ ⇒ᵗ Δ₃}{σ : Δ₁ →ᵗ Δ₂}{A : Type Δ₁}
  → subᵗ (r2s ρ) (subᵗ σ A) ≡ subᵗ (σ ⨟ᵀ r2s ρ) A
sub-renᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {σ} {`ℕ} = refl
sub-renᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {σ} {★} = refl
sub-renᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {σ} {` X} = refl
sub-renᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {σ} {A ⇒ B} =
  cong₂ _⇒_ (sub-renᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {σ} {A})
            (sub-renᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {σ} {B})
sub-renᵗ {Δ₁} {Δ₂} {Δ₃} {ρ} {σ} {`∀ A} =
  cong `∀_ (sub-renᵗ{ρ = extᵗ ρ}{σ = extsᵗ σ}{A = A})
{-# REWRITE sub-renᵗ #-}

exts-seq : ∀{Δ₁ Δ₂ Δ₃}{σ : Δ₁ →ᵗ Δ₂}{τ : Δ₂ →ᵗ Δ₃}
  → (extsᵗ σ) ⨟ᵀ (extsᵗ τ) ≡ extsᵗ (σ ⨟ᵀ τ)
exts-seq{Δ₁}{Δ₂}{Δ₃}{σ}{τ} = extensionality (aux{σ}{τ})
  where
  aux : ∀{σ : Δ₁ →ᵗ Δ₂}{τ : Δ₂ →ᵗ Δ₃}(X : TyVar (Δ₁ ,typ)) →
         (extsᵗ σ ⨟ᵀ extsᵗ τ) X ≡ extsᵗ (σ ⨟ᵀ τ) X
  aux Zᵗ = refl
  aux{σ}{τ} (Sᵗ X) = refl
{-# REWRITE exts-seq #-}

sub-subᵗ : ∀{Δ₁ Δ₂ Δ₃}{σ : Δ₁ →ᵗ Δ₂}{τ : Δ₂ →ᵗ Δ₃}{A : Type Δ₁}
  → subᵗ τ (subᵗ σ A) ≡ subᵗ (σ ⨟ᵀ τ) A
sub-subᵗ {Δ₁} {Δ₂} {Δ₃} {σ} {τ} {`ℕ} = refl
sub-subᵗ {Δ₁} {Δ₂} {Δ₃} {σ} {τ} {★} = refl
sub-subᵗ {Δ₁} {Δ₂} {Δ₃} {σ} {τ} {` X} = refl
sub-subᵗ {Δ₁} {Δ₂} {Δ₃} {σ} {τ} {A ⇒ B} =
  cong₂ _⇒_ (sub-subᵗ{σ = σ}{τ}{A}) (sub-subᵗ{σ = σ}{τ}{B})
sub-subᵗ {Δ₁} {Δ₂} {Δ₃} {σ} {τ} {`∀ A} =
  cong `∀_ (sub-subᵗ{σ = extsᵗ σ}{extsᵗ τ}{A})
{-# REWRITE sub-subᵗ #-}

sub-ids : ∀ {Δ}{A : Type Δ} → subᵗ ids A ≡ A
sub-ids {Δ} {`ℕ} = refl
sub-ids {Δ} {★} = refl
sub-ids {Δ} {` X} = refl
sub-ids {Δ} {A ⇒ B} = cong₂ _⇒_ sub-ids sub-ids
sub-ids {Δ} {`∀ A} = cong `∀_ sub-ids
{-# REWRITE sub-ids #-}

r2s-• : ∀{Δ Δ′}{Y : TyVar Δ′}{ρ : Δ ⇒ᵗ Δ′}
  → r2s (Y •ᵗ ρ) ≡ ` Y •ˢ r2s ρ
r2s-• = extensionality λ { Zᵗ → refl ; (Sᵗ x) → refl}
--{-# REWRITE r2s-• #-}

r2s-id : ∀{Δ}
  → r2s{Δ}{Δ} idᵗ ≡ ids
r2s-id = extensionality λ { Zᵗ → refl ; (Sᵗ x) → refl}
--{-# REWRITE r2s-id #-}

r2s-seq : ∀{Δ₁ Δ₂ Δ₃}{ρ₁ : Δ₁ ⇒ᵗ Δ₂}{ρ₂ : Δ₂ ⇒ᵗ Δ₃}
  → (r2s ρ₁ ⨟ᵀ r2s ρ₂) ≡ r2s (ρ₁ ⨟ᵗ ρ₂)
r2s-seq{Δ₁}{Δ₂}{Δ₃}{ρ₁}{ρ₂} = extensionality λ { Zᵗ → refl ; (Sᵗ x) → refl}
{-# REWRITE r2s-seq #-}
