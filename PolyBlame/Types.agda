{-# OPTIONS --rewriting #-}

module PolyBlame.Types where

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

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  extensionality : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁ }{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

{--- Type variables and their Contexts ---}

data TyCtx : Set 
data Type : TyCtx → Set 

infixl 5 _,typ

data TyCtx where
  ∅ : TyCtx
  _,typ : TyCtx → TyCtx

data TyVar : (Δ : TyCtx) → Set where
  Zᵗ : ∀{Δ} → TyVar (Δ ,typ)
  Sᵗ : ∀{Δ}
     → TyVar Δ
       --------------
     → TyVar (Δ ,typ)

_≡ᵗ_ : ∀{Δ} → (X : TyVar Δ) → (Y : TyVar Δ) → Dec (X ≡ Y)
Zᵗ ≡ᵗ Zᵗ = Agda.Builtin.Bool.Bool.true Relation.Nullary.because
            Relation.Nullary.ofʸ refl
Zᵗ ≡ᵗ Sᵗ Y = no λ ()
Sᵗ X ≡ᵗ Zᵗ = no λ ()
Sᵗ X ≡ᵗ Sᵗ Y
    with X ≡ᵗ Y
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl}

{- Renaming Type Variables -}

infixr 7 _⇒ᵗ_
_⇒ᵗ_ : TyCtx → TyCtx → Set
Δ₁ ⇒ᵗ Δ₂ = TyVar Δ₁ → TyVar Δ₂

idᵗ : ∀{Δ} → Δ ⇒ᵗ Δ
idᵗ = λ x → x

infixr 6 _•ᵗ_
_•ᵗ_ : ∀{Δ₁ Δ₂} → TyVar Δ₂ → (Δ₁ ⇒ᵗ Δ₂) → ((Δ₁ ,typ) ⇒ᵗ Δ₂)
(Y •ᵗ ρ) Zᵗ = Y
(Y •ᵗ ρ) (Sᵗ X) = ρ X

extᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵗ Δ₂) → ((Δ₁ ,typ) ⇒ᵗ (Δ₂ ,typ))
extᵗ ρ Zᵗ = Zᵗ
extᵗ ρ (Sᵗ X) = Sᵗ (ρ X)

⟰ᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵗ Δ₂) → (Δ₁ ⇒ᵗ (Δ₂ ,typ))
⟰ᵗ ρ x = Sᵗ (ρ x)

abstract
  infixr 5 _⨟ᵗ_
  _⨟ᵗ_ : ∀{Δ₁ Δ₂ Δ₃ : TyCtx} → (Δ₁ ⇒ᵗ Δ₂) → (Δ₂ ⇒ᵗ Δ₃) → (Δ₁ ⇒ᵗ Δ₃)
  (ρ₁ ⨟ᵗ ρ₂) x = ρ₂ (ρ₁ x)

  seq-def : ∀ {Δ₁ Δ₂ Δ₃ : TyCtx} (σ : Δ₁ ⇒ᵗ Δ₂) (τ : Δ₂ ⇒ᵗ Δ₃) x → (σ ⨟ᵗ τ) x ≡ τ (σ x)
  seq-def σ τ x = refl
  {-# REWRITE seq-def #-}

suc-seq-cons : ∀{Δ₁ Δ₂ : TyCtx} (ρ : Δ₁ ⇒ᵗ Δ₂)(Y : TyVar Δ₂)
  → Sᵗ ⨟ᵗ (Y •ᵗ ρ) ≡ ρ
suc-seq-cons ρ Y = refl  
-- {-# REWRITE suc-seq-cons #-}

cons-zero-suc-id : ∀{Δ : TyCtx} → Zᵗ{Δ} •ᵗ Sᵗ ≡ idᵗ
cons-zero-suc-id{Δ} = extensionality G
  where G : (x : TyVar (Δ ,typ)) → (Zᵗ •ᵗ Sᵗ) x ≡ idᵗ x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE cons-zero-suc-id #-}

cons-seq-dist : ∀{Δ₁}{Δ₂}{Δ₃}{Y}{ρ₁ : Δ₁ ⇒ᵗ Δ₂}{ρ₂ : Δ₂ ⇒ᵗ Δ₃}
   → (Y •ᵗ ρ₁) ⨟ᵗ ρ₂ ≡ (ρ₂ Y •ᵗ (ρ₁ ⨟ᵗ ρ₂))
cons-seq-dist {Δ₁}{Δ₂}{Δ₃}{Y}{ρ₁}{ρ₂} = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
             (Y •ᵗ ρ₁ ⨟ᵗ ρ₂) x ≡ (ρ₂ Y •ᵗ (ρ₁ ⨟ᵗ ρ₂)) x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE cons-seq-dist #-}

ext-ren : ∀{Δ₁}{Δ₂}{ρ : Δ₁ ⇒ᵗ Δ₂} → Zᵗ •ᵗ (⟰ᵗ ρ) ≡ extᵗ ρ
ext-ren {Δ₁}{Δ₂}{ρ} = extensionality G
  where G : (X : TyVar (Δ₁ ,typ)) → (Zᵗ •ᵗ ⟰ᵗ ρ) X ≡ extᵗ ρ X
        G Zᵗ = refl
        G (Sᵗ X) = refl

ext-seq-dist : ∀ {Δ₁}{Δ₂}{Δ₃} (ρ₁ : Δ₁ ⇒ᵗ Δ₂)(ρ₂ : Δ₂ ⇒ᵗ Δ₃)
  → (extᵗ ρ₁) ⨟ᵗ (extᵗ ρ₂) ≡ extᵗ (ρ₁ ⨟ᵗ ρ₂)
ext-seq-dist {Δ₁}{Δ₂}{Δ₃} ρ₁ ρ₂ = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
           (extᵗ ρ₁ ⨟ᵗ extᵗ ρ₂) x ≡ extᵗ (ρ₁ ⨟ᵗ ρ₂) x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE ext-seq-dist #-}

seq-id : ∀{Δ₁ Δ₂}{ρ : Δ₁ ⇒ᵗ Δ₂} → (idᵗ ⨟ᵗ ρ) ≡ ρ
seq-id {Δ₁}{Δ₂}{ρ} = refl
{-# REWRITE seq-id #-}

id-seq : ∀{Δ₁ Δ₂}{ρ : Δ₁ ⇒ᵗ Δ₂} → (ρ ⨟ᵗ idᵗ) ≡ ρ
id-seq {Δ₁}{Δ₂}{ρ} = refl
{-# REWRITE id-seq #-}

{-----------     Types     -----------------}

data Type where
  `ℕ  : ∀{Δ} → Type Δ
  ★   : ∀{Δ} → Type Δ
  `_ : ∀{Δ} → (x : TyVar Δ) → Type Δ
  _⇒_ : ∀{Δ} → Type Δ → Type Δ → Type Δ
  `∀_  : ∀{Δ} → Type (Δ ,typ) → Type Δ

{- Renaming type variables in types -}

renᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵗ Δ₂) → Type Δ₁ → Type Δ₂
renᵗ ρ (A ⇒ B) = (renᵗ ρ A) ⇒ (renᵗ ρ B)
renᵗ ρ `ℕ = `ℕ
renᵗ ρ ★ = ★
renᵗ ρ (`∀ A) = `∀ (renᵗ (extᵗ ρ) A)
renᵗ ρ (` X) = ` (ρ X)

infix 6 _[_]ᵗ
_[_]ᵗ : ∀{Δ} → Type (Δ ,typ) → TyVar Δ → Type Δ
A [ X ]ᵗ = renᵗ (X •ᵗ idᵗ) A

⇑ᵗ : ∀{Δ} → Type Δ → Type (Δ ,typ)
⇑ᵗ A = renᵗ Sᵗ A

ren-ren : ∀ {Δ₁}{Δ₂}{Δ₃} (ρ₁ : Δ₁ ⇒ᵗ Δ₂)(ρ₂ : Δ₂ ⇒ᵗ Δ₃){A}
  → renᵗ ρ₂ (renᵗ ρ₁ A) ≡ renᵗ (ρ₁ ⨟ᵗ ρ₂) A
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {`ℕ} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {★} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {` X} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {A ⇒ B} =
   cong₂ _⇒_ (ren-ren ρ₁ ρ₂) (ren-ren ρ₁ ρ₂)
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {`∀ A} = cong `∀_ G
  where G : renᵗ (extᵗ ρ₂) (renᵗ (extᵗ ρ₁) A) ≡ renᵗ (extᵗ (ρ₁ ⨟ᵗ ρ₂)) A
        G = ren-ren (extᵗ ρ₁) (extᵗ ρ₂)
{-# REWRITE ren-ren #-}

extᵗ-id : ∀{Δ} → extᵗ (idᵗ{Δ}) ≡ idᵗ
extᵗ-id {Δ} = extensionality G
  where G : (x : TyVar (Δ ,typ)) → extᵗ idᵗ x ≡ idᵗ x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE extᵗ-id #-}

renᵗ-id : ∀{Δ}{A : Type Δ} → renᵗ idᵗ A ≡ A
renᵗ-id {Δ} {`ℕ} = refl
renᵗ-id {Δ} {★} = refl
renᵗ-id {Δ} {` x} = refl
renᵗ-id {Δ} {A ⇒ B} = cong₂ _⇒_ renᵗ-id renᵗ-id
renᵗ-id {Δ} {`∀ A} = cong `∀_ renᵗ-id
{-# REWRITE renᵗ-id #-}

ext-seq-cons : ∀{Δ₁ Δ₂ Δ₃}{X}{ρ₁ : Δ₁ ⇒ᵗ Δ₂}{ρ₂ : Δ₂ ⇒ᵗ Δ₃}
  → (extᵗ ρ₁) ⨟ᵗ (X •ᵗ ρ₂) ≡ X •ᵗ (ρ₁ ⨟ᵗ ρ₂)
ext-seq-cons {Δ₁}{Δ₂}{Δ₃}{X}{ρ₁}{ρ₂} = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
              (X •ᵗ ρ₂) (extᵗ ρ₁ x) ≡ (X •ᵗ (ρ₁ ⨟ᵗ ρ₂)) x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE ext-seq-cons #-}

ext-suc-cons : ∀{Δ₁}{A : Type Δ₁} → extᵗ{Δ₁ = Δ₁} Sᵗ ⨟ᵗ (Zᵗ •ᵗ idᵗ) ≡ idᵗ
ext-suc-cons = refl

BindCtx : TyCtx → Set
BindCtx Δ = List (TyVar Δ × Type Δ)

{-- Looking up type variable bindings --}

data _∋_:=_ : ∀{Δ : TyCtx} → BindCtx Δ → TyVar Δ → Type Δ → Set where
  Zᵇ : ∀ {Δ}{Σ : BindCtx Δ}{X : TyVar Δ}{A : Type Δ}
    → ((X , A) ∷ Σ) ∋ X := A
  Sᵇ : ∀ {Δ}{Σ : BindCtx Δ}{X Y : TyVar Δ}{A B : Type Δ}
    → Σ ∋ X := A
    → ((Y , B) ∷ Σ) ∋ X := A

data unique : ∀{Δ : TyCtx} → BindCtx Δ → Set where
  Umt : ∀{Δ} → unique{Δ} []
  Ucons : ∀{Δ}{Σ : BindCtx Δ}{X}{A}
    → unique Σ
    → (∀ B → Σ ∋ X := B → ⊥)
    → unique ((X , A) ∷ Σ)

lookup-unique : ∀{Δ : TyCtx}{Σ : BindCtx Δ}{X}{A B}
  → (a : Σ ∋ X := A)
  → (b : Σ ∋ X := B)
  → unique Σ
  → A ≡ B
lookup-unique {Δ} {(Y , C) ∷ Σ} {X} {A} {B} Zᵇ Zᵇ (Ucons u x) = refl
lookup-unique {Δ} {(Y , C) ∷ Σ} {X} {A} {B} Zᵇ (Sᵇ b) (Ucons u nolook) = ⊥-elim (nolook B b)
lookup-unique {Δ} {(Y , C) ∷ Σ} {X} {A} {B} (Sᵇ a) Zᵇ (Ucons u nolook) = ⊥-elim (nolook A a)
lookup-unique {Δ} {(Y , C) ∷ Σ} {X} {A} {B} (Sᵇ a) (Sᵇ b) (Ucons u nolook) = lookup-unique a b u

{----- Ground Types -----}

data Grnd : TyCtx → Set where
  ★⇒★ : ∀{Δ} → Grnd Δ
  `ℕ  : ∀{Δ} → Grnd Δ
  `_ : ∀{Δ} → TyVar Δ → Grnd Δ

⌈_⌉ : ∀{Δ} → Grnd Δ → Type Δ
⌈ ★⇒★ ⌉ = ★ ⇒ ★
⌈ `ℕ ⌉ = `ℕ
⌈ ` X ⌉ = ` X

_≡ᵍ_ : ∀{Δ} → (G : Grnd Δ) → (H : Grnd Δ) → Dec (G ≡ H)
★⇒★ ≡ᵍ ★⇒★ = yes refl
★⇒★ ≡ᵍ `ℕ = no λ ()
★⇒★ ≡ᵍ (` X) = no λ ()
`ℕ ≡ᵍ ★⇒★ = no λ ()
`ℕ ≡ᵍ `ℕ = yes refl
`ℕ ≡ᵍ (` X) = no λ ()
(` X) ≡ᵍ ★⇒★ = no λ ()
(` X) ≡ᵍ `ℕ = no λ ()
(` X) ≡ᵍ (` Y)
    with X ≡ᵗ Y
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl}

ren-grnd : ∀{Δ₁ Δ₂} → Δ₁ ⇒ᵗ Δ₂ → Grnd Δ₁ → Grnd Δ₂
ren-grnd ρ ★⇒★ = ★⇒★
ren-grnd ρ `ℕ = `ℕ
ren-grnd ρ (` X) = ` (ρ X)

{--- Auxilliary notions regarding BindCtx  ---}

renᵇ : ∀{Δ₁ Δ₂} → Δ₁ ⇒ᵗ Δ₂ → TyVar Δ₁ × Type Δ₁ → TyVar Δ₂ × Type Δ₂
renᵇ ρ (X , A) = ρ X , renᵗ ρ A

⤊ : ∀{Δ} → BindCtx Δ → BindCtx (Δ ,typ)
⤊ = map (renᵇ Sᵗ)

{- The prefix/extension relation on BindCtx. -}
infix 3 _↝_
data _↝_ : ∀{Δ} → BindCtx Δ → BindCtx Δ → Set where
  ↝-extend : ∀ {Δ}{Σ : BindCtx Δ}{X}{A : Type Δ}
     → Σ ↝ (X , A) ∷ Σ
     
  ↝-refl : ∀ {Δ}{Σ : BindCtx Δ}
     → Σ ↝ Σ
     
  ↝-trans : ∀ {Δ}{Σ₁ Σ₂ Σ₃ : BindCtx Δ}
    → Σ₁ ↝ Σ₂
    → Σ₂ ↝ Σ₃
      --------
    → Σ₁ ↝ Σ₃

ren-bind-map : ∀{Δ Δ′}{Σ₁ Σ₂ : BindCtx Δ}
   (ρ : Δ ⇒ᵗ Δ′)
  → Σ₁ ↝ Σ₂
  → map (renᵇ ρ) Σ₁ ↝ map (renᵇ ρ) Σ₂
ren-bind-map ρ ↝-extend = ↝-extend
ren-bind-map ρ ↝-refl = ↝-refl
ren-bind-map ρ (↝-trans s₁ s₂) =
   ↝-trans (ren-bind-map ρ s₁) (ren-bind-map ρ s₂)

renᵇ-∘ : ∀{Δ₁ Δ₂ Δ₃}{x : TyVar Δ₁ × Type Δ₁} → (ρ₁ : Δ₁ ⇒ᵗ Δ₂) → (ρ₂ : Δ₂ ⇒ᵗ Δ₃)
  → ((renᵇ ρ₂) ∘ (renᵇ ρ₁)) x ≡ (renᵇ (ρ₁ ⨟ᵗ ρ₂)) x
renᵇ-∘ {Δ₁}{Δ₂}{Δ₃}{x} ρ₁ ρ₂ = refl

map-renᵇ-id : ∀{Δ} (Σ : BindCtx Δ)
  → map (renᵇ idᵗ) Σ ≡ Σ
map-renᵇ-id [] = refl
map-renᵇ-id ((X , A) ∷ Σ) = cong₂ _∷_ refl (map-renᵇ-id Σ)
{-# REWRITE map-renᵇ-id #-}

{---- extension preserves unique  ----}

helper : ∀{Δ}{Σ : BindCtx Δ}{B : Type (Δ ,typ)}{X}
  → map (renᵇ Sᵗ) Σ ∋ Sᵗ X := B
  → ((A : Type Δ) → Σ ∋ X := A → ⊥)
  → ⊥
helper {Δ} {(Y , C) ∷ Σ′} Zᵇ nl = nl C Zᵇ
helper {Δ} {(Y , C) ∷ Σ′} (Sᵇ ∋Sx) nl = helper ∋Sx (λ A x → nl A (Sᵇ x))

unique-⤊ : ∀ {Δ}{Σ : BindCtx Δ} → unique Σ → unique (⤊ Σ)
unique-⤊ Umt = Umt
unique-⤊ (Ucons u nolook) = Ucons (unique-⤊ u) λ { B y → helper y nolook }

suc-bind-zero : ∀{Δ}{Σ : BindCtx Δ}{C}
  → map (renᵇ Sᵗ) Σ ∋ Zᵗ := C
  → ⊥
suc-bind-zero {Δ} {(Y , A) ∷ Σ′} (Sᵇ ∋Z) = suc-bind-zero ∋Z

unique-extend : ∀ {Δ}{A}
  → (Σ : BindCtx Δ)
  → unique Σ
  → unique ((Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ)
unique-extend [] u = Ucons Umt λ { B ()}
unique-extend ((X , B) ∷ Σ) (Ucons u nolook) =
  Ucons (Ucons (unique-⤊ u) λ {C x → helper x nolook})
    λ { C (Sᵇ ∋Z) → suc-bind-zero ∋Z}

{-- Precision --}

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

{-- Consistency --}

infixr 6 _∣_⊢_∼_
data _∣_⊢_∼_ : (Δ : TyCtx) → SubCtx Δ → Type Δ → Type Δ → Set where
  ℕ∼ℕ : ∀{Δ}{Ψ}
      ------------------
     → Δ ∣ Ψ ⊢ `ℕ ∼ `ℕ
     
  X∼X : ∀{Δ}{Ψ}{X}
      --------------------
     → Δ ∣ Ψ ⊢ ` X ∼ ` X

  ★∼★ : ∀{Δ}{Ψ}
      ----------------
     → Δ ∣ Ψ ⊢ ★ ∼ ★

  ★∼X : ∀{Δ}{Ψ}{X : TyVar Δ}
     → Ψ ∋ˢ X
      ------------------
     → Δ ∣ Ψ ⊢ ★ ∼ ` X

  X∼★ : ∀{Δ}{Ψ}{X : TyVar Δ}
     → Ψ ∋ˢ X
      -----------------
     → Δ ∣ Ψ ⊢ ` X ∼ ★

  ★∼ℕ : ∀{Δ}{Ψ}
     --------------------
     → Δ ∣ Ψ ⊢ ★ ∼ `ℕ

  ℕ∼★ : ∀{Δ}{Ψ}
     ------------------
     → Δ ∣ Ψ ⊢ `ℕ ∼ ★

  ⇒∼★ : ∀{Δ}{Ψ}{A B}
     → Δ ∣ Ψ ⊢ A ∼ ★
     → Δ ∣ Ψ ⊢ B ∼ ★
       ------------------
     → Δ ∣ Ψ ⊢ A ⇒ B ∼ ★

  ★∼⇒ : ∀{Δ}{Ψ}{A B}
     → Δ ∣ Ψ ⊢ ★ ∼ A
     → Δ ∣ Ψ ⊢ ★ ∼ B
       ------------------
     → Δ ∣ Ψ ⊢ ★ ∼ A ⇒ B

  ⇒∼⇒ : ∀{Δ}{Ψ}{A B C D}
     →  Δ ∣ Ψ ⊢ A ∼ C
     →  Δ ∣ Ψ ⊢ B ∼ D
      ------------------------
     → Δ ∣ Ψ ⊢ A ⇒ B ∼ C ⇒ D

  ∀∼∀ : ∀{Δ}{Ψ}{A B}
     → (Δ ,typ) ∣ (Ψ , false) ⊢ A ∼ B
      --------------------------------
     → Δ ∣ Ψ ⊢ `∀ A ∼ `∀ B

  ∼∀ : ∀{Δ}{Ψ}{A B}
     → (Δ ,typ) ∣ (Ψ , true) ⊢ ⇑ᵗ A ∼ B
      ----------------------------------
     → Δ ∣ Ψ ⊢ A ∼ `∀ B

  ∀∼ : ∀{Δ}{Ψ}{A B}
     → (Δ ,typ) ∣ (Ψ , true) ⊢ A ∼ ⇑ᵗ B
      ----------------------------------
     → Δ ∣ Ψ ⊢ `∀ A ∼ B

_⊑_ : ∀{Δ} → SubCtx Δ → SubCtx Δ → Set
∅ ⊑ ∅ = ⊤
(Ψ , b) ⊑ (Ψ′ , b′) = (Ψ ⊑ Ψ′) × (b ≤ b′)

_⊔_ : ∀{Δ} → SubCtx Δ → SubCtx Δ → SubCtx Δ
∅ ⊔ ∅ = ∅
(Ψ , b) ⊔ (Ψ′ , b′) = (Ψ ⊔ Ψ′) , b ∨ b′

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

less-refl : ∀{Δ}(Ψ : SubCtx Δ)
  → Ψ ⊑ Ψ
less-refl ∅ = tt
less-refl (Ψ , b) = less-refl Ψ , _≤_.b≤b

less-lub-left : ∀{Δ}(Ψ Ψ′ : SubCtx Δ)
  → Ψ ⊑ (Ψ ⊔ Ψ′)
less-lub-left {Δ} ∅ ∅ = tt
less-lub-left {Δ} (Ψ , b) (Ψ′ , b′) = (less-lub-left Ψ Ψ′) , ≤-or-left b b′

less-lub-right : ∀{Δ}(Ψ Ψ′ : SubCtx Δ)
  → Ψ′ ⊑ (Ψ ⊔ Ψ′)
less-lub-right {Δ} ∅ ∅ = tt
less-lub-right {Δ} (Ψ , b) (Ψ′ , b′) = (less-lub-right Ψ Ψ′) , ≤-or-right b b′

weaken-∋ : ∀{Δ}{Ψ Ψ′}{X : TyVar Δ}
  → Ψ ⊑ Ψ′
  → Ψ ∋ˢ X
  → Ψ′ ∋ˢ X
weaken-∋ {Ψ′ = Ψ′ , true} Ψ⊑Ψ′ Zˢ = Zˢ
weaken-∋ {Ψ′ = Ψ′ , b′} Ψ⊑Ψ′ (Sˢ ∋X) = Sˢ (weaken-∋ (Ψ⊑Ψ′ .proj₁) ∋X)

weaken-⊑ : ∀{Δ}{Ψ Ψ′}{A B : Type Δ}
  → Ψ ⊑ Ψ′
  → Δ ∣ Ψ ⊢ A ⊑ B
  → Δ ∣ Ψ′ ⊢ A ⊑ B
weaken-⊑ Ψ⊑Ψ′ ℕ⊑ℕ = ℕ⊑ℕ
weaken-⊑ Ψ⊑Ψ′ X⊑X = X⊑X
weaken-⊑ Ψ⊑Ψ′ ★⊑★ = ★⊑★
weaken-⊑ Ψ⊑Ψ′ (★⊑X ∋X) = ★⊑X (weaken-∋ Ψ⊑Ψ′ ∋X)
weaken-⊑ Ψ⊑Ψ′ ★⊑ℕ = ★⊑ℕ
weaken-⊑ Ψ⊑Ψ′ (★⊑⇒ ★⊑A ★⊑B) = ★⊑⇒ (weaken-⊑ Ψ⊑Ψ′ ★⊑A) (weaken-⊑ Ψ⊑Ψ′ ★⊑B)
weaken-⊑ Ψ⊑Ψ′ (⇒⊑⇒ A⊑C B⊑D) = ⇒⊑⇒ (weaken-⊑ Ψ⊑Ψ′ A⊑C) (weaken-⊑ Ψ⊑Ψ′ B⊑D)
weaken-⊑ Ψ⊑Ψ′ (∀⊑∀ A⊑B) = ∀⊑∀ (weaken-⊑ (Ψ⊑Ψ′ , _≤_.b≤b) A⊑B)
weaken-⊑ Ψ⊑Ψ′ (⊑∀ A⊑B) = ⊑∀ (weaken-⊑ (Ψ⊑Ψ′ , _≤_.b≤b) A⊑B)

weaken-∼ : ∀{Δ}{Ψ Ψ′}{A B : Type Δ}
  → Ψ ⊑ Ψ′
  → Δ ∣ Ψ ⊢ A ∼ B
  → Δ ∣ Ψ′ ⊢ A ∼ B
weaken-∼ Ψ⊑Ψ′ ℕ∼ℕ = ℕ∼ℕ
weaken-∼ Ψ⊑Ψ′ X∼X = X∼X
weaken-∼ Ψ⊑Ψ′ ★∼★ = ★∼★
weaken-∼ Ψ⊑Ψ′ (★∼X ∋X) = ★∼X (weaken-∋ Ψ⊑Ψ′ ∋X)
weaken-∼ Ψ⊑Ψ′ (X∼★ ∋X) = X∼★ (weaken-∋ Ψ⊑Ψ′ ∋X)
weaken-∼ Ψ⊑Ψ′ ★∼ℕ = ★∼ℕ
weaken-∼ Ψ⊑Ψ′ ℕ∼★ = ℕ∼★
weaken-∼ Ψ⊑Ψ′ (⇒∼★ A∼★ B∼★) = ⇒∼★ (weaken-∼ Ψ⊑Ψ′ A∼★) (weaken-∼ Ψ⊑Ψ′ B∼★)
weaken-∼ Ψ⊑Ψ′ (★∼⇒ ★∼A ★∼B) = ★∼⇒ (weaken-∼ Ψ⊑Ψ′ ★∼A) (weaken-∼ Ψ⊑Ψ′ ★∼B)
weaken-∼ Ψ⊑Ψ′ (⇒∼⇒ A∼C B∼D) = ⇒∼⇒ (weaken-∼ Ψ⊑Ψ′ A∼C) (weaken-∼ Ψ⊑Ψ′ B∼D)
weaken-∼ Ψ⊑Ψ′ (∀∼∀ A∼B) = ∀∼∀ (weaken-∼ (Ψ⊑Ψ′ , _≤_.b≤b) A∼B)
weaken-∼ Ψ⊑Ψ′ (∼∀ A∼B) = ∼∀ (weaken-∼ (Ψ⊑Ψ′ , _≤_.b≤b) A∼B)
weaken-∼ Ψ⊑Ψ′ (∀∼ A∼B) = ∀∼ (weaken-∼ (Ψ⊑Ψ′ , _≤_.b≤b) A∼B)

injective : ∀{A B : Set} → (A → B) → Set
injective{A} f = ∀ (x y : A) → (f x ≡ f y) → (x ≡ y)

injective-Sᵗ : ∀{Δ} → injective (Sᵗ{Δ})
injective-Sᵗ x y refl = refl

injective-ext : ∀{Δ Δ′}
    → (ρ : Δ ⇒ᵗ Δ′)
    → injective ρ
    → injective (extᵗ ρ)
injective-ext ρ inj Zᵗ Zᵗ eq = refl
injective-ext ρ inj (Sᵗ x) (Sᵗ y) eq =
  cong Sᵗ (inj x y (injective-Sᵗ (ρ x) (ρ y) eq))

X≡Y⇒X∼Y : ∀{Δ}{Ψ}{X Y : TyVar Δ}
  → X ≡ Y
  → Δ ∣ Ψ ⊢ ` X ∼ ` Y
X≡Y⇒X∼Y refl = X∼X

X∼Y⇒X≡Y : ∀{Δ}{Ψ}{X Y : TyVar Δ}
  → Δ ∣ Ψ ⊢ ` X ∼ ` Y
  → X ≡ Y
X∼Y⇒X≡Y X∼X = refl

-- Capture the initial renaming and changes in this relation
data Pres-⇑ : ∀{Δ Δ′} → (ρ : Δ ⇒ᵗ Δ′)
    → (Ψ : SubCtx Δ) → (Ψ′ : SubCtx Δ′) → Set where
    
  Pres-Sᵗ : ∀{Δ}{Ψ}{b} → Pres-⇑{Δ}{Δ ,typ} Sᵗ Ψ (Ψ , b)
  
  Pres-ext : ∀{Δ Δ′}{Ψ Ψ′}{b}{ρ : Δ ⇒ᵗ Δ′}
    → Pres-⇑ ρ Ψ Ψ′
    → Pres-⇑ (extᵗ ρ) (Ψ , b) (Ψ′ , b)

-- Prove that the each cast has the desired property
Pres-⇑⇒∋ : ∀{Δ Δ′}{Ψ Ψ′}{X}
  → (ρ : Δ ⇒ᵗ Δ′)
  → Pres-⇑ ρ Ψ Ψ′
  → Ψ′ ∋ˢ ρ X
  → Ψ ∋ˢ X
Pres-⇑⇒∋ ρ Pres-Sᵗ (Sˢ ∋ρX) = ∋ρX
Pres-⇑⇒∋ {X = Zᵗ} ρ (Pres-ext IH) Zˢ = Zˢ
Pres-⇑⇒∋ {X = Sᵗ X} ρ (Pres-ext {ρ = ρ′} IH) (Sˢ ∋ρX) =
  Sˢ (Pres-⇑⇒∋ ρ′ IH ∋ρX)

ren-type-∼ : ∀{Δ Δ′}{Ψ Ψ′}{A B : Type Δ}
    → (ρ : Δ ⇒ᵗ Δ′)
    → Δ′ ∣ Ψ′ ⊢ renᵗ ρ A ∼ renᵗ ρ B
    → injective ρ
    → Pres-⇑ ρ Ψ Ψ′
    → Δ ∣ Ψ ⊢ A ∼ B
ren-type-∼ {A = `ℕ} {`ℕ} ρ ρA∼ρB inj p = ℕ∼ℕ
ren-type-∼ {A = `ℕ} {★} ρ ρA∼ρB inj p = ℕ∼★
ren-type-∼ {A = `ℕ} {`∀ B} ρ (∼∀ ρA∼ρB) inj p =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext p))
ren-type-∼ {A = ★} {`ℕ} ρ ρA∼ρB inj pres = ★∼ℕ
ren-type-∼ {A = ★} {★} ρ ρA∼ρB inj pres = ★∼★
ren-type-∼ {A = ★} {` X} ρ (★∼X ∋ρX) inj pres =
  ★∼X (Pres-⇑⇒∋ ρ pres ∋ρX)
ren-type-∼ {A = ★} {B₁ ⇒ B₂} ρ (★∼⇒ ρA∼ρB ρA∼ρB₁) inj pres =
  ★∼⇒ (ren-type-∼ ρ ρA∼ρB inj pres) (ren-type-∼ ρ ρA∼ρB₁ inj pres)
ren-type-∼ {A = ★} {`∀ B} ρ (∼∀ ρA∼ρB) inj pres =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = ` X} {★} ρ (X∼★ ∋ρX) inj pres =
  X∼★ (Pres-⇑⇒∋ ρ pres ∋ρX)
ren-type-∼ {A = ` X} {` Y} ρ ρA∼ρB inj pres =
  X≡Y⇒X∼Y (inj X Y (X∼Y⇒X≡Y ρA∼ρB))
ren-type-∼ {A = ` X} {`∀ B} ρ (∼∀ ρA∼ρB) inj pres =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = A₁ ⇒ A₂} {★} ρ (⇒∼★ ρA∼ρB ρA∼ρB₁) inj pres =
  ⇒∼★ (ren-type-∼ ρ ρA∼ρB inj pres) (ren-type-∼ ρ ρA∼ρB₁ inj pres)
ren-type-∼ {A = A₁ ⇒ A₂} {B₁ ⇒ B₂} ρ (⇒∼⇒ ρA∼ρB ρA∼ρB₁) inj pres =
  ⇒∼⇒ (ren-type-∼ ρ ρA∼ρB inj pres) (ren-type-∼ ρ ρA∼ρB₁ inj pres)
ren-type-∼ {A = A₁ ⇒ A₂} {`∀ B} ρ (∼∀ ρA∼ρB) inj pres =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {`ℕ} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {★} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {` x} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {B₁ ⇒ B₂} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {`∀ B} ρ (∀∼∀ ρA∼ρB) inj pres =
  ∀∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {`∀ B} ρ (∼∀ ρA∼ρB) inj pres =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {`∀ B} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))

dec-∼ : ∀{Δ}{Ψ}{A B : Type Δ}{b}
    → (Δ ,typ) ∣ Ψ , b ⊢ ⇑ᵗ A ∼ ⇑ᵗ B
    → Δ ∣ Ψ ⊢ A ∼ B
dec-∼ ⇑A∼⇑B = ren-type-∼ Sᵗ ⇑A∼⇑B injective-Sᵗ Pres-Sᵗ

UB⇒consistent : ∀{Δ}{Ψ₁ Ψ₂}{A B C : Type Δ}
  → Δ ∣ Ψ₁ ⊢ A ⊑ C
  → Δ ∣ Ψ₂ ⊢ B ⊑ C
  → Δ ∣ Ψ₁ ⊔ Ψ₂ ⊢ A ∼ B
UB⇒consistent{Ψ₁ = Ψ₁} ℕ⊑ℕ ℕ⊑ℕ = ℕ∼ℕ
UB⇒consistent{Ψ₁ = Ψ₁} ℕ⊑ℕ ★⊑ℕ = ℕ∼★
UB⇒consistent{Ψ₁ = Ψ₁} X⊑X X⊑X =  X∼X
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} X⊑X (★⊑X ∋X) =
  X∼★ (weaken-∋ (less-lub-right Ψ₁ Ψ₂) ∋X)
UB⇒consistent{Ψ₁ = Ψ₁} ★⊑★ ★⊑★ = ★∼★
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (★⊑X ∋X) X⊑X =
  ★∼X (weaken-∋ (less-lub-left Ψ₁ Ψ₂) ∋X)
UB⇒consistent{Ψ₁ = Ψ₁} (★⊑X ∋X) (★⊑X ∋X′) =  ★∼★
UB⇒consistent{Ψ₁ = Ψ₁} ★⊑ℕ ℕ⊑ℕ = ★∼ℕ
UB⇒consistent{Ψ₁ = Ψ₁} ★⊑ℕ ★⊑ℕ = ★∼★
UB⇒consistent{Ψ₁ = Ψ₁} (★⊑⇒ ac ac₁) (★⊑⇒ bc bc₁) = ★∼★
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (★⊑⇒{A = C₁}{B = C₂} ★⊑C₁ ★⊑C₂)
                           (⇒⊑⇒{A = B₁}{B₂} B₁⊑C₁ B₂⊑C₂) =
    ★∼⇒ (UB⇒consistent ★⊑C₁ B₁⊑C₁) (UB⇒consistent ★⊑C₂ B₂⊑C₂)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (⇒⊑⇒ a⊑c b⊑d) (★⊑⇒ ⊑c ⊑d) =
    ⇒∼★ (UB⇒consistent a⊑c ⊑c) (UB⇒consistent b⊑d ⊑d)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (⇒⊑⇒ a⊑c b⊑d) (⇒⊑⇒ ac bd) =
    ⇒∼⇒ (UB⇒consistent a⊑c ac) (UB⇒consistent b⊑d bd)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (∀⊑∀ a⊑b) (∀⊑∀ a′⊑b) =
    ∀∼∀ (UB⇒consistent a⊑b a′⊑b)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (∀⊑∀{B = C} ac) (⊑∀{B = C}  bc) =
  ∀∼ (UB⇒consistent ac bc)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (⊑∀ ac) (∀⊑∀ bc) = ∼∀ (UB⇒consistent ac bc)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (⊑∀ ac) (⊑∀ bc) = dec-∼ (UB⇒consistent ac bc)
