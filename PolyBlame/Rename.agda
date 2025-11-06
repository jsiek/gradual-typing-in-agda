{-# OPTIONS --rewriting #-}

module PolyBlame.Rename where

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

postulate
  extensionality : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁ }{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

data TyCtx : Set 
data Type : TyCtx → Set 

infixl 5 _,typ
--infixl 5 _,=_

data TyCtx where
  ∅ : TyCtx
  _,typ : TyCtx → TyCtx
--  _,=_ : (Δ : TyCtx) → Type Δ → TyCtx

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

infixr 7 _⇒ᵣ_

_⇒ᵣ_ : TyCtx → TyCtx → Set
Δ₁ ⇒ᵣ Δ₂ = TyVar Δ₁ → TyVar Δ₂

idᵗ : ∀{Δ} → Δ ⇒ᵣ Δ
idᵗ = λ x → x

infixr 6 _•ᵗ_
_•ᵗ_ : ∀{Δ₁ Δ₂} → TyVar Δ₂ → (Δ₁ ⇒ᵣ Δ₂) → ((Δ₁ ,typ) ⇒ᵣ Δ₂)
(Y •ᵗ ρ) Zᵗ = Y
(Y •ᵗ ρ) (Sᵗ X) = ρ X

extᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵣ Δ₂) → ((Δ₁ ,typ) ⇒ᵣ (Δ₂ ,typ))
extᵗ ρ Zᵗ = Zᵗ
extᵗ ρ (Sᵗ X) = Sᵗ (ρ X)

⟰ᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵣ Δ₂) → (Δ₁ ⇒ᵣ (Δ₂ ,typ))
⟰ᵗ ρ x = Sᵗ (ρ x)

abstract
  infixr 5 _⨟ᵗ_
  _⨟ᵗ_ : ∀{Δ₁ Δ₂ Δ₃ : TyCtx} → (Δ₁ ⇒ᵣ Δ₂) → (Δ₂ ⇒ᵣ Δ₃) → (Δ₁ ⇒ᵣ Δ₃)
  (ρ₁ ⨟ᵗ ρ₂) x = ρ₂ (ρ₁ x)

  seq-def : ∀ {Δ₁ Δ₂ Δ₃ : TyCtx} (σ : Δ₁ ⇒ᵣ Δ₂) (τ : Δ₂ ⇒ᵣ Δ₃) x → (σ ⨟ᵗ τ) x ≡ τ (σ x)
  seq-def σ τ x = refl
  {-# REWRITE seq-def #-}

suc-seq-cons : ∀{Δ₁ Δ₂ : TyCtx} (ρ : Δ₁ ⇒ᵣ Δ₂)(Y : TyVar Δ₂)
  → Sᵗ ⨟ᵗ (Y •ᵗ ρ) ≡ ρ
suc-seq-cons ρ Y = refl  
-- {-# REWRITE suc-seq-cons #-}

cons-zero-suc-id : ∀{Δ : TyCtx} → Zᵗ{Δ} •ᵗ Sᵗ ≡ idᵗ
cons-zero-suc-id{Δ} = extensionality G
  where G : (x : TyVar (Δ ,typ)) → (Zᵗ •ᵗ Sᵗ) x ≡ idᵗ x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE cons-zero-suc-id #-}

cons-seq-dist : ∀{Δ₁}{Δ₂}{Δ₃}{Y}{ρ₁ : Δ₁ ⇒ᵣ Δ₂}{ρ₂ : Δ₂ ⇒ᵣ Δ₃}
   → (Y •ᵗ ρ₁) ⨟ᵗ ρ₂ ≡ (ρ₂ Y •ᵗ (ρ₁ ⨟ᵗ ρ₂))
cons-seq-dist {Δ₁}{Δ₂}{Δ₃}{Y}{ρ₁}{ρ₂} = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
             (Y •ᵗ ρ₁ ⨟ᵗ ρ₂) x ≡ (ρ₂ Y •ᵗ (ρ₁ ⨟ᵗ ρ₂)) x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE cons-seq-dist #-}

ext-ren : ∀{Δ₁}{Δ₂}{ρ : Δ₁ ⇒ᵣ Δ₂} → Zᵗ •ᵗ (⟰ᵗ ρ) ≡ extᵗ ρ
ext-ren {Δ₁}{Δ₂}{ρ} = extensionality G
  where G : (X : TyVar (Δ₁ ,typ)) → (Zᵗ •ᵗ ⟰ᵗ ρ) X ≡ extᵗ ρ X
        G Zᵗ = refl
        G (Sᵗ X) = refl

ext-compose-dist : ∀ {Δ₁}{Δ₂}{Δ₃} (ρ₁ : Δ₁ ⇒ᵣ Δ₂)(ρ₂ : Δ₂ ⇒ᵣ Δ₃)
  → (extᵗ ρ₁) ⨟ᵗ (extᵗ ρ₂) ≡ extᵗ (ρ₁ ⨟ᵗ ρ₂)
ext-compose-dist {Δ₁}{Δ₂}{Δ₃} ρ₁ ρ₂ = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
           (extᵗ ρ₁ ⨟ᵗ extᵗ ρ₂) x ≡ extᵗ (ρ₁ ⨟ᵗ ρ₂) x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE ext-compose-dist #-}

seq-id : ∀{Δ₁ Δ₂}{ρ : Δ₁ ⇒ᵣ Δ₂} → (idᵗ ⨟ᵗ ρ) ≡ ρ
seq-id {Δ₁}{Δ₂}{ρ} = refl
{-# REWRITE seq-id #-}

id-seq : ∀{Δ₁ Δ₂}{ρ : Δ₁ ⇒ᵣ Δ₂} → (ρ ⨟ᵗ idᵗ) ≡ ρ
id-seq {Δ₁}{Δ₂}{ρ} = refl
{-# REWRITE id-seq #-}

data Type where
  `ℕ  : ∀{Δ} → Type Δ
  ★   : ∀{Δ} → Type Δ
  `_ : ∀{Δ} → (x : TyVar Δ) → Type Δ
  _⇒_ : ∀{Δ} → Type Δ → Type Δ → Type Δ
  `∀_  : ∀{Δ} → Type (Δ ,typ) → Type Δ

ren-type : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵣ Δ₂) → Type Δ₁ → Type Δ₂
ren-type ρ (A ⇒ B) = (ren-type ρ A) ⇒ (ren-type ρ B)
ren-type ρ `ℕ = `ℕ
ren-type ρ ★ = ★
ren-type ρ (`∀ A) = `∀ (ren-type (extᵗ ρ) A)
ren-type ρ (` X) = ` (ρ X)

infix 6 _[_]ᵗ
_[_]ᵗ : ∀{Δ} → Type (Δ ,typ) → TyVar Δ → Type Δ
A [ X ]ᵗ = ren-type (X •ᵗ idᵗ) A

⇑ᵗ : ∀{Δ} → Type Δ → Type (Δ ,typ)
⇑ᵗ A = ren-type Sᵗ A

ren-ren : ∀ {Δ₁}{Δ₂}{Δ₃} (ρ₁ : Δ₁ ⇒ᵣ Δ₂)(ρ₂ : Δ₂ ⇒ᵣ Δ₃){A}
  → ren-type ρ₂ (ren-type ρ₁ A) ≡ ren-type (ρ₁ ⨟ᵗ ρ₂) A
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {`ℕ} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {★} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {` X} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {A ⇒ B} =
   cong₂ _⇒_ (ren-ren ρ₁ ρ₂) (ren-ren ρ₁ ρ₂)
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {`∀ A} = cong `∀_ G
  where G : ren-type (extᵗ ρ₂) (ren-type (extᵗ ρ₁) A) ≡ ren-type (extᵗ (ρ₁ ⨟ᵗ ρ₂)) A
        G rewrite sym (ext-compose-dist ρ₁ ρ₂) = ren-ren (extᵗ ρ₁) (extᵗ ρ₂)
{-# REWRITE ren-ren #-}

extᵗ-id : ∀{Δ} → extᵗ (idᵗ{Δ}) ≡ idᵗ
extᵗ-id {Δ} = extensionality G
  where G : (x : TyVar (Δ ,typ)) → extᵗ idᵗ x ≡ idᵗ x
        G Zᵗ = refl
        G (Sᵗ x) = refl
{-# REWRITE extᵗ-id #-}

ren-type-id : ∀{Δ}{A : Type Δ} → ren-type idᵗ A ≡ A
ren-type-id {Δ} {`ℕ} = refl
ren-type-id {Δ} {★} = refl
ren-type-id {Δ} {` x} = refl
ren-type-id {Δ} {A ⇒ B} = cong₂ _⇒_ ren-type-id ren-type-id
ren-type-id {Δ} {`∀ A} = cong `∀_ ren-type-id
{-# REWRITE ren-type-id #-}

ext-seq-cons : ∀{Δ₁ Δ₂ Δ₃}{X}{ρ₁ : Δ₁ ⇒ᵣ Δ₂}{ρ₂ : Δ₂ ⇒ᵣ Δ₃}
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

ren-grnd : ∀{Δ₁ Δ₂} → Δ₁ ⇒ᵣ Δ₂ → Grnd Δ₁ → Grnd Δ₂
ren-grnd ρ ★⇒★ = ★⇒★
ren-grnd ρ `ℕ = `ℕ
ren-grnd ρ (` X) = ` (ρ X)

ren-pair : ∀{Δ₁ Δ₂} → Δ₁ ⇒ᵣ Δ₂ → TyVar Δ₁ × Type Δ₁ → TyVar Δ₂ × Type Δ₂
ren-pair ρ (X , A) = ρ X , ren-type ρ A

⤊ : ∀{Δ} → BindCtx Δ → BindCtx (Δ ,typ)
⤊ = map (ren-pair Sᵗ)

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
