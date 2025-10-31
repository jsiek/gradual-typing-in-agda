{-# OPTIONS --rewriting #-}

module PolyBlame.Rename where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.List.Properties using (map-∘)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Data.Fin
open import Function using (_∘_)

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
  Ztyp : ∀{Δ} → TyVar (Δ ,typ)
  Styp : ∀{Δ}
     → TyVar Δ
       --------------
     → TyVar (Δ ,typ)

{- Renaming Type Variables -}

infixr 7 _⇒ᵣ_

_⇒ᵣ_ : TyCtx → TyCtx → Set
Δ₁ ⇒ᵣ Δ₂ = TyVar Δ₁ → TyVar Δ₂

idᵗ : ∀{Δ} → Δ ⇒ᵣ Δ
idᵗ = λ x → x

infixr 6 _•ᵗ_
_•ᵗ_ : ∀{Δ₁ Δ₂} → TyVar Δ₂ → (Δ₁ ⇒ᵣ Δ₂) → ((Δ₁ ,typ) ⇒ᵣ Δ₂)
(Y •ᵗ ρ) Ztyp = Y
(Y •ᵗ ρ) (Styp X) = ρ X

extᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵣ Δ₂) → ((Δ₁ ,typ) ⇒ᵣ (Δ₂ ,typ))
extᵗ ρ Ztyp = Ztyp
extᵗ ρ (Styp X) = Styp (ρ X)

⟰ᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵣ Δ₂) → (Δ₁ ⇒ᵣ (Δ₂ ,typ))
⟰ᵗ ρ x = Styp (ρ x)

abstract
  infixr 5 _⨟ᵗ_
  _⨟ᵗ_ : ∀{Δ₁ Δ₂ Δ₃ : TyCtx} → (Δ₁ ⇒ᵣ Δ₂) → (Δ₂ ⇒ᵣ Δ₃) → (Δ₁ ⇒ᵣ Δ₃)
  (ρ₁ ⨟ᵗ ρ₂) x = ρ₂ (ρ₁ x)

  seq-def : ∀ {Δ₁ Δ₂ Δ₃ : TyCtx} (σ : Δ₁ ⇒ᵣ Δ₂) (τ : Δ₂ ⇒ᵣ Δ₃) x → (σ ⨟ᵗ τ) x ≡ τ (σ x)
  seq-def σ τ x = refl
  {-# REWRITE seq-def #-}
  
cons-seq-dist : ∀{Δ₁}{Δ₂}{Δ₃}{Y}{ρ₁ : Δ₁ ⇒ᵣ Δ₂}{ρ₂ : Δ₂ ⇒ᵣ Δ₃}
   → (Y •ᵗ ρ₁) ⨟ᵗ ρ₂ ≡ (ρ₂ Y •ᵗ (ρ₁ ⨟ᵗ ρ₂))
cons-seq-dist {Δ₁}{Δ₂}{Δ₃}{Y}{ρ₁}{ρ₂} = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
             (Y •ᵗ ρ₁ ⨟ᵗ ρ₂) x ≡ (ρ₂ Y •ᵗ (ρ₁ ⨟ᵗ ρ₂)) x
        G Ztyp = refl
        G (Styp x) = refl
{-# REWRITE cons-seq-dist #-}

ext-ren : ∀{Δ₁}{Δ₂}{ρ : Δ₁ ⇒ᵣ Δ₂} → Ztyp •ᵗ (⟰ᵗ ρ) ≡ extᵗ ρ
ext-ren {Δ₁}{Δ₂}{ρ} = extensionality G
  where G : (X : TyVar (Δ₁ ,typ)) → (Ztyp •ᵗ ⟰ᵗ ρ) X ≡ extᵗ ρ X
        G Ztyp = refl
        G (Styp X) = refl

ext-compose-dist : ∀ {Δ₁}{Δ₂}{Δ₃} (ρ₁ : Δ₁ ⇒ᵣ Δ₂)(ρ₂ : Δ₂ ⇒ᵣ Δ₃)
  → (extᵗ ρ₁) ⨟ᵗ (extᵗ ρ₂) ≡ extᵗ (ρ₁ ⨟ᵗ ρ₂)
ext-compose-dist {Δ₁}{Δ₂}{Δ₃} ρ₁ ρ₂ = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
           (extᵗ ρ₁ ⨟ᵗ extᵗ ρ₂) x ≡ extᵗ (ρ₁ ⨟ᵗ ρ₂) x
        G Ztyp = refl
        G (Styp x) = refl
{-# REWRITE ext-compose-dist #-}

seq-id : ∀{Δ₁ Δ₂}{ρ : Δ₁ ⇒ᵣ Δ₂} → (idᵗ ⨟ᵗ ρ) ≡ ρ
seq-id {Δ₁}{Δ₂}{ρ} = refl

id-seq : ∀{Δ₁ Δ₂}{ρ : Δ₁ ⇒ᵣ Δ₂} → (ρ ⨟ᵗ idᵗ) ≡ ρ
id-seq {Δ₁}{Δ₂}{ρ} = refl

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

ren-ren : ∀ {Δ₁}{Δ₂}{Δ₃} (ρ₁ : Δ₁ ⇒ᵣ Δ₂)(ρ₂ : Δ₂ ⇒ᵣ Δ₃){A}
  → ren-type ρ₂ (ren-type ρ₁ A) ≡ ren-type (ρ₁ ⨟ᵗ ρ₂) A
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {`ℕ} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {★} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {` X} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {A ⇒ B} = cong₂ _⇒_ (ren-ren ρ₁ ρ₂) (ren-ren ρ₁ ρ₂)
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {`∀ A} = cong `∀_ G
  where G : ren-type (extᵗ ρ₂) (ren-type (extᵗ ρ₁) A) ≡ ren-type (extᵗ (ρ₁ ⨟ᵗ ρ₂)) A
        G rewrite sym (ext-compose-dist ρ₁ ρ₂) = ren-ren (extᵗ ρ₁) (extᵗ ρ₂)
{-# REWRITE ren-ren #-}

extᵗ-id : ∀{Δ} → extᵗ (idᵗ{Δ}) ≡ idᵗ
extᵗ-id {Δ} = extensionality G
  where G : (x : TyVar (Δ ,typ)) → extᵗ idᵗ x ≡ idᵗ x
        G Ztyp = refl
        G (Styp x) = refl
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
        G Ztyp = refl
        G (Styp x) = refl
{-# REWRITE ext-seq-cons #-}

BindCtx : TyCtx → Set
BindCtx Δ = List (TyVar Δ × Type Δ)

data _∋_:=_ : ∀{Δ : TyCtx} → BindCtx Δ → TyVar Δ → Type Δ → Set where
  here : ∀ {Δ}{Σ : BindCtx Δ}{X : TyVar Δ}{A : Type Δ}
    → ((X , A) ∷ Σ) ∋ X := A
  there : ∀ {Δ}{Σ : BindCtx Δ}{X Y : TyVar Δ}{A B : Type Δ}
    → Σ ∋ X := A
    → ((Y , B) ∷ Σ) ∋ X := A

data Grnd : TyCtx → Set where
  ★⇒★ : ∀{Δ} → Grnd Δ
  `ℕ  : ∀{Δ} → Grnd Δ
  `_ : ∀{Δ} → TyVar Δ → Grnd Δ

⌈_⌉ : ∀{Δ} → Grnd Δ → Type Δ
⌈ ★⇒★ ⌉ = ★ ⇒ ★
⌈ `ℕ ⌉ = `ℕ
⌈ ` X ⌉ = ` X

ren-grnd : ∀{Δ₁ Δ₂} → Δ₁ ⇒ᵣ Δ₂ → Grnd Δ₁ → Grnd Δ₂
ren-grnd ρ ★⇒★ = ★⇒★
ren-grnd ρ `ℕ = `ℕ
ren-grnd ρ (` X) = ` (ρ X)

ren-pair : ∀{Δ₁ Δ₂} → Δ₁ ⇒ᵣ Δ₂ → TyVar Δ₁ × Type Δ₁ → TyVar Δ₂ × Type Δ₂
ren-pair ρ (X , A) = ρ X , ren-type ρ A

⤊ : ∀{Δ} → BindCtx Δ → BindCtx (Δ ,typ)
⤊ = map (ren-pair Styp)

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
   → Crcn (Δ ,typ) (⤊ Σ) (ren-type Styp A) B
   → Crcn Δ Σ A (`∀ B)
 ℐ : ∀{Δ}{Σ}{A : Type (Δ ,typ)} {B : Type Δ}
   → Crcn (Δ ,typ) ((Ztyp , ★) ∷ ⤊ Σ) A (ren-type Styp B)
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
  → (ren-type (extᵗ ρ) (ren-type Styp A)) ≡ (ren-type Styp (ren-type ρ A))
extr-suc-commute = refl

ren-bind : ∀{Δ₁ Δ₂ : TyCtx}{Σ : BindCtx Δ₁}{ρ : Δ₁ ⇒ᵣ Δ₂}
    {X : TyVar Δ₁}{A : Type Δ₁}
  → Σ ∋ X := A
  → map (ren-pair ρ) Σ ∋ ρ X := ren-type ρ A
ren-bind {Δ₁} {Δ₂} {Σ} {ρ} {X} {A} here = here
ren-bind {Δ₁} {Δ₂} {Σ} {ρ} {X} {A} (there ∋α) = there (ren-bind ∋α)

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

