{-# OPTIONS --rewriting #-}

module PolyBlame.Rename where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Data.Fin

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
infixl 5 _,=_

data TyCtx where
  ∅ : TyCtx
  _,typ : TyCtx → TyCtx
  _,=_ : (Δ : TyCtx) → Type Δ → TyCtx

data TyVar : (Δ : TyCtx) → Set where
  Ztyp : ∀{Δ} → TyVar (Δ ,typ)
  Zbind : ∀{Δ}
    → (A : Type Δ)
    → TyVar (Δ ,= A)
  Styp : ∀{Δ}
     → TyVar Δ
     → TyVar (Δ ,typ)
  Sbind : ∀{Δ}{A : Type Δ}
     → TyVar Δ
     → TyVar (Δ ,= A)

data TyRen : TyCtx → TyCtx → Set where
  idr : ∀{Δ} → TyRen ∅ Δ
  extr-typ : ∀{Δ₁ Δ₂}
    → (ρ : TyRen Δ₁ Δ₂)
    → TyRen (Δ₁ ,typ) (Δ₂ ,typ)
  sucr-typ : ∀{Δ}
    → TyRen Δ (Δ ,typ)
  sucr-bind : ∀{Δ}{A : Type Δ}
    → TyRen Δ (Δ ,= A)

ren-tyvar : ∀{Δ₁ Δ₂} → TyRen Δ₁ Δ₂ → TyVar Δ₁ → TyVar Δ₂
ren-tyvar (extr-typ ρ) Ztyp = Ztyp
ren-tyvar (extr-typ ρ) (Styp X) = Styp (ren-tyvar ρ X)
ren-tyvar sucr-typ X = Styp X
ren-tyvar sucr-bind X = Sbind X

infixr 7 _⇒ᵣ_

_⇒ᵣ_ : TyCtx → TyCtx → Set
Δ₁ ⇒ᵣ Δ₂ = TyVar Δ₁ → TyVar Δ₂

idᵗ : ∀{Δ} → Δ ⇒ᵣ Δ
idᵗ x = x

infixr 6 _•ᵗ_
_•ᵗ_ : ∀{Δ₁ Δ₂} → TyVar Δ₂ → (Δ₁ ⇒ᵣ Δ₂) → ((Δ₁ ,typ) ⇒ᵣ Δ₂)
(Y •ᵗ ρ) Ztyp = Y
(Y •ᵗ ρ) (Styp X) = ρ X

extᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵣ Δ₂) → ((Δ₁ ,typ) ⇒ᵣ (Δ₂ ,typ))
extᵗ ρ Ztyp = Ztyp
extᵗ ρ (Styp X) = Styp (ρ X)

⟰ᵗ : ∀{Δ₁ Δ₂} → (Δ₁ ⇒ᵣ Δ₂) → (Δ₁ ⇒ᵣ (Δ₂ ,typ))
⟰ᵗ ρ x = Styp (ρ x)

ren-tyvar-id : ren-tyvar idr ≡ (idᵗ{∅})
ren-tyvar-id = extensionality G
  where G : (x : TyVar ∅) → ren-tyvar idr x ≡ idᵗ x
        G ()
{-# REWRITE ren-tyvar-id #-}

ren-tyvar-extr-typ : ∀{Δ₁ Δ₂} (ρ : TyRen Δ₁ Δ₂)
  → ren-tyvar (extr-typ ρ) ≡ extᵗ (ren-tyvar ρ)
ren-tyvar-extr-typ {Δ₁}{Δ₂} ρ = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
           ren-tyvar (extr-typ ρ) x ≡ extᵗ (ren-tyvar ρ) x
        G Ztyp = refl
        G (Styp x) = refl
{-# REWRITE ren-tyvar-extr-typ #-}

infixr 5 _⨟ᵗ_
_⨟ᵗ_ : ∀{Δ₁ Δ₂ Δ₃ : TyCtx} → (Δ₁ ⇒ᵣ Δ₂) → (Δ₂ ⇒ᵣ Δ₃) → (Δ₁ ⇒ᵣ Δ₃)
(ρ₁ ⨟ᵗ ρ₂) x = ρ₂ (ρ₁ x)

cons-seq-dist : ∀{Δ₁}{Δ₂}{Δ₃}{Y}{ρ₁ : Δ₁ ⇒ᵣ Δ₂}{ρ₂ : Δ₂ ⇒ᵣ Δ₃}
   → (Y •ᵗ ρ₁) ⨟ᵗ ρ₂ ≡ (ρ₂ Y •ᵗ (ρ₁ ⨟ᵗ ρ₂))
cons-seq-dist {Δ₁}{Δ₂}{Δ₃}{Y}{ρ₁}{ρ₂} = extensionality G
  where G : (x : TyVar (Δ₁ ,typ)) →
             (Y •ᵗ ρ₁ ⨟ᵗ ρ₂) x ≡ (ρ₂ Y •ᵗ (ρ₁ ⨟ᵗ ρ₂)) x
        G Ztyp = refl
        G (Styp x) = refl

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

ren-ty : ∀{Δ₁ Δ₂} → TyRen Δ₁ Δ₂ → Type Δ₁ → Type Δ₂
ren-ty ρ A = ren-type (ren-tyvar ρ) A

ren-ren : ∀ {Δ₁}{Δ₂}{Δ₃} (ρ₁ : Δ₁ ⇒ᵣ Δ₂)(ρ₂ : Δ₂ ⇒ᵣ Δ₃){A}
  → ren-type ρ₂ (ren-type ρ₁ A) ≡ ren-type (ρ₁ ⨟ᵗ ρ₂) A
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {`ℕ} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {★} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {` X} = refl
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {A ⇒ B} = cong₂ _⇒_ (ren-ren ρ₁ ρ₂) (ren-ren ρ₁ ρ₂)
ren-ren {Δ₁} {Δ₂} {Δ₃} ρ₁ ρ₂ {`∀ A} = cong `∀_ G
  where G : ren-type (extᵗ ρ₂) (ren-type (extᵗ ρ₁) A) ≡ ren-type (extᵗ (ρ₁ ⨟ᵗ ρ₂)) A
        G rewrite sym (ext-compose-dist ρ₁ ρ₂) = ren-ren (extᵗ ρ₁) (extᵗ ρ₂)

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

data _∋_:=_ : (Δ : TyCtx) → TyVar Δ → Type Δ → Set where
  bindZ : ∀{Δ}{A : Type Δ}
    → (Δ ,= A) ∋ (Zbind A) := (ren-ty sucr-bind A)
  bindStyp : ∀{Δ}{A : Type Δ}{X : TyVar Δ}
    → Δ ∋ X := A
    → (Δ ,typ) ∋ (Styp X) := (ren-ty sucr-typ A)
  bindSbind : ∀{Δ}{A : Type Δ}{B}{X : TyVar Δ}
    → Δ ∋ X := A
    → (Δ ,= B) ∋ (Sbind X) := (ren-ty sucr-bind A)
  
data Grnd : TyCtx → Set where
  ★⇒★ : ∀{Δ} → Grnd Δ
  `ℕ  : ∀{Δ} → Grnd Δ
  `_ : ∀{Δ} → TyVar Δ → Grnd Δ

⌈_⌉ : ∀{Δ} → Grnd Δ → Type Δ
⌈ ★⇒★ ⌉ = ★ ⇒ ★
⌈ `ℕ ⌉ = `ℕ
⌈ ` X ⌉ = ` X

ren-grnd : ∀{Δ₁ Δ₂} → TyRen Δ₁ Δ₂ → Grnd Δ₁ → Grnd Δ₂
ren-grnd ρ ★⇒★ = ★⇒★
ren-grnd ρ `ℕ = `ℕ
ren-grnd ρ (` X) = ` (ren-tyvar ρ X)

data Crcn : ∀(Δ : TyCtx) → Type Δ → Type Δ → Set where
 id : ∀{Δ}{A : Type Δ} → Crcn Δ A A
 _↦_ : ∀{Δ}{A B C D : Type Δ}
   → Crcn Δ C A
   → Crcn Δ B D
   → Crcn Δ (A ⇒ B) (C ⇒ D)
 _⨟_ : ∀{Δ}{A B C : Type Δ}
   → Crcn Δ A B
   → Crcn Δ B C
   → Crcn Δ A C
 `∀_ : ∀{Δ}{A B : Type (Δ ,typ)}
   → Crcn (Δ ,typ) A B
   → Crcn Δ (`∀ A) (`∀ B)
 𝒢 : ∀{Δ}{A : Type Δ} {B : Type (Δ ,typ)}
   → Crcn (Δ ,typ) (ren-ty sucr-typ A) B
   → Crcn Δ A (`∀ B)
 ℐ : ∀{Δ}{A : Type (Δ ,typ)} {B : Type Δ}
   → Crcn (Δ ,typ) A (ren-ty sucr-typ B)
   → Crcn Δ (`∀ A) B
 _↓_ : ∀{Δ}{A : Type Δ}
   → (X : TyVar Δ)
   → Δ ∋ X := A
   → Crcn Δ A (` X)
 _↑_ : ∀{Δ}{A : Type Δ}
   → (X : TyVar Δ)
   → Δ ∋ X := A
   → Crcn Δ (` X) A
 _! : ∀{Δ}
   → (G : Grnd Δ)
   → Crcn Δ ⌈ G ⌉ ★
 _`? : ∀{Δ}
   → (H : Grnd Δ)
   → Crcn Δ ★ ⌈ H ⌉

postulate extr-suc-commute : ∀{Δ₁ Δ₂}{ρ : TyRen Δ₁ Δ₂}{A} → (ren-ty (extr-typ ρ) (ren-ty sucr-typ A)) ≡ (ren-ty sucr-typ (ren-ty ρ A))

ren-bind : ∀{Δ₁ Δ₂ : TyCtx}{ρ : TyRen Δ₁ Δ₂}{X : TyVar Δ₁}{A : Type Δ₁}
  → Δ₁ ∋ X := A
  → Δ₂ ∋ ren-tyvar ρ X := ren-ty ρ A
ren-bind {Δ₁} {Δ₂} {sucr-typ} bindZ = bindStyp bindZ
ren-bind {Δ₁} {Δ₂} {sucr-bind} bindZ = bindSbind bindZ
ren-bind {Δ₁ ,typ} {Δ₂ ,typ} {extr-typ ρ} (bindStyp{A = A} Δ₁∋X)
  rewrite extr-suc-commute{Δ₁}{Δ₂}{ρ}{A} = bindStyp (ren-bind Δ₁∋X)
ren-bind {Δ₁} {Δ₂} {sucr-typ} (bindStyp Δ₁∋X) = bindStyp (ren-bind {ρ = sucr-typ} Δ₁∋X)
ren-bind {Δ₁} {Δ₂} {sucr-bind} (bindStyp Δ₁∋X) = bindSbind (ren-bind {ρ = sucr-typ} Δ₁∋X)
ren-bind {Δ₁} {Δ₂} {sucr-typ} (bindSbind Δ₁∋X) = bindStyp (ren-bind Δ₁∋X)
ren-bind {Δ₁} {Δ₂} {sucr-bind} (bindSbind Δ₁∋X) = bindSbind (ren-bind Δ₁∋X)

ren-from-grnd : ∀{Δ₁ Δ₂} (ρ : TyRen Δ₁ Δ₂)(G : Grnd Δ₁) → ren-ty ρ ⌈ G ⌉ ≡ ⌈ ren-grnd ρ G ⌉ 
ren-from-grnd ρ ★⇒★ = refl
ren-from-grnd ρ `ℕ = refl
ren-from-grnd ρ (` X) = refl

rename-crcn : ∀{Δ₁ Δ₂}{A B}
  → (ρ : TyRen Δ₁ Δ₂) → Crcn Δ₁ A B → Crcn Δ₂ (ren-ty ρ A) (ren-ty ρ B)
rename-crcn ρ id = id
rename-crcn ρ (c ↦ d) = rename-crcn ρ c ↦ rename-crcn ρ d
rename-crcn ρ (c ⨟ d) = rename-crcn ρ c ⨟ rename-crcn ρ d
rename-crcn ρ (`∀ c) = `∀ rename-crcn (extr-typ ρ) c
rename-crcn {Δ₁}{Δ₂}{A}{`∀ B} ρ (𝒢{Δ₁}{A}{B} c)
    with rename-crcn (extr-typ ρ) c
... | IH
    rewrite extr-suc-commute{Δ₁}{Δ₂}{ρ}{A} =
    𝒢 IH
rename-crcn {Δ₁}{Δ₂}{`∀ A}{B} ρ (ℐ c)
    with rename-crcn (extr-typ ρ) c
... | IH
    rewrite extr-suc-commute{Δ₁}{Δ₂}{ρ}{B} =
    ℐ IH
rename-crcn {Δ₁}{Δ₂} ρ (X ↓ Δ₁∋X:=A) = (ren-tyvar ρ X) ↓ (ren-bind Δ₁∋X:=A)
rename-crcn ρ (X ↑ Δ₁∋X:=A) = (ren-tyvar ρ X) ↑ ren-bind Δ₁∋X:=A
rename-crcn ρ (G !) rewrite ren-from-grnd ρ G = ren-grnd ρ G !
rename-crcn ρ (H `?) rewrite ren-from-grnd ρ H = ren-grnd ρ H `?
