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
open import Data.Sum using (_⊎_)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)

open import PolyBlame.Rename

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

infix  5 ƛ_
infixl 7 _·_
infixl 7 _◯_
infix  9 `_
infix  9 #_

infixl 5 _▷_

{--- Term Variables and Contexts ---}

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
⟰ Γ = ren-ctx Sᵗ Γ

{----------- Well-Typed Terms ---------------------------------}

infix 4 _∣_∣_⊢_
data _∣_∣_⊢_ : (Δ : TyCtx) → BindCtx Δ → Ctx Δ → Type Δ → Set
  where
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
       --------------------
     → Δ ∣ Σ ∣ Γ ⊢ A [ X ]ᵗ
     
  _⟨_⟩ : ∀{Δ Σ Γ A B}
     → Δ ∣ Σ ∣ Γ ⊢ A
     → Δ ∣ Σ ⊢ A ⇒ B
       --------------
     → Δ ∣ Σ ∣ Γ ⊢ B
     
  blame : ∀{Δ Σ Γ A} → Δ ∣ Σ ∣ Γ ⊢ A
  
  ν_·_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{B : Type Δ}
    → (A : Type Δ)
    → (Δ ,typ) ∣ (Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ ∣ ⟰ Γ ⊢ ⇑ᵗ B
    → Δ ∣ Σ ∣ Γ ⊢ B

{------- Renaming Type Variables ------------}

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

infix 6 _[_]ᵀ
_[_]ᵀ : ∀{Δ}{Σ}{Γ}{A} → (Δ ,typ) ∣ Σ ∣ Γ ⊢ A → (X : TyVar Δ)
  → Δ ∣ map (ren-pair (X •ᵗ idᵗ)) Σ ∣ ren-ctx (X •ᵗ idᵗ) Γ ⊢ ren-type (X •ᵗ idᵗ) A
M [ X ]ᵀ = rename-ty (X •ᵗ idᵗ) M

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

rename-bind : ∀{Δ}{Σ₁ Σ₂ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}
  → (ρ : Σ₁ ⇒ᵇ Σ₂)
  → Δ ∣ Σ₁ ∣ Γ ⊢ A
  → Δ ∣ Σ₂ ∣ Γ ⊢ A
rename-bind ρ (` x) = ` x
rename-bind ρ (# k) = # k
rename-bind ρ (ƛ N) = ƛ rename-bind ρ N
rename-bind ρ (L · M) = (rename-bind ρ L) · (rename-bind ρ M)
rename-bind ρ (Λ N) = Λ rename-bind (extᵇ ρ) N
rename-bind ρ (M ◯ X) = rename-bind ρ M ◯ X
rename-bind ρ (M ⟨ c ⟩) = rename-bind ρ M ⟨ rename-crcn-bind ρ c ⟩
rename-bind ρ blame = blame
rename-bind ρ (ν A · N) = ν A · rename-bind (extᶜ (extᵇ ρ)) N

⇑ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}
  → Δ ∣ Σ ∣ Γ ⊢ A
  → (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ ⇑ᵗ A
⇑ M = rename-ty Sᵗ M

⇑ᵇ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{X}{B}
  → Δ ∣ Σ ∣ Γ ⊢ A
  → Δ ∣ (X , B) ∷ Σ ∣ Γ ⊢ A
⇑ᵇ M = rename-bind Sᵇ M

{---- Renaming Term Variables ----}

_⇨ᵣ_ : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Γ ⇨ᵣ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A

ext : ∀ {Δ : TyCtx}{Γ Γ′ : Ctx Δ}{A : Type Δ}
  → Γ ⇨ᵣ Γ′
  → (Γ ▷ A) ⇨ᵣ (Γ′ ▷ A)
ext ρ Z = Z
ext ρ (S x) = S ρ x

ren-ctx-∋ : ∀ {Δ Δ′}{Γ : Ctx Δ}{A : Type Δ′}{B : Type Δ}{r : Δ ⇒ᵣ Δ′}
  → ren-ctx r Γ ∋ A
  → Σ[ B ∈ Type Δ ] A ≡ ren-type r B × Γ ∋ B
ren-ctx-∋ {Δ}{Δ′} {Γ ▷ C} Z = C , refl , Z
ren-ctx-∋ {Δ}{Δ′}{Γ ▷ C}{A}{B} (S x)
    with ren-ctx-∋{Δ}{Δ′}{Γ}{A}{B} x
... | C , refl , y = C , refl , (S y)

rename-ctx : ∀ {Δ₁ Δ₂ : TyCtx}{r : Δ₁ ⇒ᵣ Δ₂}{Γ : Ctx Δ₁}{Γ′ : Ctx Δ₁}
  → Γ ⇨ᵣ Γ′
  → ren-ctx r Γ ⇨ᵣ ren-ctx r Γ′
rename-ctx {Δ₁} {Δ₂} {r} {Γ ▷ A} {Γ′} ρ {B} Z = ren-var r (ρ Z)
rename-ctx {Δ₁} {Δ₂} {r} {Γ ▷ A} {Γ′} ρ {B} (S x)
    with ren-ctx-∋{Δ₁}{Δ₂}{Γ}{B = A} {r = r} x
... | C , refl , Γ∋C = ren-var r (ρ (S Γ∋C))

rename : ∀{Δ}{Σ}{Γ}{Γ′}{A}
  → (ρ : Γ ⇨ᵣ Γ′)
  → Δ ∣ Σ ∣ Γ ⊢ A
  → Δ ∣ Σ ∣ Γ′ ⊢ A
rename ρ (` x) = ` (ρ x)
rename ρ (# k) = # k
rename ρ (ƛ N) = ƛ rename (ext ρ) N
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (Λ N) = Λ rename (rename-ctx ρ) N
rename ρ (M ◯ X) = (rename ρ M) ◯ X
rename ρ (M ⟨ c ⟩) = rename ρ M ⟨ c ⟩
rename ρ blame = blame
rename ρ (ν B · N) = ν B · rename (rename-ctx ρ) N

{---- Substitution of Term Variables ----}

_∣_⊢_⇨_ : ∀ (Δ : TyCtx) → BindCtx Δ → Ctx Δ → Ctx Δ → Set
Δ ∣ Σ ⊢ Γ ⇨ Γ′ = ∀ {A} → Γ ∋ A → Δ ∣ Σ ∣ Γ′ ⊢ A

exts : ∀ {Δ : TyCtx}{Σ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{A : Type Δ}
  → Δ ∣ Σ ⊢ Γ ⇨ Γ′
  → Δ ∣ Σ ⊢ (Γ ▷ A) ⇨ (Γ′ ▷ A)
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)

sub-ctx : ∀ {Δ₁ Δ₂ : TyCtx}{r : Δ₁ ⇒ᵣ Δ₂}{Σ : BindCtx Δ₁}{Γ : Ctx Δ₁}{Γ′ : Ctx Δ₁}
  → Δ₁ ∣ Σ ⊢ Γ ⇨ Γ′
  → Δ₂ ∣ map (ren-pair r) Σ ⊢ ren-ctx r Γ ⇨ ren-ctx r Γ′
sub-ctx {Δ₁} {Δ₂} {r} {Σ} {Γ ▷ A} {Γ′} σ Z = rename-ty r (σ Z)
sub-ctx {Δ₁} {Δ₂} {r} {Σ} {Γ ▷ A} {Γ′} σ (S x)
    with ren-ctx-∋{Δ₁}{Δ₂}{Γ}{B = A} {r = r} x
... | C , refl , Γ∋C = rename-ty r (σ (S Γ∋C))

sub : ∀{Δ}{Σ}{Γ}{Γ′}{A} → Δ ∣ Σ ⊢ Γ ⇨ Γ′ → Δ ∣ Σ ∣ Γ ⊢ A → Δ ∣ Σ ∣ Γ′ ⊢ A
sub σ (` x) = σ x
sub σ (# x) = # x
sub σ (ƛ N) = ƛ sub (exts σ) N
sub σ (L · M) = sub σ L · sub σ M
sub σ (Λ N) = Λ sub (sub-ctx σ) N
sub σ (M ◯ X) = sub σ M ◯ X
sub σ (M ⟨ c ⟩) = sub σ M ⟨ c ⟩
sub σ blame = blame
sub {Δ} σ (ν A · N) = ν A · sub (λ x → ⇑ᵇ (sub-ctx σ x)) N

idˢ : ∀{Δ}{Σ}{Γ} → Δ ∣ Σ ⊢ Γ ⇨ Γ
idˢ x = ` x

_•_ : ∀{Δ}{Σ}{Γ}{Γ′}{A}
  → Δ ∣ Σ ∣ Γ′ ⊢ A
  → Δ ∣ Σ ⊢ Γ ⇨ Γ′
  → Δ ∣ Σ ⊢ Γ ▷ A ⇨ Γ′
(M • σ) Z = M
(M • σ) (S x) = σ x

_[_] : ∀ {Δ}{Σ}{Γ}{A}{B}
  → Δ ∣ Σ ∣ Γ ▷ A ⊢ B
  → Δ ∣ Σ ∣ Γ ⊢ A
  → Δ ∣ Σ ∣ Γ ⊢ B 
M [ N ] = sub (N • idˢ) M

{- Value -}

data Value : ∀ {Δ}{Σ}{Γ}{A} → Δ ∣ Σ ∣ Γ ⊢ A → Set where
  ƛ_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → (N : Δ ∣ Σ ∣ (Γ ▷ A) ⊢ B)
       -------------------------
     → Value (ƛ N)

  #_ : ∀{Δ Σ Γ}{k}
     → ℕ
       --------------------
     → Value{Δ}{Σ}{Γ} (# k)
  
  Λ_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
     → (N : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A)
       -------------------------------
     → Value{Δ}{Σ}{Γ} (Λ N)

  _⟨G!⟩ : ∀{Δ Σ Γ}{G : Grnd Δ}{V : Δ ∣ Σ ∣ Γ ⊢ ⌈ G ⌉}
     → Value V
       -----------------
     → Value (V ⟨ G ! ⟩)

  _⟨X↓⟩ : ∀{Δ Σ Γ A}{V : Δ ∣ Σ ∣ Γ ⊢ A}{X}{∋X : Σ ∋ X := A}
     → Value V
       -----------------
     → Value (V ⟨ ∋X ↓ ⟩)

  -- problem parsing ambiguity
  V-⟨↦⟩ : ∀{Δ Σ Γ A B C D}{V : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
            {c : Δ ∣ Σ ⊢ C ⇒ A}{d : Δ ∣ Σ ⊢ B ⇒ D}
     → Value V
       -------------------
     → Value (V ⟨ c ↦ d ⟩)

  _⟨∀_⟩ : ∀{Δ Σ Γ A B}{V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
           {c : Δ ,typ ∣ ⤊ Σ ⊢ A ⇒ B}
     → Value V
       ------------------
     → Value (V ⟨ `∀ c ⟩)

  _⟨𝒢_⟩ : ∀{Δ Σ Γ A B}{V : Δ ∣ Σ ∣ Γ ⊢ A}
           {c : Δ ,typ ∣ ⤊ Σ ⊢ ⇑ᵗ A ⇒ B}
     → Value V
       -----------------
     → Value (V ⟨ 𝒢 c ⟩)

{- Pure Reduction -}

infix 2 _—→_
data _—→_ : ∀ {Δ Σ Γ A} → (Δ ∣ Σ ∣ Γ ⊢ A) → (Δ ∣ Σ ∣ Γ ⊢ A) → Set where

  -- (λx.N) V              —→  N[V/x]
  β : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
          {N : Δ ∣ Σ ∣ Γ ▷ B ⊢ A}
          {V : Δ ∣ Σ ∣ Γ ⊢ B}
    → Value V
    → (ƛ N) · V —→ N [ V ]

  -- (ΛX.V)[Y]             —→  V[Y/X]
  β-Λ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
          {V : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A}
          {Y : TyVar Δ}
    →  (Λ V) ◯ Y —→ V [ Y ]ᵀ

  -- V⟨∀X.c⟩[Y]            —→  V[Y]⟨c[Y/X]⟩
  β-⟨∀⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type (Δ ,typ)}
            {V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
            {c : Δ ,typ ∣ ⤊ Σ ⊢ A ⇒ B}
            {Y : TyVar Δ}
    → V ⟨ `∀ c ⟩ ◯ Y —→ (V ◯ Y) ⟨ c [ Y ]ᶜ ⟩

  -- V⟨𝒢 X.c⟩[Y]           —→ V⟨c[Y/X]⟩
  β-⟨𝒢⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}{B : Type (Δ ,typ)}
            {V : Δ ∣ Σ ∣ Γ ⊢ A}
            {c : Δ ,typ ∣ ⤊ Σ ⊢ (⇑ᵗ A) ⇒ B}
            {Y : TyVar Δ}
    → V ⟨ 𝒢 c ⟩ ◯ Y —→ V ⟨ c [ Y ]ᶜ ⟩

  -- V⟨ℐ X.c⟩             —→  νX=★. V[X]⟨c⟩
  β-⟨ℐ⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}{B : Type Δ}
            {V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
            {c : Δ ,typ ∣ (Zᵗ , ★) ∷ ⤊ Σ ⊢ A ⇒ (⇑ᵗ B)}
    → (V ⟨ ℐ{B = B} c ⟩) —→ (ν ★ · ((⇑ᵇ (⇑ V) ◯ Zᵗ) ⟨ c ⟩))
    
  -- V⟨id⟩                  —→  V
  ⟨id⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}{B : Type Δ}
           {V : Δ ∣ Σ ∣ Γ ⊢ A}
    → (V ⟨ id ⟩) —→ V

  -- V⟨X↓⟩⟨X↑⟩                  —→  V
  ⟨X↓⟩⟨X↑⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}{B : Type Δ}
           {V : Δ ∣ Σ ∣ Γ ⊢ A}{X}{∋X : Σ ∋ X := A}{∋X′ : Σ ∋ X := A}
    → (V ⟨ ∋X ↓ ⟩ ⟨ ∋X′ ↑ ⟩) —→ V

  -- V⟨G!⟩⟨G?⟩              —→  V
  ⟨G!⟩⟨G?⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{G}
           {V : Δ ∣ Σ ∣ Γ ⊢ ⌈ G ⌉}
    → V ⟨ G ! ⟩ ⟨ G `? ⟩ —→ V

  -- V⟨G!⟩⟨H?l⟩             —→  blame l    (G ≠ H)
  ⟨G!⟩⟨H?⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{G}{H}
           {V : Δ ∣ Σ ∣ Γ ⊢ ⌈ G ⌉}
    → G ≢ H
    → V ⟨ G ! ⟩ ⟨ H `? ⟩ —→ blame

  -- V⟨c → d⟩ W             —→  (V W⟨c⟩)⟨d⟩
  β-⟨c→d⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{B}{C}{D}
           {V : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}{W : Δ ∣ Σ ∣ Γ ⊢ C}
           {c : Δ ∣ Σ ⊢ C ⇒ A}{d : Δ ∣ Σ ⊢ B ⇒ D}
    → (V ⟨ c ↦ d ⟩) · W —→ (V · W ⟨ c ⟩) ⟨ d ⟩ 

  -- V⟨c ; d⟩              —→  V⟨c⟩⟨d⟩
  β-⟨c⨟d⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{B}{C}
           {V : Δ ∣ Σ ∣ Γ ⊢ A}
           {c : Δ ∣ Σ ⊢ A ⇒ B}{d : Δ ∣ Σ ⊢ B ⇒ C}
    → V ⟨ c ⨟ d ⟩ —→ V ⟨ c ⟩ ⟨ d ⟩ 

{- Helpers for Context Weaking -}

infix 3 _↝_
data _↝_ : ∀{Δ} → BindCtx Δ → BindCtx Δ → Set where
  ↝-extend : ∀ {Δ}{Σ : BindCtx Δ}{X}{A : Type Δ} → Σ ↝ (X , A) ∷ Σ
  ↝-refl : ∀ {Δ}{Σ : BindCtx Δ} → Σ ↝ Σ
  ↝-trans : ∀ {Δ}{Σ₁ Σ₂ Σ₃ : BindCtx Δ}
    → Σ₁ ↝ Σ₂
    → Σ₂ ↝ Σ₃
    → Σ₁ ↝ Σ₃

ren-bind-map : ∀{Δ Δ′}{Σ₁ Σ₂ : BindCtx Δ}
   (ρ : Δ ⇒ᵣ Δ′)
  → Σ₁ ↝ Σ₂
  → map (ren-pair ρ) Σ₁ ↝ map (ren-pair ρ) Σ₂
ren-bind-map ρ ↝-extend = ↝-extend
ren-bind-map ρ ↝-refl = ↝-refl
ren-bind-map ρ (↝-trans s₁ s₂) = ↝-trans (ren-bind-map ρ s₁) (ren-bind-map ρ s₂)

rbm : ∀ {Δ₁ Δ₂ Δ₃ : TyCtx}{Σ₁ : BindCtx Δ₁}{Σ₂ : BindCtx Δ₂}
        (ρ₁ : TyVar Δ₁ → TyVar Δ₂)
        (ρ₂ : TyVar Δ₂ → TyVar Δ₃)
  → map (ren-pair ρ₁) Σ₁ ↝ Σ₂
  → map (ren-pair (ρ₁ ⨟ᵗ ρ₂)) Σ₁ ↝ map (ren-pair ρ₂) Σ₂
rbm ρ₁ ρ₂ s = (let s' = ren-bind-map ρ₂ s in s')

⤊ᵇ : ∀{Δ}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ}{Γ}{A}
  → Σ ↝ Σ′
  → Δ ∣ Σ ∣ Γ ⊢ A
  → Δ ∣ Σ′ ∣ Γ ⊢ A
⤊ᵇ ↝-refl M = M
⤊ᵇ ↝-extend M = ⇑ᵇ M
⤊ᵇ (↝-trans a b) M = ⤊ᵇ b (⤊ᵇ a M)

⇧ᵇ : ∀{Δ}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ}{A}{B}
  → Σ ↝ Σ′
  → Δ ∣ Σ ⊢ A ⇒ B
  → Δ ∣ Σ′ ⊢ A ⇒ B
⇧ᵇ ↝-extend c = rename-crcn-bind Sᵇ c
⇧ᵇ ↝-refl c = c
⇧ᵇ (↝-trans s s′) c = ⇧ᵇ s′ (⇧ᵇ s c)

{- Reduction -}

infix 2 _∥_∥_⊢_∋_—→_∣_∣_∣_⊢_
data _∥_∥_⊢_∋_—→_∣_∣_∣_⊢_ : ∀ (Δ₁ : TyCtx) → (Σ₁ : BindCtx Δ₁)
  → (Γ : Ctx Δ₁) → (A : Type Δ₁) → (Δ₁ ∣ Σ₁ ∣ Γ ⊢ A) 
  → (Δ₂ : TyCtx)
  → (ρ : Δ₁ ⇒ᵣ Δ₂)
  → (Σ₂ : BindCtx Δ₂)
  → (s : (map (ren-pair ρ) Σ₁) ↝ Σ₂)
  → (Δ₂ ∣ Σ₂ ∣ ren-ctx ρ Γ ⊢ ren-type ρ A)
  → Set where
  
  pure : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{M N : Δ ∣ Σ ∣ Γ ⊢ A}
    → M —→ N
    → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ N

  β-ν : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
      {N : (Δ ,typ) ∣ (Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ ∣ ⟰ Γ ⊢ (⇑ᵗ B)}
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (ν A · N) —→ (Δ ,typ) ∣ Sᵗ ∣ ((Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ) ∣ ↝-extend ⊢ N

  ξ-·₁ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵣ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
      {s : map (ren-pair ρ) Σ ↝ Σ′}
      {Γ : Ctx Δ}{A B}
      {L : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {L′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ ren-type ρ (A ⇒ B)}
      {M : Δ ∣ Σ ∣ Γ ⊢ A}
    → Δ ∥ Σ ∥ Γ ⊢ (A ⇒ B) ∋ L —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ L′
      ------------------------------------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (L · M) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ (L′ · ⤊ᵇ s (rename-ty ρ M))

  ξ-·₂ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵣ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
      {s : map (ren-pair ρ) Σ ↝ Σ′}
      {Γ : Ctx Δ}{A B}
      {V : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {M : Δ ∣ Σ ∣ Γ ⊢ A} {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ ren-type ρ A}
    → Value V
    → Δ ∥ Σ ∥ Γ  ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
      ----------------------------------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (V · M) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ ⤊ᵇ s (rename-ty ρ V) · M′

  blame-·₁ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B}{M : Δ ∣ Σ ∣ Γ ⊢ A}
      ----------------------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (blame · M) —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ blame

  blame-·₂ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B}
      {V : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
    → Value V
      ----------------------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (V · blame) —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ blame
    
  ξ-◯ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵣ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
     {s : map (ren-pair ρ) Σ ↝ Σ′}
     {Γ : Ctx Δ}{A}
     {M : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
     {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ ren-type ρ (`∀ A)}
     {X : TyVar Δ}
   → Δ ∥ Σ ∥ Γ ⊢ (`∀ A) ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
     --------------------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ A [ X ]ᵗ ∋ (M ◯ X) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ (M′ ◯ ρ X)

  blame-◯ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{X : TyVar Δ}
     ---------------------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ A [ X ]ᵗ ∋ (_◯_{A = A} blame X) —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ blame

  ξ-⟨⟩ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵣ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
     {s : map (ren-pair ρ) Σ ↝ Σ′}
     {Γ : Ctx Δ}{A}{B}
     {M : Δ ∣ Σ ∣ Γ ⊢ A} {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ ren-type ρ A}
     {c : Δ ∣ Σ ⊢ A ⇒ B}
   → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
     -----------------------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ B ∋ (M ⟨ c ⟩) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ (M′ ⟨ ⇧ᵇ s (rename-crcn ρ c) ⟩)

  blame-⟨⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{B}{c : Δ ∣ Σ ⊢ A ⇒ B}
     -------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ B ∋ (blame ⟨ c ⟩) —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ blame

{- Reflexive and transitive closure -}

infix  2 _∥_∥_⊢_∋_—↠_∣_∣_∣_⊢_
--infix  1 begin_
--infixr 2 _—→⟨_⟩_
infix  3 _∎

data _∥_∥_⊢_∋_—↠_∣_∣_∣_⊢_ : ∀ (Δ₁ : TyCtx) → (Σ₁ : BindCtx Δ₁)
  → (Γ : Ctx Δ₁) → (A : Type Δ₁) → (Δ₁ ∣ Σ₁ ∣ Γ ⊢ A) 
  → (Δ₂ : TyCtx)
  → (ρ : Δ₁ ⇒ᵣ Δ₂)
  → (Σ₂ : BindCtx Δ₂)
  → (s : (map (ren-pair ρ) Σ₁) ↝ Σ₂)
  → (Δ₂ ∣ Σ₂ ∣ ren-ctx ρ Γ ⊢ ren-type ρ A)
  → Set where

  _∎ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}
    → (M : Δ ∣ Σ ∣ Γ ⊢ A)
      ---------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —↠ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ M

  step—→ : ∀{Δ₁ Δ₂ Δ₃}{Σ₁ Σ₂ Σ₃}{Γ}{A}{ρ₁}{s₁}{ρ₂}{s₂}
      (L : Δ₁ ∣ Σ₁ ∣ Γ ⊢ A)
      {M : Δ₂ ∣ Σ₂ ∣ ren-ctx ρ₁ Γ ⊢ ren-type ρ₁ A}
      {N : Δ₃ ∣ Σ₃ ∣ ren-ctx ρ₂ (ren-ctx ρ₁ Γ) ⊢ ren-type ρ₂ (ren-type ρ₁ A)}
    → Δ₁ ∥ Σ₁ ∥ Γ ⊢ A ∋ L —→ Δ₂ ∣ ρ₁ ∣ Σ₂ ∣ s₁ ⊢ M
    → Δ₂ ∥ Σ₂ ∥ ren-ctx ρ₁ Γ ⊢ ren-type ρ₁ A ∋ M —↠ Δ₃ ∣ ρ₂ ∣ Σ₃ ∣ s₂ ⊢ N
      ---------------------------------------------------------------------------
    → Δ₁ ∥ Σ₁ ∥ Γ ⊢ A ∋ L —↠ Δ₃ ∣ (ρ₁ ⨟ᵗ ρ₂) ∣ Σ₃ ∣ ↝-trans (rbm ρ₁ ρ₂ s₁) s₂ ⊢ N


{- Progress -}

data Progress {Δ}{Σ}{A} (M : Δ ∣ Σ ∣ ∅ ⊢ A) : Set where
  step : ∀ {Δ′}{ρ}{Σ′}{s} {N : Δ′ ∣ Σ′ ∣ ∅ ⊢ ren-type ρ A}
    → Δ ∥ Σ ∥ ∅ ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ N
    → Progress M
    
  done :
      Value M
      -----------
    → Progress M

  blame :
      M ≡ blame
    → Progress M

progress-seal : ∀{Δ Σ}{Y}{A}
  → unique Σ
  → (M : Δ ∣ Σ ∣ ∅ ⊢ (` Y))
  → (∋Y : Σ ∋ Y := A)
  → (c : Crcn Δ Σ (` Y) A)
  → Value M
  → Progress (M ⟨ ∋Y ↑ ⟩)
progress-seal {A = A} u (V ⟨ ∋X ↓ ⟩) ∋Y c (vM ⟨X↓⟩)
    with lookup-unique ∋X ∋Y u
... | refl = step (pure (⟨X↓⟩⟨X↑⟩{B = A}))

progress : ∀ {Δ Σ A} → (M : Δ ∣ Σ ∣ ∅ ⊢ A) → unique Σ → Progress M
progress (# k) u = done (# k)
progress (ƛ N) u = done (ƛ N)
progress (L · M) u with progress L u
... | step L→L′ = step (ξ-·₁ L→L′)
... | done (V-⟨↦⟩ v) = step (pure β-⟨c→d⟩)
... | blame refl = step blame-·₁
... | done (ƛ N) with progress M u
... | step M→M′ = step (ξ-·₂ (ƛ N) M→M′)
... | done w = step (pure (β w))
... | blame refl = step (blame-·₂ (ƛ N))
progress (Λ N) u = done (Λ N)
progress (M ◯ X) u with progress M u
... | step M→M′ = step (ξ-◯ M→M′)
... | done (Λ N) = step (pure β-Λ)
... | done (_⟨∀_⟩ v) = step (pure β-⟨∀⟩)
... | done (_⟨𝒢_⟩ v) = step (pure β-⟨𝒢⟩)
... | blame refl = step blame-◯
progress (_⟨_⟩{A = A } M c) u with progress M u
... | step M→M′ = step (ξ-⟨⟩ M→M′)
... | blame refl = step blame-⟨⟩
... | done v
    with c
... | id = step (pure (⟨id⟩{B = A}))
... | c ↦ d = done (V-⟨↦⟩ v)
... | c ⨟ d = step (pure β-⟨c⨟d⟩)
... | `∀ c = done (_⟨∀_⟩ v)
... | 𝒢 c = done (_⟨𝒢_⟩ v)
... | ℐ c = step (pure β-⟨ℐ⟩)
... | X ↓ = done (v ⟨X↓⟩)
... | X ↑ = progress-seal u M X c v
... | G ! = done (v ⟨G!⟩)
... | H `?
    with v
... | _⟨G!⟩ {G = G} v′
    with G ≡ᵍ H
... | yes refl = step (pure ⟨G!⟩⟨G?⟩)
... | no neq = step (pure (⟨G!⟩⟨H?⟩ neq))
progress blame u = blame refl
progress (ν A · N) u = step β-ν

{--- Type Safety ---}

helper : ∀{Δ}{Σ : BindCtx Δ}{B : Type (Δ ,typ)}{X}
  → map (ren-pair Sᵗ) Σ ∋ Sᵗ X := B
  → ((A : Type Δ) → Σ ∋ X := A → ⊥)
  → ⊥
helper {Δ} {(Y , C) ∷ Σ′} Zᵇ nl = nl C Zᵇ
helper {Δ} {(Y , C) ∷ Σ′} (Sᵇ ∋Sx) nl = helper ∋Sx (λ A x → nl A (Sᵇ x))

unique-⤊ : ∀ {Δ}{Σ : BindCtx Δ} → unique Σ → unique (⤊ Σ)
unique-⤊ Umt = Umt
unique-⤊ (Ucons u nolook) = Ucons (unique-⤊ u) λ { B y → helper y nolook }

suc-bind-zero : ∀{Δ}{Σ : BindCtx Δ}{C}
  → map (ren-pair Sᵗ) Σ ∋ Zᵗ := C
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

unique-preservation : ∀ {Δ Δ′}{ρ : Δ ⇒ᵣ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
     {s : map (ren-pair ρ) Σ ↝ Σ′} {Γ : Ctx Δ}{A}
     {M : Δ ∣ Σ ∣ Γ ⊢ A}
     {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ ren-type ρ A}
  → unique Σ
  → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
  → unique Σ′ 
unique-preservation u (pure x) = u
unique-preservation {Σ = Σ} u (β-ν{A = A}) = unique-extend{A = A} Σ u
unique-preservation u (ξ-·₁ M→M′) = unique-preservation u M→M′
unique-preservation u (ξ-·₂ x M→M′) = unique-preservation u M→M′
unique-preservation u blame-·₁ = u
unique-preservation u (blame-·₂ x) = u
unique-preservation u (ξ-◯ M→M′) = unique-preservation u M→M′
unique-preservation u blame-◯ = u
unique-preservation u (ξ-⟨⟩ M→M′) = unique-preservation u M→M′
unique-preservation u blame-⟨⟩ = u

type-safety : ∀{Δ Δ′}{ρ}{Σ}{Σ′}{s}{A}{M}{N}
  → unique Σ
  → Δ ∥ Σ ∥ ∅ ⊢ A ∋ M —↠ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ N
  → Progress N
type-safety u (M ∎) = progress M u
type-safety u (step—→ _ M→M′ M′→N) = type-safety (unique-preservation u M→M′) M′→N
