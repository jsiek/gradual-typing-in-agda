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

  _⟨G!⟩ : ∀{Δ Σ Γ G}{V : Δ ∣ Σ ∣ Γ ⊢ ⌈ G ⌉}
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
           {V : Δ ∣ Σ ∣ Γ ⊢ A}{X}{∋X : Σ ∋ X := A}
    → (V ⟨ ∋X ↓ ⟩ ⟨ ∋X ↑ ⟩) —→ V

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

  ξ-◯ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵣ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
     {s : map (ren-pair ρ) Σ ↝ Σ′}
     {Γ : Ctx Δ}{A}
     {M : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
     {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ ren-type ρ (`∀ A)}
     {X : TyVar Δ}
   → Δ ∥ Σ ∥ Γ ⊢ (`∀ A) ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
     --------------------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ A [ X ]ᵗ ∋ (M ◯ X) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ (M′ ◯ ρ X)

  ξ-⟨⟩ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵣ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
     {s : map (ren-pair ρ) Σ ↝ Σ′}
     {Γ : Ctx Δ}{A}{B}
     {M : Δ ∣ Σ ∣ Γ ⊢ A} {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ ren-type ρ A}
     {c : Δ ∣ Σ ⊢ A ⇒ B}
   → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
     -----------------------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ B ∋ (M ⟨ c ⟩) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ (M′ ⟨ ⇧ᵇ s (rename-crcn ρ c) ⟩)

{- Reflexive and transitive closure -}

{- Progress -}

{- Evaluation -}
