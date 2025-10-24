module PolyBlame.PolyBlame where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)

postulate
  extensionality : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁ }{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Variables are de Bruijn indices
Var = ℕ

{-- Renaming (Language Independent Stuff) --}
Rename : Set
Rename = Var → Var

infixr 6 _•ᵣ_
_•ᵣ_ : Var → Rename → Rename
(y •ᵣ ρ) 0 = y
(y •ᵣ ρ) (suc x) = ρ x

⟰ᵣ : Rename → Rename
⟰ᵣ ρ x = suc (ρ x)

extr : Rename → Rename
extr ρ = 0 •ᵣ ⟰ᵣ ρ

idr : Rename
idr x = x

-- Syntax of Polymorphic Cast Calculus

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infixl 7 _◯_
infix  9 `_
infix  9 #_

data Grnd : Set where
  ★⇒★ : Grnd
  `ℕ  : Grnd
  `_ : Var → Grnd
  
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type
  ★   : Type
  `∀_  : Type → Type
  `_ : Var → Type

data Crcn : Set where
 id : Crcn
 _↦_ : Crcn → Crcn → Crcn
 _⨟_ : Crcn → Crcn → Crcn
 `∀_ : Crcn → Crcn
 𝒢_ : Crcn → Crcn
 ℐ_ : Crcn → Crcn
 _↓ : Var → Crcn
 _↑ : Var → Crcn
 _! : Grnd → Crcn
 _`? : Grnd → Crcn

data Expr : Set where
  `_ : Var → Expr
  #_ : ℕ → Expr
  ƛ_ : Expr → Expr
  _·_ : Expr → Expr → Expr
  Λ_ : Expr → Expr
  _◯_ : Expr → Var → Expr
  ν_·_ : Type → Expr → Expr
  _⟨_⟩ : Expr → Crcn → Expr
  blame : Expr

-- Type Renaming in Grnd
rename-grnd : Rename → Grnd → Grnd
rename-grnd ρ ★⇒★ = ★⇒★
rename-grnd ρ `ℕ = `ℕ
rename-grnd ρ (` X) = ` ρ X

-- Type Renaming in Crcn
rename-crcn : Rename → Crcn → Crcn
rename-crcn ρ id = id
rename-crcn ρ (c ↦ d) = (rename-crcn ρ c) ↦ (rename-crcn ρ d)
rename-crcn ρ (c ⨟ d) = (rename-crcn ρ c) ⨟ (rename-crcn ρ d)
rename-crcn ρ (`∀ c) = `∀ (rename-crcn (extr ρ) c)
rename-crcn ρ (𝒢 c) = 𝒢 (rename-crcn (extr ρ) c)
rename-crcn ρ (ℐ c) = ℐ (rename-crcn (extr ρ) c)
rename-crcn ρ (X ↓) = (ρ X) ↓
rename-crcn ρ (X ↑) = (ρ X) ↑
rename-crcn ρ (G !) = (rename-grnd ρ G) !
rename-crcn ρ (G `?) = (rename-grnd ρ G) `?

-- Type Renaming in Expr
rename-ty : Rename → Expr → Expr
rename-ty ρ (` x) = ` ρ x
rename-ty ρ (# k) = # k
rename-ty ρ (ƛ M) = rename-ty (extr ρ) M
rename-ty ρ (L · M) = (rename-ty ρ L) · (rename-ty ρ M)
rename-ty ρ (Λ N) = Λ (rename-ty ρ N)
rename-ty ρ (L ◯ X) = (rename-ty ρ L) ◯ (ρ X)
rename-ty ρ (ν A · N) = ν A · (rename-ty ρ N)
rename-ty ρ (M ⟨ c ⟩) = (rename-ty ρ M) ⟨ rename-crcn ρ c ⟩
rename-ty ρ blame = blame

-- Term Renaming
rename : Rename → Expr → Expr
rename ρ (` x) = ` ρ x
rename ρ (# k) = # k
rename ρ (ƛ M) = ƛ (rename (extr ρ) M)
rename ρ (L · M) = (rename ρ L) · (rename ρ M)
rename ρ (Λ N) = Λ (rename ρ N)
rename ρ (L ◯ X) = (rename ρ L) ◯ X
rename ρ (ν A · N) = ν A · (rename ρ N)
rename ρ (M ⟨ c ⟩) = (rename ρ M) ⟨ c ⟩
rename ρ blame = blame

{--- Term Substitution --}
Subst : Set
Subst = Var → Expr

infixr 6 _•_
_•_ : Expr → Subst → Subst
(M • σ) 0 = M
(M • σ) (suc x) = σ x

⟰ : Subst → Subst
⟰ σ x = rename suc (σ x)

exts : Subst → Subst
exts σ = ` 0 • ⟰ σ

⟰ᵗ : Subst → Subst
⟰ᵗ σ x = rename-ty suc (σ x)

sub : Subst → Expr → Expr
sub σ (` x) = σ x
sub σ (# k) = # k
sub σ (ƛ N) = ƛ (sub (exts σ) N)
sub σ (L · M) = (sub σ L) · (sub σ M)
sub σ (Λ N) = Λ (sub (⟰ᵗ σ) N)
sub σ (M ◯ X) = (sub σ M) ◯ X
sub σ (ν A · N) = ν A · (sub (⟰ᵗ σ) N)
sub σ (M ⟨ c ⟩) = (sub σ M) ⟨ c ⟩
sub σ blame = blame

infixr 5 _;_
_;_ : Subst → Subst → Subst
(σ ; τ) x = sub τ (σ x)

ids : Subst
ids x = ` x

_[_] : Expr → Expr → Expr
N [ M ] =  sub (M • ids) N

{--- Values ---}

data Value : Expr → Set where
  V-ƛ : ∀{N} → Value (ƛ N)
  V-# : ∀{k} → Value (# k)
  V-Λ : ∀{V} → Value V → Value (Λ V)
  V-! : ∀{V G} → Value V → Value (V ⟨ G ! ⟩)
  V-↦ : ∀{V c d} → Value V → Value (V ⟨ c ↦ d ⟩)
  V-𝒢 : ∀{V c} → Value V → Value (V ⟨ 𝒢 c ⟩)
  V-∀ : ∀{V c} → Value V → Value (V ⟨ `∀ c ⟩)

{--- Frames ---}

data Frame : Set where
  □·_ : Expr → Frame
  _·□ : Expr → Frame
  □⟨_⟩ : Crcn → Frame
  □◯_ : Var → Frame
  ν_·□ : Type → Frame

plug : Frame → Expr → Expr
plug (□· M) L = L · M
plug (L ·□) M = L · M
plug □⟨ c ⟩ M = M ⟨ c ⟩
plug (□◯ X) M = M ◯ X
plug ν A ·□ N = ν A · N

{--- Reduction ---}

infix 2 _—→_

data _—→_ : Expr → Expr → Set where

  ξ : ∀{F M N}
    → M —→ N
      ---------------------
    → plug F M —→ plug F N

  β-ƛ : ∀{N W}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀{V X}
      -----------------------------------
    → (Λ V) ◯ X —→ rename-ty (X •ᵣ idr) V

  β-↦ : ∀{V W c d}
      ----------------------------------------
    → V ⟨ c ↦ d ⟩ · W —→ (V · (W ⟨ c ⟩)) ⟨ d ⟩
    
  β-∀ : ∀{V c X}
      ------------------------------------------------------
    → V ⟨ `∀ c ⟩ ◯ X —→ (V ◯ X) ⟨ rename-crcn (X •ᵣ idr) c ⟩

  β-𝒢 : ∀{V c X}
      -----------------------------------------------
    → V ⟨ 𝒢 c ⟩ ◯ X —→ V ⟨ rename-crcn (X •ᵣ idr) c ⟩

  cast-ℐ : ∀{V c}
      -----------------------------------------------------
    → (V ⟨ ℐ c ⟩) —→ ν ★ · (((rename-ty suc V) ◯ 0) ⟨ c ⟩)

  cast-id : ∀ {V}
      -------------
    → V ⟨ id ⟩ —→ V

  cast-collapse : ∀{V G}
      -----------------------
    → V ⟨ G ! ⟩ ⟨ G `? ⟩ —→ V

  cast-conflict : ∀{V G H}
    → G ≢ H
      ---------------------------
    → V ⟨ G ! ⟩ ⟨ H `? ⟩ —→ blame

  cast-⨟ : ∀{V c d}
      ----------------------------
    → V ⟨ c ⨟ d ⟩ —→ V ⟨ c ⟩ ⟨ d ⟩

