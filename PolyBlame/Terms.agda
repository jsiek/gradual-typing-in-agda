{-# OPTIONS --rewriting #-}
module PolyBlame.Terms where

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

open import PolyBlame.Types
open import PolyBlame.Coercions
open import PolyBlame.Variables

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

infix  5 ƛ_
infixl 7 _·_
infixl 7 _◯_
infix  9 `_
infix  9 #_

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
     → Δ ∣ Σ ∣ Γ ⊢ A ⇒ B
     
  _·_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)
     → Δ ∣ Σ ∣ Γ ⊢ A
       -------------------
     → Δ ∣ Σ ∣ Γ ⊢ B
     
  Λ_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
     → (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A
       --------------------------
     → Δ ∣ Σ ∣ Γ ⊢ `∀ A
     
  _◯_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
     → Δ ∣ Σ ∣ Γ ⊢ `∀ A
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
      -------------------------------------------
    → Δ ∣ Σ ∣ Γ ⊢ B

{------- Renaming Type Variables ------------}

rename-ty : ∀{Δ₁ Δ₂}{Σ : BindCtx Δ₁}{Γ : Ctx Δ₁}{A : Type Δ₁}
  → (ρ : Δ₁ ⇒ᵗ Δ₂)
  → Δ₁ ∣ Σ ∣ Γ ⊢ A
  → Δ₂ ∣ map (renᵇ ρ) Σ ∣ (ren-ctx ρ Γ) ⊢ renᵗ ρ A
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
  ν (renᵗ ρ A) · N′

infix 6 _[_]ᵀ
_[_]ᵀ : ∀{Δ}{Σ}{Γ}{A} → (Δ ,typ) ∣ Σ ∣ Γ ⊢ A → (X : TyVar Δ)
  → Δ ∣ map (renᵇ (X •ᵗ idᵗ)) Σ ∣ ren-ctx (X •ᵗ idᵗ) Γ ⊢ renᵗ (X •ᵗ idᵗ) A
M [ X ]ᵀ = rename-ty (X •ᵗ idᵗ) M

⇑ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}
  → Δ ∣ Σ ∣ Γ ⊢ A
  → (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ ⇑ᵗ A
⇑ M = rename-ty Sᵗ M

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

⇑ᵇ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{X}{B}
  → Δ ∣ Σ ∣ Γ ⊢ A
  → Δ ∣ (X , B) ∷ Σ ∣ Γ ⊢ A
⇑ᵇ M = rename-bind Sᵇ M

{---- Renaming of Term Variables in Terms ----}

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

{---- Substitution of Term Variables in Terms ----}

_∣_⊢_⇨_ : ∀ (Δ : TyCtx) → BindCtx Δ → Ctx Δ → Ctx Δ → Set
Δ ∣ Σ ⊢ Γ ⇨ Γ′ = ∀ {A} → Γ ∋ A → Δ ∣ Σ ∣ Γ′ ⊢ A

exts : ∀ {Δ : TyCtx}{Σ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{A : Type Δ}
  → Δ ∣ Σ ⊢ Γ ⇨ Γ′
  → Δ ∣ Σ ⊢ (Γ ▷ A) ⇨ (Γ′ ▷ A)
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)

sub-ctx : ∀ {Δ₁ Δ₂ : TyCtx}{r : Δ₁ ⇒ᵗ Δ₂}{Σ : BindCtx Δ₁}{Γ : Ctx Δ₁}{Γ′ : Ctx Δ₁}
  → Δ₁ ∣ Σ ⊢ Γ ⇨ Γ′
  → Δ₂ ∣ map (renᵇ r) Σ ⊢ ren-ctx r Γ ⇨ ren-ctx r Γ′
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
