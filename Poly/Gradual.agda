{-# OPTIONS --rewriting #-}
{-

  This gradual version of System F is similar to System F_G of
  Igarashi, Sekiyama, and Igarashi (ICFP 2017).

  todo: list the subtle differences
  * no monomorphic restriction on all~any, any~all, and any⊑all

-}

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig renaming (ν to nu)
open import Var using (Var)

module Poly.Gradual where

open import Poly.Types

{-------------      Terms    -------------}

data Op : Set where
  op-nat : ℕ → Op
  op-lam : Type → Op
  op-app : Op
  op-tyabs : Op
  op-tyapp : Type → Op

sig : Op → List Sig
sig (op-nat n) = []
sig (op-lam A) = (nu ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-tyabs = (nu ■) ∷ []
sig (op-tyapp A) = ■ ∷ []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern $ᵍ n = (op-nat n) ⦅ nil ⦆
pattern λᵍ A N  = (op-lam A) ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _˙_
pattern _˙_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern Λᵍ N  = op-tyabs ⦅ cons (bind (ast N)) nil ⦆
infix 5 _◎_
pattern _◎_ L B = (op-tyapp B) ⦅ cons (ast L) nil ⦆

{----------------------- Values ------------------------}

data Value : Term → Set where

  V-nat : ∀ {n : ℕ}
      -------------
    → Value ($ᵍ n)
    
  V-λᵍ : ∀ {A : Type}{N : Term}
      ---------------------------
    → Value (λᵍ A N)

  V-Λᵍ : ∀ {N : Term}
      ---------------------------
    → Value (Λᵍ N)
    
{-------------      Type System    -------------}

infix 1 _⊢ᵍ_⦂_
data _⊢ᵍ_⦂_ : TyEnv → Term → Type → Set where

  ⊢ᵍ-nat : ∀{Γ} → ∀ n
        -----------------
      → Γ ⊢ᵍ $ᵍ n ⦂ Nat

  ⊢ᵍ-var : ∀{Γ}{x}{A}
      → Γ ∋ x ⦂ trm A
        ---------------
      → Γ ⊢ᵍ ` x ⦂ A

  ⊢ᵍ-lam : ∀{Γ}{N}{A}{B}
     → Γ ⊢ A ok
     → trm A ∷ Γ ⊢ᵍ N ⦂ B
       -------------------
     → Γ ⊢ᵍ λᵍ A N ⦂ A ⇒ B
     
  ⊢ᵍ-app : ∀{Γ}{L}{M}{A}{B}{A′}
     → Γ ⊢ᵍ L ⦂ A ⇒ B
     → Γ ⊢ᵍ M ⦂ A′
     → [] ⊢ A′ ~ A
       -----------------
     → Γ ⊢ᵍ L ˙ M ⦂ B

  ⊢ᵍ-app★ : ∀{Γ}{L}{M}{A}
     → Γ ⊢ᵍ L ⦂ ★
     → Γ ⊢ᵍ M ⦂ A
       --------------
     → Γ ⊢ᵍ L ˙ M ⦂ ★

  ⊢ᵍ-tyabs : ∀{Γ}{V}{A}
     → Value V
     → typ ∷ Γ ⊢ᵍ V ⦂ A
       ---------------
     → Γ ⊢ᵍ Λᵍ V ⦂ ∀̇ A

  ⊢ᵍ-tyapp : ∀{Γ}{L}{A}{B}
     → Γ ⊢ᵍ L ⦂ ∀̇ A
     → Γ ⊢ B ok
       -------------------
     → Γ ⊢ᵍ L ◎ B ⦂ A ⦗ B ⦘

  ⊢ᵍ-tyapp★ : ∀{Γ}{L}{B}
     → Γ ⊢ᵍ L ⦂ ★
     → Γ ⊢ B ok
       -------------
     → Γ ⊢ᵍ L ◎ B ⦂ ★

