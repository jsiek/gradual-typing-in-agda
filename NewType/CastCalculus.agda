{-# OPTIONS --rewriting #-}

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
open import Sig
open import Var

module NewType.CastCalculus where

{- Base types -}

data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base

_≡$?_ : (ι : Base) → (ι′ : Base) → Dec (ι ≡ ι′)
′ℕ  ≡$? ′ℕ  =  yes refl
′ℕ  ≡$? ′𝔹  =  no (λ ())
′𝔹  ≡$? ′ℕ  =  no (λ ())
′𝔹  ≡$? ′𝔹  =  yes refl

{- Types -}

infixr 7 _⇒_
infix  8 $ₜ_

data Type : Set where
  ★ : Type
  $ₜ_ : (ι : Base) → Type
  _⇒_ : (A : Type) → (B : Type) → Type
  `_ : Var → Type

{------------------------ Terms --------------------------------}

infixl 7  _·_

data Lit : Set where
  Num : ℕ → Lit
  Bool : 𝔹 → Lit

typeof : Lit → Base
typeof (Num n) = ′ℕ
typeof (Bool b) = ′𝔹

data Op : Set where
  op-lam : Op
  op-app : Op
  op-lit : Lit → Op
  op-inject : Op
  op-project : Op
  op-blame : Op
  op-new : Op
  op-base : Base → Op
  op-fun : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit c) = []
sig op-inject = ■ ∷ ■ ∷ []
sig op-project = ■ ∷ ■ ∷ []
sig op-blame = []
sig op-new = (ν ■) ∷ []
sig (op-base ι) = []
sig op-fun = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $ c = (op-lit c) ⦅ nil ⦆
pattern _⟨_!⟩ M G = op-inject ⦅ cons (ast M) (cons (ast G) nil) ⦆
pattern _⟨_?⟩ M H = op-project ⦅ cons (ast M) (cons (ast H) nil) ⦆
pattern blame = op-blame ⦅ nil ⦆
pattern $ᵍ_ ι = (op-base ι) ⦅ nil ⦆
pattern ★⇒★ = op-fun ⦅ nil ⦆

{----- Ground Types ---}

data Ground : Term → Set where
  gnd-base : (ι : Base) → Ground ($ᵍ ι)
  gnd-fun : Ground ★⇒★
  gnd-var : (x : Var) → Ground (` x)

{--------------------- Values -----------------------------}

data Value : Term → Set where
  ƛ̬_ : (N : Term) → Value (ƛ N)
  $̬ : (c : Lit) → Value ($ c)
  _〈_〉 : ∀{V G} → Value V → Ground G → Value (V ⟨ G !⟩)

value : ∀ {V : Term}
  → (v : Value V)
    -------------
  → Term
value {V = V} v  =  V  

rename-val : ∀ {V : Term}
  → (ρ : Rename)
  → Value V
    ------------------
  → Value (rename ρ V)
rename-val ρ (ƛ̬ N)    =  ƛ̬ (rename (extr ρ) N)
rename-val ρ ($̬ c)    =  $̬ c
rename-val ρ (_〈_〉 {V}{G} v g) =  (rename-val ρ v) 〈 rG g 〉
  where
  rG : ∀{G} → Ground G → Ground (rename ρ G)
  rG {.($ᵍ ι)} (gnd-base ι) = gnd-base ι
  rG {.★⇒★} gnd-fun = gnd-fun
  rG {.(` x)} (gnd-var x) = gnd-var (ρ x)

{-  The following is not true.
sub-val : ∀ {V}
  → (σ : Subst)
  → Value V
  → Value (⟪ σ ⟫ V)
sub-val σ (ƛ̬ N) = ƛ̬ ⟪ ext σ ⟫ N
sub-val σ ($̬ c) = $̬ c
sub-val σ (V 〈 g 〉)  =  (sub-val σ V) 〈 {!!} 〉
-}
