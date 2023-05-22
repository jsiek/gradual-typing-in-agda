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
  op-lam : Op
  op-app : Op
  op-tyabs : Op
  op-tyapp : Op

sig : Op → List Sig
sig (op-nat n) = []
sig op-lam = (nu ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-tyabs = (nu ■) ∷ []
sig op-tyapp = ■ ∷ ■ ∷ []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern $ n = (op-nat n) ⦅ nil ⦆
pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern Λ N  = op-tyabs ⦅ cons (bind (ast N)) nil ⦆
infix 5 _【_】
pattern _【_】 L α = op-tyapp ⦅ cons (ast L) (cons (ast α) nil) ⦆
