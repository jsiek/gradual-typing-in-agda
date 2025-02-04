{-# OPTIONS --rewriting --allow-unsolved-metas  #-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Var using (Var)
open import Poly.CastCalculus

module Poly.PresBeta where

subst-pres : ∀ Γ N W A B 
  → trm B ∷ Γ ⊢ N ⦂ A
  → Γ ⊢ W ⦂ B
  → Γ ⊢ N [ W ] ⦂ A
subst-pres Γ N W A B ⊢N ⊢W = {!!}

preservation-beta : ∀ {Γ}{N W : Term}{A : Type}
  → Γ ⊢ (ƛ N) · W ⦂ A
  → Γ ⊢ N [ W ] ⦂ A
preservation-beta {Γ}{N}{W}{A} (⊢-app (⊢-lam{A = B}{B = A} ⊢B ⊢N) ⊢W) =
  subst-pres Γ N W A B ⊢N ⊢W


