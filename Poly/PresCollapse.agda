{-# OPTIONS --rewriting #-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Var using (Var)
open import Poly.CastCalculus

module Poly.PresCollapse where

preservation-collapse : ∀ {Γ}{V : Term}{G}{A : Type}
  → Γ ⊢ V ⟨ G !! ⟩ ⟨ G ?? ⟩ ⦂ A
  → Γ ⊢ V  ⦂ A
preservation-collapse {Γ} {V} {G} {.(gnd⇒ty g2)} (⊢-cast (⊢-cast ⊢V (wt-inj g1)) (wt-proj g2))
    rewrite unique-ground g1 g2 = ⊢V


  


