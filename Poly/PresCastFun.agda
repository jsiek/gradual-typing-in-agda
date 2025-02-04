{-# OPTIONS --rewriting --allow-unsolved-metas  #-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Var using (Var)
open import Poly.CastCalculus

module Poly.PresCastFun where

weaken-term-var : ∀ {Γ V A B}
  → Γ ⊢ V ⦂ A
  → trm B ∷ Γ ⊢ rename suc V ⦂ A
weaken-term-var {Γ}{V}{A}{B} ⊢V = {!!}

weaken-term-var-cast : ∀ {Γ c A B A′}
  → Γ ⊢ c ⦂ A ↝ A′ 
  → trm B ∷ Γ ⊢ rename suc c ⦂ A ↝ A′
weaken-term-var-cast {Γ}{c}{A}{B}{A′} ⊢c = {!!}

preservation-cast-fun : ∀ {Γ}{V : Term}{c d}{A : Type}
  → Γ ⊢ V ⟨ c ↪ d ⟩ ⦂ A
  → Γ ⊢ ƛ (((rename suc V) · (` 0 ⟨ (rename suc c) ⟩)) ⟨ (rename suc d) ⟩) ⦂ A
preservation-cast-fun {Γ} {V} {c} {d} {.(_ ⇒ _)} (⊢-cast ⊢V (wt-fun ⊢c ⊢d)) =
  ⊢-lam {!!} (⊢-cast (⊢-app (weaken-term-var ⊢V) (⊢-cast (⊢-var trmZ) (weaken-term-var-cast ⊢c))) (weaken-term-var-cast ⊢d))




