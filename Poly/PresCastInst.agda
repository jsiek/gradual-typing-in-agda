{-# OPTIONS --rewriting  --allow-unsolved-metas #-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Var using (Var)
open import Poly.CastCalculus

module Poly.PresCastInst where

weaken-term : ∀ {Γ V A B}
  → Γ ⊢ V ⦂ A
  → bnd B ∷ Γ ⊢ rename suc V ⦂ (renameᵗ suc A)
weaken-term {Γ}{V}{A}{B} ⊢V = {!!}

preservation-cast-inst : ∀ {Γ}{V : Term}{c}{A : Type}
  → Γ ⊢ V ⟨ inst c ⟩ ⦂ A
  → Γ ⊢ (ν (rename suc V) 【 0 】 ⟨ c ⟩)  ⦂ A
preservation-cast-inst {Γ} {V} {c} {A} (⊢-cast ⊢V (wt-inst ⊢c)) =
  ⊢-ν (⊢-cast (⊢-tyapp (weaken-term ⊢V) bndZ) {!!})



  


