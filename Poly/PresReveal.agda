{-# OPTIONS --rewriting --allow-unsolved-metas  #-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Var using (Var)
open import Poly.CastCalculus

module Poly.PresReveal where

lookup-unique : ∀ {Γ α A B}
   → Γ ∋ α ⦂ bnd A
   → Γ ∋ α ⦂ bnd B
   → B ≡ A
lookup-unique {Γ}{α}{A}{B} ∋α1 ∋α2 = {!!}

preservation-reveal : ∀ {Γ}{V : Term}{α : Var}{A : Type}
  → Γ ⊢ V ⟨ ` α ↡ ⟩ ⟨ ` α ↟ ⟩ ⦂ A
  → Γ ⊢ V ⦂ A
preservation-reveal {V}{α} (⊢-cast (⊢-cast ⊢V (wt-seal ∋α1)) (wt-unseal ∋α2))
    rewrite lookup-unique ∋α1 ∋α2 = ⊢V

