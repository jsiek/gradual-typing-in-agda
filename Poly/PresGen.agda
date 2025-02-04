{-# OPTIONS --rewriting --allow-unsolved-metas  #-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Var using (Var)
open import Poly.CastCalculus

module Poly.PresGen where

ty-ren-cast : ∀ Γ c α D C B
  → typ ∷ Γ ⊢ c ⦂ (⟪ renᵗ suc ⟫ᵗ D) ↝ C
  → Γ ∋ α ⦂ bnd B
  → Γ ⊢ c [ α ]ᵣ ⦂ D ↝ C ⦗ α ⦘ᵣ
ty-ren-cast Γ c α D C B = {!!}

preservation-gen : ∀ {Γ}{V : Term}{c}{α : Var}{A : Type}
  → Γ ⊢ V ⟨ gen c ⟩ 【 α 】 ⦂ A
  → Γ ⊢ V ⟨ c [ α ]ᵣ ⟩  ⦂ A
preservation-gen {Γ}{V}{c}{α}{A} (⊢-tyapp{A = C}{B = B} (⊢-cast{A = D} ⊢V (wt-gen ⊢c)) ∋α) =
  ⊢-cast ⊢V (ty-ren-cast Γ c α D C B ⊢c ∋α)

  


