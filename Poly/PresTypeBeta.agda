{-# OPTIONS --rewriting --allow-unsolved-metas  #-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Var using (Var)
open import Poly.CastCalculus

module Poly.PresTypeBeta where

ty-ren-pres : ∀ Γ N A α B
  → typ ∷ Γ ⊢ N ⦂ A
  → Γ ∋ α ⦂ bnd B
  → Γ ⊢ N [ α ]ᵣ ⦂ A ⦗ α ⦘ᵣ
ty-ren-pres Γ N A α B ⊢N ∋α = {!!}

preservation-type-beta : ∀ {Γ}{N : Term}{α : Var}{A : Type}
  → Γ ⊢ (Λ N) 【 α 】 ⦂ A
  → Γ ⊢ N [ α ]ᵣ ⦂ A
preservation-type-beta {Γ}{N}{α}{A} (⊢-tyapp{A = C}{B = B} (⊢-tyabs v ⊢V) ∋α) =
    ty-ren-pres Γ N C α B ⊢V ∋α
  


