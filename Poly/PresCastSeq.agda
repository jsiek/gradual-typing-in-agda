{-# OPTIONS --rewriting #-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Var using (Var)
open import Poly.CastCalculus

module Poly.PresCastSeq where

preservation-cast-seq : ∀ {Γ}{V : Term}{c d}{A : Type}
  → Γ ⊢ V ⟨ c ⍮ d ⟩ ⦂ A
  → Γ ⊢ V ⟨ c ⟩ ⟨ d ⟩  ⦂ A
preservation-cast-seq {Γ} {V} {c} {d} {A} (⊢-cast ⊢V (wt-seq ⊢c ⊢d)) = ⊢-cast (⊢-cast ⊢V ⊢c) ⊢d



  


