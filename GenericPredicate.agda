open import Data.List
  using (List; []; _∷_; length)
open import Data.Vec
  using (Vec)
  renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Unit renaming (tt to unit)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)

open import PreCastStructure
open import Syntax

module GenericPredicate (precast : PreCastStruct) where

  open import ParamCastCalculusSyntax precast using (Op; sig)
  open Op

  module GenericPredicatePatterns {ℓ} {I : Set ℓ}
    (𝑉 : List I → Var → I → I → Set)
    (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set) where

    open import ABTPredicate Op sig 𝑉 𝑃

    pattern ⊢` ∋x = var-p ∋x refl

    pattern ⊢ƛ A ⊢N eq = op-p {op = op-lam A} (cons-p (bind-p (ast-p ⊢N)) nil-p) eq
    pattern ⊢ƛ-refl A ⊢N = ⊢ƛ A ⊢N (⟨ refl , refl ⟩)

    pattern ⊢· ⊢L ⊢M eq = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq
    pattern ⊢·-refl ⊢L ⊢M = ⊢· ⊢L ⊢M refl

    pattern ⊢$ r p eq = op-p {op = op-lit r p} nil-p eq
    pattern ⊢$-refl r p = ⊢$ r p refl

    pattern ⊢if ⊢L ⊢M ⊢N eq = op-p {op = op-if}
                                 (cons-p (ast-p ⊢L)
                                         (cons-p (ast-p ⊢M)
                                                 (cons-p (ast-p ⊢N) nil-p))) eq
    pattern ⊢if-refl ⊢L ⊢M ⊢N = ⊢if ⊢L ⊢M ⊢N (⟨ ⟨ refl , refl ⟩ , refl ⟩)

    pattern ⊢cons ⊢M ⊢N eq = op-p {op = op-cons}
                           (cons-p (ast-p ⊢M) (cons-p (ast-p ⊢N) nil-p)) eq
    pattern ⊢cons-refl ⊢M ⊢N = ⊢cons ⊢M ⊢N refl

    pattern ⊢fst ⊢M eq = op-p {op = op-fst} (cons-p (ast-p ⊢M) nil-p) eq
    pattern ⊢fst-refl ⊢M = ⊢fst ⊢M (⟨ _ , refl ⟩)

    pattern ⊢snd ⊢M eq = op-p {op = op-snd} (cons-p (ast-p ⊢M) nil-p) eq
    pattern ⊢snd-refl ⊢M = ⊢snd ⊢M (⟨ _ , refl ⟩)

    pattern ⊢inl B ⊢M eq = op-p {op = op-inl B} (cons-p (ast-p ⊢M) nil-p) eq
    pattern ⊢inl-refl B ⊢M = ⊢inl B ⊢M refl

    pattern ⊢inr A ⊢M eq = op-p {op = op-inr A} (cons-p (ast-p ⊢M) nil-p) eq
    pattern ⊢inr-refl A ⊢M = ⊢inr A ⊢M refl

    pattern ⊢case A B ⊢L ⊢M ⊢N eq = op-p {op = op-case A B}
                                     (cons-p (ast-p ⊢L)
                                             (cons-p (bind-p (ast-p ⊢M))
                                                     (cons-p (bind-p (ast-p ⊢N)) nil-p))) eq
    pattern ⊢case-refl A B ⊢L ⊢M ⊢N = ⊢case A B ⊢L ⊢M ⊢N (⟨ ⟨ refl , refl ⟩ , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩)

    pattern ⊢cast c ⊢M eq = op-p {op = op-cast c} (cons-p (ast-p ⊢M) nil-p) eq
    pattern ⊢cast-refl c ⊢M = ⊢cast c ⊢M (⟨ refl , refl ⟩)

    pattern ⊢wrap c i ⊢M eq = op-p {op = op-wrap c i} (cons-p (ast-p ⊢M) nil-p) eq
    pattern ⊢wrap-refl c i ⊢M = ⊢wrap c i ⊢M (⟨ refl , refl ⟩)

    pattern ⊢blame ℓ eq = op-p {op = op-blame ℓ} nil-p eq
    pattern ⊢blame-refl ℓ = ⊢blame ℓ unit
