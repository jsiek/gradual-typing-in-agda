open import Denot.Value
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import NewDenotProperties
open import Types
open import Labels
open import PreCastStructure

open import Data.Bool using (true; false)
open import Data.Empty renaming (⊥ to False)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic renaming (⊤ to p⊤; tt to ptt)
open import Relation.Nullary using (¬_)


module Denot.ParamCC (pcs : PreCastStruct) where
  open import ParamCastCalculusABT pcs public  
  {-can use ParamCCSyntaxABT instead if we want just the syntax and don't need typing rules-}

  {- want a denotational semantics from this ABT syntax -}


  open import Fold2 Op sig
  open import NewSemantics Op sig public

  𝕆-ParamCC : DOpSig (𝒫 Val) sig
  𝕆-ParamCC (op-lam x) ⟨ F , ptt ⟩ = Λ F
  𝕆-ParamCC op-app ⟨ D , ⟨ E , ptt ⟩ ⟩ = D ∗ E
  𝕆-ParamCC (op-lit f P) ptt = ℘ P f
  𝕆-ParamCC op-if ⟨ D , ⟨ E₁ , ⟨ E₂ , ptt ⟩ ⟩ ⟩ = If D E₁ E₂
  𝕆-ParamCC op-cons ⟨ D , ⟨ E , ptt ⟩ ⟩ = pair D E
  𝕆-ParamCC op-fst ⟨ D , ptt ⟩ = car D
  𝕆-ParamCC op-snd ⟨ D , ptt ⟩ = cdr D
  𝕆-ParamCC (op-inl x) ⟨ D , ptt ⟩ = inleft D
  𝕆-ParamCC (op-inr x) ⟨ D , ptt ⟩ = inright D
  𝕆-ParamCC (op-case x₁ x₂) ⟨ D , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩ = cond D F₁ F₂
  𝕆-ParamCC (op-cast x) Ds = {!   !}
  𝕆-ParamCC (op-wrap c x) Ds = {!   !}
  𝕆-ParamCC (op-blame x x₁) Ds = {!   !}
  
  
  𝕆-ParamCC-mono : 𝕆-monotone sig 𝕆-ParamCC
  𝕆-ParamCC-mono = {!   !}

  instance
    ParamCC-Semantics : Semantics
    ParamCC-Semantics = record { interp-op = 𝕆-ParamCC ;
                               mono-op = 𝕆-ParamCC-mono ;
                               error = ERR }
  open Semantics {{...}} public

{-
𝑉⊢ : List Type → Var → Type → Type → Set
𝑃⊢ : (op : Op) → Vec Type (length (sig op)) → BTypes Type (sig op) → Type → Set

open import ABTPredicate Op sig 𝑉⊢ 𝑃⊢ public renaming (_⊢_⦂_ to predicate)
  _⊢_⦂_ = predicate

  open import SubstPreserve Op sig Type 𝑉⊢ 𝑃⊢ (λ x → refl) (λ { refl refl → refl })
    (λ x → x) (λ { refl ⊢M → ⊢M }) public
      using (preserve-rename; preserve-subst; preserve-substitution)

  open import GenericPredicate pcs
  open GenericPredicatePatterns 𝑉⊢ 𝑃⊢ public


data _⊢_ : Context → Type → Set where


  pattern ƛ_˙_ A N = (op-lam A) ⦅ cons (bind (ast N)) nil ⦆
  pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
  pattern $_#_ r p = (op-lit r p) ⦅ nil ⦆
  pattern if_then_else_endif L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
  pattern ⟦_,_⟧ M N = op-cons ⦅ cons (ast M) (cons (ast N) nil) ⦆
  pattern fst_ M = op-fst ⦅ cons (ast M) nil ⦆
  pattern snd_ M = op-snd ⦅ cons (ast M) nil ⦆
  pattern inl_other_ M B = (op-inl B) ⦅ cons (ast M) nil ⦆
  pattern inr_other_ M A = (op-inr A) ⦅ cons (ast M) nil ⦆
  pattern case_of_⇒_∣_⇒_ L A M B N =
        (op-case A B) ⦅ cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil)) ⦆
  pattern _⟨_⟩ M c = (op-cast c) ⦅ cons (ast M) nil ⦆
  pattern _⟨_₍_₎⟩ M c i = (op-wrap c i) ⦅ cons (ast M) nil ⦆
  pattern blame A ℓ = (op-blame A ℓ) ⦅ nil ⦆

-}