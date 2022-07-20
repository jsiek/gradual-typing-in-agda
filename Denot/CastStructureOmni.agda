{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; _≤_; _⊔_; _+_; _*_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic renaming (⊤ to p⊤; tt to ptt)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)

open import Types
open import Labels
open import PreCastStructure
open import CastStructureABT
open import Pow2
open import Denot.Value
open import Denot.OpOmni
open import Primitives hiding (_⇒_)
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import SetsAsPredicates
open import NewDenotProperties


module Denot.CastStructureOmni where

import ParamCastCalculusABT
import ParamCastAuxABT
-- import EfficientParamCastAux


record DenotCastStruct : Set₁ where
  field
    cast : CastStruct
  open CastStruct cast
  open ParamCastCalculusABT precast
  open ParamCastAuxABT precast
  field
    𝒞 : ∀ {A B : Type} → Cast (A ⇒ B) → 𝒫 Val → 𝒫 Val
{- add monotone field for 𝒞  -}
  𝕆 : DOpSig (𝒫 Val) sig
  𝕆 (op-lam A) ⟨ F , ptt ⟩ = Λ A F
  𝕆 op-app ⟨ D , ⟨ E , ptt ⟩ ⟩ = D ∗ E
  𝕆 (op-lit f P) ptt = ℘ P f
  𝕆 op-if ⟨ D , ⟨ E₁ , ⟨ E₂ , ptt ⟩ ⟩ ⟩ = If D E₁ E₂
  𝕆 op-cons ⟨ D , ⟨ E , ptt ⟩ ⟩ = pair D E
  𝕆 op-fst ⟨ D , ptt ⟩ = car D
  𝕆 op-snd ⟨ D , ptt ⟩ = cdr D
  𝕆 (op-inl x) ⟨ D , ptt ⟩ = inleft D
  𝕆 (op-inr x) ⟨ D , ptt ⟩ = inright D
  𝕆 (op-case x₁ x₂) ⟨ D , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩ = cond D F₁ F₂
  𝕆 (op-cast c) ⟨ D , ptt ⟩ = 𝒞 c D
  𝕆 (op-wrap c x) ⟨ D , ptt ⟩ = 𝒞 c D
  𝕆 (op-blame x ℓ) Ds = ℬ ℓ
  {- add proof of monotonicity -}
  𝕆-mono : 𝕆-monotone sig 𝕆
  𝕆-mono = {!   !}
  open import Fold2 Op sig
  open import NewSemantics Op sig public
  instance
    semantics : Semantics
    semantics = record { interp-op = 𝕆 ;
                         mono-op = 𝕆-mono ;
                         error = Val.blame (neg zero) }
  open Semantics semantics public

  {- possible other fields include: 
      + denotApplyCast-wt
      + sound w.r.t. applyCast
      + adequate w.r.t. applyCast
  -}



{-
 -- cast application is well-typed
 applyCast-wt : ∀ {Γ A B} {V : Term} {c : Cast (A ⇒ B)}
   → (⊢V : Γ ⊢ V ⦂ A)
   → (v : Value V) → (a : Active c)
    --------------------------------
   → Γ ⊢ applyCast V ⊢V v c {a} ⦂ B
 -}
    


