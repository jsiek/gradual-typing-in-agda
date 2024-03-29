open import Types hiding (_⊔_)
open import Variables
open import PreCastStructure

open import Data.Nat using (ℕ; _≤_; _⊔_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)

module CastStructureOrig where

import ParamCastCalculusOrig
import ParamCastAuxOrig
import EfficientParamCastAux

  {-

  We need a few operations to define reduction in a generic way.
  In particular, we need parameters that say how to reduce casts and
  how to eliminate values wrapped in casts. 
  * The applyCast parameter, applies an Active cast to a value. 
  * The funCast parameter applies a function wrapped in an inert cast
    to an argument.
  * The fstCast and sndCast parameters take the first or second part
    of a pair wrapped in an inert cast.
  * The caseCast performs a case-elimination on a value of sum type (inl or inr)
    that is wrapped in an inert cast.
  * The baseNotInert parameter ensures that every cast to a base type
    is not inert.

  We define a nested module named Reduction with these parameters
  because they all depend on parameters of the outer module, and it
  seems that Agda does not allow parameters to depend on other
  parameters of the same module.

  -}
  
record CastStruct : Set₁ where
  field
    precast : PreCastStruct
  open PreCastStruct precast public
  open ParamCastCalculusOrig Cast
  open ParamCastAuxOrig precast
  field
    applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
                 → ∀ {a : Active c} → Γ ⊢ B

record EfficientCastStruct : Set₁ where
  field
    precast : PreCastStruct
  open PreCastStruct precast public
  open ParamCastCalculusOrig Cast
  open EfficientParamCastAux precast
  field
    applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
                 → ∀ {a : Active c} → Γ ⊢ B
    compose : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C)) → Cast (A ⇒ C)
    height : ∀{A B} → (c : Cast (A ⇒ B)) → ℕ
    compose-height : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
                   → height (compose c d) ≤ (height c) ⊔ (height d)
