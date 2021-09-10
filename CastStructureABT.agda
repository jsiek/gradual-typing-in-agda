open import Types hiding (_⊔_)
open import Variables
open import PreCastStructure
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _≤_; _⊔_; _+_; _*_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)
open import Pow2


module CastStructureABT where

import ParamCastCalculusABT
import ParamCastAuxABT
-- import EfficientParamCastAux


record CastStruct : Set₁ where
  field
    precast : PreCastStruct
  open PreCastStruct precast public
  open ParamCastCalculusABT precast
  open ParamCastAuxABT precast
  field
    applyCast : ∀ {A B} → (M : Term) → Value M → (c : Cast (A ⇒ B))
                    → ∀ {a : Active c} → Term

    -- cast application is well-typed
    applyCast-wt : ∀ {Γ A B} {M : Term} {c : Cast (A ⇒ B)}
      → Γ ⊢ M ⦂ A
      → (v : Value M) → (a : Active c)
        --------------------------------
      → Γ ⊢ applyCast M v c {a} ⦂ B
