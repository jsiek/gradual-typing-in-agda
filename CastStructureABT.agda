open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _≤_; _⊔_; _+_; _*_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)

open import Types hiding (_⊔_)
open import PreCastStructure
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
    applyCast : ∀ {Γ A B} → (V : Term) → Γ ⊢ V ⦂ A → Value V → (c : Cast (A ⇒ B))
                          → {a : Active c} → Term

    -- cast application is well-typed
    applyCast-wt : ∀ {Γ A B} {V : Term} {c : Cast (A ⇒ B)}
      → (⊢V : Γ ⊢ V ⦂ A)
      → (v : Value V) → (a : Active c)
        --------------------------------
      → Γ ⊢ applyCast V ⊢V v c {a} ⦂ B
