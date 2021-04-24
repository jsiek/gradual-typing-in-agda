open import Types
open import Variables
open import PreCastStructureWithBlameSafety
open import CastStructure

open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)


module CastStructureWithBlameSafety where

import ParamCastCalculus
import ParamCastAux
import ParamCastSubtyping
import EfficientParamCastAux

record CastStructWithBlameSafety : Set₁ where
  field
    pcss : PreCastStructWithBlameSafety
  open PreCastStructWithBlameSafety pcss public
  open ParamCastCalculus Cast Inert
  open ParamCastAux precast
  open ParamCastSubtyping pcss
  field
    applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
                 → ∀ {a : Active c} → Γ ⊢ B
    {- The field is for blame-subtyping. -}
    applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
      → (a : Active c)
      → CastBlameSafe c ℓ
      → CastsAllSafe V ℓ
        --------------------------------------
      → CastsAllSafe (applyCast V vV c {a}) ℓ

  cs : CastStruct
  cs = record { precast = precast; applyCast = applyCast }
