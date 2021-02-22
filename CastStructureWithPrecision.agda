open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Types
open import Variables
open import PreCastStructureWithPrecision
open import CastStructure

import ParamCastCalculus
import ParamCastAux
import ParamCastSubtyping
import ParamCCPrecision


module CastStructureWithPrecision where

import ParamCastReduction

record CastStructWithPrecision : Set₁ where
  field
    pcsp : PreCastStructWithPrecision
  open PreCastStructWithPrecision pcsp public
  open ParamCastCalculus Cast Inert
  open ParamCastAux precast
  open ParamCastSubtyping pcss
  open ParamCCPrecision pcsp
  field
    applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
                 → ∀ {a : Active c} → Γ ⊢ B
    {- The field is for blame-subtyping. -}
    applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
      → (a : Active c)
      → Safe c ℓ
      → CastsAllSafe V ℓ
        --------------------------------------
      → CastsAllSafe (applyCast V vV c {a}) ℓ
  cs : CastStruct
  cs = record {
         applyCast = applyCast;
         applyCast-pres-allsafe = applyCast-pres-allsafe
       }
  open ParamCastReduction cs
  field
    {- The field is for gradual guarantees. -}
    applyCast-catchup : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
      → (a : Active c)
      → (vV : Value V) → Value V′
      → A ⊑ A′ → B ⊑ A′
      → Γ , Γ′ ⊢ V ⊑ᶜ V′
        -----------------------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {a} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
