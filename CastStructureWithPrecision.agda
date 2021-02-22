open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Types
open import Variables
open import PreCastStructure
open import CastStructure

import ParamCastCalculus
import ParamCastAux
import ParamCCPrecision

module CastStructureWithPrecision where

import ParamCastReduction

record CastStructWithPrecision : Set₁ where
  field
    cs : CastStruct
  open CastStruct cs
  open ParamCastCalculus Cast Inert
  open ParamCastAux precast
  open ParamCastReduction cs
  open ParamCCPrecision pcsp
  field
    applyCast-catchup : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
      → (a : Active c)
      → (vV : Value V) → Value V′
      → A ⊑ A′ → B ⊑ A′
      → Γ , Γ′ ⊢ V ⊑ᶜ V′
        -----------------------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {a} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
