open import Data.Product using (_×_; ∃; ∃-syntax)

open import Types
open import PreCastStructure
open import CastStructureABT
import ParamCastCalculusABT
import ParamCastAuxABT
import ParamCCPrecisionABT
import ParamCastReductionABT


module CastStructureWithPrecisionABT where

{- TODO : better make this similar to `CastStruct` -}
record CastStructWithPrecision : Set₁ where
  field
    precast : PreCastStruct
  open PreCastStruct precast public
  open ParamCastCalculusABT precast
  open ParamCastAuxABT precast
  open ParamCCPrecisionABT precast
  field
    applyCast : ∀ {A B} → (M : Term) → Value M → (c : Cast (A ⇒ B))
                        → ∀ {a : Active c} → Term

    applyCast-wt : ∀ {Γ A B} {M : Term} {c : Cast (A ⇒ B)}
      → Γ ⊢ M ⦂ A
      → (v : Value M) → (a : Active c)
        --------------------------------
      → Γ ⊢ applyCast M v c {a} ⦂ B

  cs : CastStruct
  cs = record { precast = precast ; applyCast = applyCast ; applyCast-wt = applyCast-wt }

  open ParamCastReductionABT cs
  field
    {- For gradual guarantee.
       Because the implementation of `applyCast` is unique to each cast representation,
       we need to prove this lemma for each specific representation too. -}
    applyCast-catchup : ∀ {Γ Γ′ A A′ B} {V V′} {c : Cast (A ⇒ B)}
      → (a : Active c)
      → (Γ ⊢ V ⦂ A) → (Γ′ ⊢ V′ ⦂ A′)
      → (vV : Value V) → Value V′
      → A ⊑ A′ → B ⊑ A′
      → Γ , Γ′ ⊢ V ⊑ V′
        -----------------------------------------------------------------
      → ∃[ W ] Value W × (applyCast V vV c {a} —↠ W) × Γ , Γ′ ⊢ W ⊑ V′
