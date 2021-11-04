open import Types
open import Labels
open import Variables
open import PreCastStructureWithBlameSafety
open import CastStructureABT


module CastStructureWithBlameSafetyABT where

  import ParamCastCalculusABT
  import ParamCastAuxABT
  import ParamCastSubtypingABT
  -- import EfficientParamCastAux

  record CastStructWithBlameSafety : Set₁ where
    field
      pcss : PreCastStructWithBlameSafety
    open PreCastStructWithBlameSafety pcss public
    open ParamCastCalculusABT precast
    open ParamCastAuxABT precast
    open ParamCastSubtypingABT pcss
    field
      {- These are usual `CastStruct` fields. -}
      applyCast : ∀ {A B} → (M : Term) → Value M → (c : Cast (A ⇒ B))
                          → ∀ {a : Active c} → Term
      applyCast-wt : ∀ {Γ A B} {M : Term} {c : Cast (A ⇒ B)}
        → Γ ⊢ M ⦂ A
        → (v : Value M) → (a : Active c)
          --------------------------------
        → Γ ⊢ applyCast M v c {a} ⦂ B
      {- This field is for blame-subtyping. -}
      applyCast-pres-SafeFor : ∀ {A B} {V : Term} {v : Value V} {c : Cast (A ⇒ B)} {ℓ}
        → (a : Active c)
        → CastBlameSafe c ℓ
        → V SafeFor ℓ
          --------------------------------------
        → (applyCast V v c {a}) SafeFor ℓ

    cs : CastStruct
    cs = record {
           precast = precast;
           applyCast-wt = applyCast-wt;
           applyCast = applyCast
         }
