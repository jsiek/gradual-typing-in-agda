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
      {- The usual `CastStruct` fields. -}
      applyCast : ∀ {Γ A B} → (V : Term) → Γ ⊢ V ⦂ A → Value V → (c : Cast (A ⇒ B))
                            → {a : Active c} → Term
      applyCast-wt : ∀ {Γ A B} {V : Term} {c : Cast (A ⇒ B)}
        → (⊢V : Γ ⊢ V ⦂ A)
        → (v : Value V) → (a : Active c)
          --------------------------------
        → Γ ⊢ applyCast V ⊢V v c {a} ⦂ B
      {- This field is for blame-subtyping. -}
      applyCast-pres-SafeFor : ∀ {Γ A B} {V : Term} {v : Value V} {c : Cast (A ⇒ B)} {ℓ}
        → (⊢V : Γ ⊢ V ⦂ A)
        → (a : Active c)
        → CastBlameSafe c ℓ
        → V SafeFor ℓ
          --------------------------------------
        → (applyCast V ⊢V v c {a}) SafeFor ℓ

    cs : CastStruct
    cs = record {
           precast = precast;
           applyCast-wt = applyCast-wt;
           applyCast = applyCast
         }
