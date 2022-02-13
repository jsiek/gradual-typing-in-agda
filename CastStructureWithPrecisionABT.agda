open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃; ∃-syntax)

open import Types
open import PreCastStructure
open import CastStructureABT
import ParamCastCalculusABT
import ParamCastAuxABT
import ParamCCPrecisionABT
import ParamCastReductionABT


module CastStructureWithPrecisionABT where

record CastStructWithPrecision : Set₁ where
  field
    precast : PreCastStruct
  open PreCastStruct precast public
  open ParamCastCalculusABT precast
  open ParamCastAuxABT precast
  open ParamCCPrecisionABT precast
  field
    applyCast : ∀ {Γ A B} → (V : Term) → Γ ⊢ V ⦂ A → Value V → (c : Cast (A ⇒ B))
                          → {a : Active c} → Term

    applyCast-wt : ∀ {Γ A B} {V : Term} {c : Cast (A ⇒ B)}
      → (⊢V : Γ ⊢ V ⦂ A)
      → (v : Value V) → (a : Active c)
        --------------------------------
      → Γ ⊢ applyCast V ⊢V v c {a} ⦂ B


  cs : CastStruct
  cs = record { precast = precast ; applyCast = applyCast ; applyCast-wt = applyCast-wt }

  open ParamCastReductionABT cs
  field
    {- For gradual guarantee.
       Because the implementation of `applyCast` is unique to each cast representation,
       we need to prove this lemma for each specific representation too. -}
    applyCast-catchup : ∀ {A A′ B} {V V′} {c : Cast (A ⇒ B)}
      → (a : Active c)
      → (⊢V : [] ⊢ V ⦂ A) → [] ⊢ V′ ⦂ A′
      → (v : Value V) → Value V′
      → A ⊑ A′ → B ⊑ A′
      → [] , [] ⊢ V ⊑ V′
        -----------------------------------------------------------------
      → ∃[ W ] Value W × (applyCast V ⊢V v c {a} —↠ W) × [] , [] ⊢ W ⊑ V′

    sim-cast : ∀ {A A′ B B′} {V V′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
      → (a′ : Active c′)
      → [] ⊢ V ⦂ A → (⊢V′ : [] ⊢ V′ ⦂ A′)
      → Value V → (v′ : Value V′)
      → A ⊑ A′ → B ⊑ B′
      → [] , [] ⊢ V ⊑ V′
        ------------------------------------------------------------
      → ∃[ N ] (V ⟨ c ⟩ —↠ N) × [] , [] ⊢ N ⊑ applyCast V′ ⊢V′ v′ c′ {a′}

    cast-castr : ∀ {A A′ B′} {V V′} {c′ : Cast (A′ ⇒ B′)}
      → (a′ : Active c′)
      → [] ⊢ V ⦂ A → (⊢V′ : [] ⊢ V′ ⦂ A′)
      → Value V → (v′ : Value V′)
      → A ⊑ A′ → A ⊑ B′
      → [] , [] ⊢ V ⊑ V′
        --------------------------------------
      → [] , [] ⊢ V ⊑ applyCast V′ ⊢V′ v′ c′ {a′}
