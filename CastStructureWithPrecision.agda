open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong)
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
    {- This field is for gradual guarantees.
       Because the implementation of `applyCast` is unique to each cast representation,
       we need to prove this lemma for each specific representation as well. -}
    applyCast-catchup : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
      → (a : Active c)
      → (vV : Value V) → Value V′
      → A ⊑ A′ → B ⊑ A′
      → Γ , Γ′ ⊢ V ⊑ᶜ V′
        -----------------------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {a} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))


    sim-cast : ∀ {A A′ B B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
      → Value V → (v′ : Value V′)
      → (a′ : Active c′)
      → A ⊑ A′ → B ⊑ B′
      → ∅ , ∅ ⊢ V ⊑ᶜ V′
        ------------------------------------------------------------
      → ∃[ N ] ((V ⟨ c ⟩ —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ applyCast V′ v′ c′ {a′}))
    sim-wrap : ∀ {A A′ B B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
      → Value V → (v′ : Value V′)
      → (i′ : Inert c′)
      → A ⊑ A′ → B ⊑ B′
      → ∅ , ∅ ⊢ V ⊑ᶜ V′
        -----------------------------------------------------
      → ∃[ N ] ((V ⟨ c ⟩ —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ V′ ⟪ i′ ⟫))
    castr-cast : ∀ {A A′ B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c′ : Cast (A′ ⇒ B′)}
      → Value V → (v′ : Value V′)
      → (a′ : Active c′)
      → A ⊑ A′ → A ⊑ B′
      → ∅ , ∅ ⊢ V ⊑ᶜ V′
        ------------------------------------------------------------
      → ∅ , ∅ ⊢ V ⊑ᶜ applyCast V′ v′ c′ {a′}
    castr-wrap : ∀ {A A′ B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c′ : Cast (A′ ⇒ B′)}
      → Value V → (v′ : Value V′)
      → (i′ : Inert c′)
      → A ⊑ A′ → A ⊑ B′
      → ∅ , ∅ ⊢ V ⊑ᶜ V′
        -----------------------------------------------------
      → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
