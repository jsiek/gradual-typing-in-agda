{-# OPTIONS --allow-unsolved-metas #-}

module LazyCoercionsABT where

  open import Data.Nat
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

  open import PreCastStructure
  open import LazyCoercions using (pcs; id; _??_; _!!; _↣_; _`×_; _`+_; ⊥_⟨_⟩_; coerce; ƛ_) public
  open PreCastStruct pcs public

  import ParamCastCalculusABT
  import ParamCastAuxABT
  open ParamCastCalculusABT pcs renaming (fst_ to first_; snd_ to second_; blame to mkblame) public
  open ParamCastAuxABT pcs public

  applyCast : ∀ {Γ A B} → (M : Term) → Γ ⊢ M ⦂ A → (Value M) → (c : Cast (A ⇒ B))
              → ∀ {a : Active c} → Term
  applyCast M Γ⊢M∶A v id {a} = M
  applyCast M Γ⊢M∶A v (B ?? ℓ) {a} with canonical⋆ Γ⊢M∶A v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , ⟨ q , refl ⟩ ⟩ ⟩ ⟩ ⟩ = M' ⟨ coerce A' B ℓ ⟩
  applyCast {A = A ⇒ B} {B = A' ⇒ B'} M Γ⊢M∶A v (c ↣ d) {a} = 
    ƛ A' ˙ ((rename suc M · ((` zero) ⟨ c ⟩)) ⟨ d ⟩)
  applyCast M Γ⊢M∶A v (c `× d) {a} = 
    ⟦ first M ⟨ c ⟩ , second M ⟨ d ⟩ ⟧
  applyCast {A = A `⊎ B} {B = A' `⊎ B'} M Γ⊢M∶A v (c `+ d) {a} =
    let L = inl ((` zero) ⟨ c ⟩) other B' in
    let R = inr ((` zero) ⟨ d ⟩) other A' in
        case M of A ⇒ L ∣ B ⇒ R
  applyCast M Γ⊢M∶A v (⊥ A ⟨ ℓ ⟩ B) {a} = mkblame B ℓ


  applyCast-wt : ∀ {Γ A B} {V : Term} {c : Cast (A ⇒ B)}
      → (⊢V : Γ ⊢ V ⦂ A)
      → (v : Value V) → (a : Active c)
        --------------------------------
      → Γ ⊢ applyCast V ⊢V v c {a} ⦂ B
  applyCast-wt = {!   !}

  open import CastStructureABT

  cs : CastStruct
  cs = record { precast = pcs 
              ; applyCast = applyCast 
              ; applyCast-wt = applyCast-wt }
  

  open import ParamCastReductionABT cs public

{-
  open import ParamCastDeterministic cs public

  import GTLC2CC
  open GTLC2CC Cast Inert (λ A B ℓ {c} → coerce A B ℓ) public

-}