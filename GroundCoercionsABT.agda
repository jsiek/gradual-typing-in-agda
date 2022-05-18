{-# OPTIONS --allow-unsolved-metas #-}

module GroundCoercionsABT where

  open import Data.Nat
  open import Types
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
      renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
      using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

  open import PreCastStructure
  open import GroundCoercions 
    using (pcs; id; inj; proj; cfun; cpair; csum; cseq; C-pair; C-sum) public
  open PreCastStruct pcs public

  import ParamCastCalculusABT
  import ParamCastAuxABT
  open ParamCastCalculusABT pcs public
  open ParamCastAuxABT pcs public



  applyCast : ∀ {Γ A B} → (M : Term) → Γ ⊢ M ⦂ A → (Value M) → (c : Cast (A ⇒ B))
              → ∀ {a : Active c} → Term
  applyCast {Γ} {A} {.A} M Γ⊢M∶A vM id {a} = M
  applyCast {Γ} {.⋆} {B} M Γ⊢M∶A vM (proj .B ℓ {gb}) {a} with canonical⋆ Γ⊢M∶A vM
  ... | ⟨ G , ⟨ V , ⟨ .(inj G) , ⟨ GroundCoercions.I-inj {G}{ga} , ⟨ q , refl ⟩ ⟩ ⟩ ⟩ ⟩
     with gnd-eq? G B {ga} {gb} 
  ... | no neq = blame B ℓ
  ... | yes refl = V
  applyCast {Γ} {.(_ `× _)} {.(_ `× _)} M Γ⊢M∶A vM (cpair c d) {a} = eta× M (cpair c d) C-pair
  applyCast {Γ} {.(_ `⊎ _)} {.(_ `⊎ _)} M Γ⊢M∶A vM (csum c d) {a} = eta⊎ M (csum c d) C-sum
  applyCast {Γ} {A} {B} M Γ⊢M∶A vM (cseq c d) {a} = (M ⟨ c ⟩) ⟨ d ⟩
  
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
  
{-
  open import ParamCastReduction cs public
  open import ParamCastDeterministic cs public

  import GTLC2CC
  open GTLC2CC Cast Inert (λ A B ℓ {c} → coerce A B ℓ) public
-}