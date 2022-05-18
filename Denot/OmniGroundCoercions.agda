{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product using (_×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to p⊤; tt to ptt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong-app)
open import Level using (Lift; lift; lower)

open import Denot.GroundCoercions as λC
open import Denot.GroundCoercionsOmniscient as λC𝒪
open import Denot.CastStructure
open import SetsAsPredicates
open import AbstractBindingTree
open import ParamCCSyntaxABT
open import GroundCoercions
open import Types
open import Labels
open import Denot.Value
open import GSubst using (_•_)

module Denot.OmniGroundCoercions where

  open DenotCastStruct λC.dcs using (⟦_⟧)
  open DenotCastStruct λC𝒪.dcs using () renaming (⟦_⟧ to 𝒪⟦_⟧)

  

  -- for soundness of Omni w.r.t Denot should just need a lemma for coercions
  -- everything else should be monotonicity and managing environment invariants
  -- thus, it would be nice to handle this using a theorem over an arbitrary DenotCastStruct
  


  omni-coerce-⊆ : ∀ {A B} → (c : Cast (A ⇒ B)) 
    → ∀ u v
    → u ↝⟨ c ⟩↝ v → u ↝⟦ c ⟧↝ v
  omni-coerce-⊆₊ : ∀ {A B} → (c : Cast (A ⇒ B))
    → ∀ U V
    → U ↝⟨ c ⟩₊↝ V
    → U ↝⟦ c ⟧₊↝ V
  omni-coerce-⊆ .id u .u (⟦id⟧ wt) = coerce-ok wt
  omni-coerce-⊆ .(inj _) u .u (⟦inj⟧ wt) = coerce-ok tt
  omni-coerce-⊆ {A}{B} (proj .B ℓ) u .u (⟦proj⟧-ok {g = g} u∶B) = 
    coerce-ok (𝐺-sound B g u u∶B)
  omni-coerce-⊆ {A}{B} .(proj _ _) u .(Val.blame _) (⟦proj⟧-fail {g = g} ¬u∶B) = 
    coerce-fail tt (λ z → ¬u∶B (𝐺-adequate B g u z)) (here refl)
  omni-coerce-⊆ {A ⇒ B}{A' ⇒ B'} (cfun c d) (V ↦ w) (V' ↦ w') (⟦cfun⟧ wt V'↝V w↝w')
    = fun-regular (omni-coerce-⊆₊ c V' V V'↝V) 
                (omni-coerce-⊆ d w w' w↝w')
  omni-coerce-⊆ (cseq {A}{B}{C} c d) u w (⟦cseq⟧ {v = v} u↝v v↝w) =
    𝒪seq (omni-coerce-⊆ c u v u↝v) (omni-coerce-⊆ d v w v↝w)
  omni-coerce-⊆₊ c [] [] [] = []
  omni-coerce-⊆₊ c (u ∷ U) (v ∷ V) (u↝v ∷ U↝V) = 
    omni-coerce-⊆ c u v u↝v ∷ omni-coerce-⊆₊ c U V U↝V


  soundDenotOmni : ∀ M ρ ρ' → (∀ i → ρ i ⊆ ρ' i) → ⟦ M ⟧ ρ ⊆ 𝒪⟦ M ⟧ ρ'
  soundDenotOmni (` i) ρ ρ' ρ⊆ = ρ⊆ i
  soundDenotOmni (op-lam A ⦅ cons (bind (ast N)) nil ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ 
    = lower (DenotCastStruct.𝕆-mono λC𝒪.dcs (op-lam A) 
        ⟨ (λ D → ⟦ N ⟧ (D • ρ)) , ptt ⟩ ⟨ ((λ D' → 𝒪⟦ N ⟧ (D' • ρ'))) , ptt ⟩ 
        ⟨ (λ D D' D⊆D' → lift (soundDenotOmni N (D • ρ) (D' • ρ') (λ {zero → D⊆D' ; (suc n) → ρ⊆ n}))) , ptt ⟩) 
            d d∈⟦M⟧
  soundDenotOmni (op-app ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-lit x₁ x₂ ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = d∈⟦M⟧
  soundDenotOmni (op-if ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-cons ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-fst ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-snd ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-inl x₁ ⦅ cons (ast M) nil ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-inr x₁ ⦅ cons  (ast M) nil ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-case x₁ x₂ ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-cast c ⦅ cons (ast M) nil ⦆) ρ ρ' ρ⊆ d ⟨ u , ⟨ u∈⟦M⟧ , u↝⟨c⟩↝d ⟩ ⟩ 
    = ⟨ u , ⟨ IHu , omni-coerce-⊆ c u d u↝⟨c⟩↝d ⟩ ⟩
    where
    IHu : u ∈ 𝒪⟦ M ⟧ ρ'
    IHu = soundDenotOmni M ρ ρ' ρ⊆ u u∈⟦M⟧
  soundDenotOmni (op-wrap c x₁ ⦅ cons (ast M) nil ⦆) = soundDenotOmni M
  soundDenotOmni (op-blame x₁ x₂ ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = d∈⟦M⟧



  adequate : {! ∀ v v' →   !}
  adequate = {!   !}

{-
soundness (for Regular)
If M —→ N, then ⟦ M ⟧ = ⟦ N ⟧

adequacy (for Regular)
if ⟦ M ⟧ non-empty, then M —↠ V.


soundness of regular wrt. omniscient
⟦ M ⟧ ⊆ 𝒪⟦ M ⟧
-}
