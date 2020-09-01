open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties using (_≟_)

-- We're using simple cast - at least for now.
open import SimpleCast using (Cast; pcs; cs)
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast
import ParamCastAux
open ParamCastAux pcs using (Value; Frame; plug)
import ParamCastReduction
open ParamCastReduction cs
open import CastSubtyping using (CastsRespect<:)
open CastsRespect<:

-- Test
-- M : ∅ ⊢ ⋆
-- M = ($_ zero {Prim.P-Base}) ⟨ _⇒⟨_⟩_ (` Nat) (Label.pos zero) ⋆ {unk~R} ⟩


open _—→_
open _—↠_
open Value

-- Values do not reduce.
postulate
  V⌿→ : ∀ {Γ A} {M N : Γ ⊢ A}
    → Value M
    → ¬ (M —→ N)

{-
  If every cast in the term M respects subtyping, then M ⌿↠ blame 𝓁 for any 𝓁 .
-}
soundness-<: : ∀ {Γ A} {M : Γ ⊢ A}
  → CastsRespect<: M
  → ¬ (∃[ 𝓁 ] (M —↠ blame 𝓁))
soundness-<: resp ⟨ 𝓁 , .(plug _ _) —→⟨ ξ rd ⟩ rdd ⟩ = {!!}
soundness-<: resp ⟨ 𝓁 , .(plug (blame _) _) —→⟨ ξ-blame ⟩ rdd ⟩ = {!!}
soundness-<: {M = (ƛ N) · W} (CastsRespect<:-· resp-ƛN resp-W) ⟨ 𝓁 , .((ƛ N) · W) —→⟨ β vW ⟩ N[W]↠blame ⟩ = {!!}
soundness-<: resp ⟨ 𝓁 , .(($ _) · ($ _)) —→⟨ δ ⟩ rdd ⟩ = {!!}
soundness-<: {M = if ($ true) M N} (CastsRespect<:-if _ resp-M _) ⟨ 𝓁 , .(if ($ true) M N) —→⟨ β-if-true ⟩ M↠blame ⟩ =
  soundness-<: resp-M (⟨ 𝓁 , M↠blame ⟩)
soundness-<: {M = if ($ false) M N} (CastsRespect<:-if _ _ resp-N) ⟨ 𝓁 , .(if ($ false) M N) —→⟨ β-if-false ⟩ N↠blame ⟩ =
  soundness-<: resp-N (⟨ 𝓁 , N↠blame ⟩)
soundness-<: {M = fst (cons V W)} (CastsRespect<:-fst (CastsRespect<:-cons resp-V resp-W)) ⟨ 𝓁 , .(fst (cons V W)) —→⟨ β-fst vV vW ⟩ V↠blame ⟩ =
  -- Another way to do this is to prove that V cannot step to blame.
  soundness-<: resp-V (⟨ 𝓁 , V↠blame ⟩)
soundness-<: {M = snd (cons V W)} (CastsRespect<:-snd (CastsRespect<:-cons resp-V resp-W)) ⟨ 𝓁 , .(snd (cons V W)) —→⟨ β-snd vV vW ⟩ W↠blame ⟩ =
  soundness-<: resp-W (⟨ 𝓁 , W↠blame ⟩)
soundness-<: {M = case (inl V) L M} (CastsRespect<:-case (CastsRespect<:-inl resp-V) resp-L _) ⟨ 𝓁 , .(case (inl V) L M) —→⟨ β-caseL vV ⟩ L·V↠blame ⟩ =
  soundness-<: (CastsRespect<:-· resp-L resp-V) (⟨ 𝓁 , L·V↠blame ⟩)
soundness-<: {M = case (inr V) L M} (CastsRespect<:-case (CastsRespect<:-inr resp-V) _ resp-M) ⟨ 𝓁 , .(case (inr V) L M) —→⟨ β-caseR vV ⟩ M·V↠blame ⟩ =
  soundness-<: (CastsRespect<:-· resp-M resp-V) (⟨ 𝓁 , M·V↠blame ⟩)
soundness-<: resp ⟨ 𝓁 , .(_ ⟨ _ ⟩) —→⟨ cast v ⟩ rdd ⟩ = {!!}
soundness-<: resp ⟨ 𝓁 , .(_ ⟨ _ ⟩ · _) —→⟨ fun-cast v x ⟩ rdd ⟩ = {!!}
soundness-<: resp ⟨ 𝓁 , .(fst (_ ⟨ _ ⟩)) —→⟨ fst-cast x ⟩ rdd ⟩ = {!!}
soundness-<: resp ⟨ 𝓁 , .(snd (_ ⟨ _ ⟩)) —→⟨ snd-cast x ⟩ rdd ⟩ = {!!}
soundness-<: resp ⟨ 𝓁 , .(case (_ ⟨ _ ⟩) _ _) —→⟨ case-cast x ⟩ rdd ⟩ = {!!}
