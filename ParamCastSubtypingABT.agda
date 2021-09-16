open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.List
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Unit using (⊤) renaming (tt to unit)

open import Types
open import Labels
open import PreCastStructureWithBlameSafety

open import Syntax


-- Module definition - parameterized by `PreCastStruct` .
module ParamCastSubtypingABT (pcss : PreCastStructWithBlameSafety) where

  open PreCastStructWithBlameSafety pcss

  open import ParamCastCalculusABT precast

  private
    𝑉ₛ : List Label → Var → Label → Label → Set
    𝑃ₛ : (op : Op) → Vec Label (length (sig op)) → BTypes Label (sig op) → Label → Set

  -- data CastsAllSafe : ∀ (M : Term) → (ℓ : Label) → Set where

  --   allsafe-var : ∀ {x} {ℓ}
  --       ------------------------------
  --     → CastsAllSafe (` x) ℓ
  𝑉ₛ _ _ ℓ′ ℓ = ℓ ≡ ℓ′

  --   allsafe-cast : ∀ {S T} {M : Term} {c : Cast (S ⇒ T)} {ℓ}
  --     → CastBlameSafe c ℓ
  --     → CastsAllSafe M ℓ
  --       -------------------------------------
  --     → CastsAllSafe (M ⟨ c ⟩) ℓ
  𝑃ₛ (op-cast c) (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = CastBlameSafe c ℓ × ℓ ≡ ℓₘ

  --   allsafe-wrap : ∀ {S T} {M : Term} {c : Cast (S ⇒ T)} {i : Inert c} {ℓ}
  --     → CastBlameSafe c ℓ
  --     → CastsAllSafe M ℓ
  --       -------------------------------------
  --     → CastsAllSafe (M ⟨ c ₍ i ₎⟩) ℓ
  𝑃ₛ (op-wrap c i) (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = CastBlameSafe c ℓ × ℓ ≡ ℓₘ

  --   allsafe-ƛ : ∀ {A} {N : Term} {ℓ}
  --     → CastsAllSafe N ℓ
  --       -----------------------
  --     → CastsAllSafe (ƛ A ˙ N) ℓ
  𝑃ₛ (op-lam _) (ℓₙ ∷ᵥ []ᵥ) ⟨ ⟨ ℓ′ , tt ⟩ , tt ⟩ ℓ = ℓ ≡ ℓ′ × ℓ ≡ ℓₙ

  --   allsafe-· : ∀ {L M : Term} {ℓ}
  --     → CastsAllSafe L ℓ
  --     → CastsAllSafe M ℓ
  --       -------------------------
  --     → CastsAllSafe (L · M) ℓ
  𝑃ₛ op-app (ℓₗ ∷ᵥ ℓₘ ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , tt ⟩ ⟩ ℓ = ℓ ≡ ℓₗ × ℓ ≡ ℓₘ

  --   allsafe-prim : ∀ {A} {r : rep A} {p : Prim A} {ℓ}
  --       --------------------------------------------
  --     → CastsAllSafe ($ r # p) ℓ
  𝑃ₛ (op-lit r p) []ᵥ tt ℓ = ⊤

  --   allsafe-if : ∀ {L M N : Term} {ℓ}
  --     → CastsAllSafe L ℓ
  --     → CastsAllSafe M ℓ
  --     → CastsAllSafe N ℓ
  --       -----------------------------
  --     → CastsAllSafe (if L then M else N endif) ℓ
  𝑃ₛ op-if (ℓₗ ∷ᵥ ℓₘ ∷ᵥ ℓₙ ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , ⟨ tt , tt ⟩ ⟩ ⟩ ℓ = ℓ ≡ ℓₗ × ℓ ≡ ℓₘ × ℓ ≡ ℓₙ

  --   allsafe-cons : ∀ {M N : Term} {ℓ}
  --     → CastsAllSafe M ℓ
  --     → CastsAllSafe N ℓ
  --       ----------------------------
  --     → CastsAllSafe ⟦ M , N ⟧ ℓ
  𝑃ₛ op-cons (ℓₘ ∷ᵥ ℓₙ ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , tt ⟩ ⟩ ℓ = ℓ ≡ ℓₘ × ℓ ≡ ℓₙ

  --   allsafe-fst : ∀ {M : Term} {ℓ}
  --     → CastsAllSafe M ℓ
  --       -------------------------
  --     → CastsAllSafe (fst M) ℓ
  𝑃ₛ op-fst (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = ℓ ≡ ℓₘ

  --   allsafe-snd : ∀ {M : Term} {ℓ}
  --     → CastsAllSafe M ℓ
  --       -------------------------
  --     → CastsAllSafe (snd M) ℓ
  𝑃ₛ op-snd (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = ℓ ≡ ℓₘ

  --   allsafe-inl : ∀ {B} {M : Term} {ℓ}
  --     → CastsAllSafe M ℓ
  --       ---------------------------------
  --     → CastsAllSafe (inl M other B) ℓ
  𝑃ₛ (op-inl _) (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = ℓ ≡ ℓₘ

  --   allsafe-inr : ∀ {A} {N : Term} {ℓ}
  --     → CastsAllSafe N ℓ
  --       ----------------------------------
  --     → CastsAllSafe (inr N other A) ℓ
  𝑃ₛ (op-inr _) (ℓₙ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = ℓ ≡ ℓₙ

  --   allsafe-case : ∀ {A B} {L M N} {ℓ}
  --     → CastsAllSafe L ℓ
  --     → CastsAllSafe M ℓ
  --     → CastsAllSafe N ℓ
  --       ------------------------------
  --     → CastsAllSafe (case L of A ⇒ M ∣ B ⇒ N) ℓ
  𝑃ₛ (op-case _ _) (ℓₗ ∷ᵥ ℓₘ ∷ᵥ ℓₙ ∷ᵥ []ᵥ) ⟨ tt , ⟨ ⟨ _ , tt ⟩ , ⟨ ⟨ _ , tt ⟩ , tt ⟩ ⟩ ⟩ ℓ =
    ℓ ≡ ℓₗ × ℓ ≡ ℓₘ × ℓ ≡ ℓₙ

  {-
    NOTE:
    A well-typed surface language term can never be compiled into a blame in the cast calculus (CC).
    However we still have a case for `blame ℓ` here since it has such a case in CC.
  -}
  --   allsafe-blame-diff-ℓ : ∀ {ℓ ℓ′}
  --     → ℓ ≢̂ ℓ′
  --       ------------------------------------
  --     → CastsAllSafe (blame ℓ′) ℓ
  𝑃ₛ (op-blame ℓ′) []ᵥ tt ℓ = ℓ ≢̂ ℓ′

  pattern 𝐶ₛ-cast = ⟨ _ , refl ⟩
  pattern 𝐶ₛ-wrap = ⟨ _ , refl ⟩
  pattern 𝐶ₛ-ƛ = ⟨ refl , refl ⟩
  pattern 𝐶ₛ-$ = unit
  pattern 𝐶ₛ-· = ⟨ refl , refl ⟩
  pattern 𝐶ₛ-if = ⟨ refl , ⟨ refl , refl ⟩ ⟩
  pattern 𝐶ₛ-cons = ⟨ refl , refl ⟩
  pattern 𝐶ₛ-fst = refl
  pattern 𝐶ₛ-snd = refl
  pattern 𝐶ₛ-inl = refl
  pattern 𝐶ₛ-inr = refl
  pattern 𝐶ₛ-case = ⟨ refl , ⟨ refl , refl ⟩ ⟩

  open import ABTPredicate Op sig 𝑉ₛ 𝑃ₛ public
    renaming (_⊢_⦂_ to predicate-allsafe)

  CastsAllSafe : Term → Label → Set  -- CastsAllSafe M ℓ
  CastsAllSafe = predicate-allsafe []

  open import SubstPreserve Op sig Label 𝑉ₛ 𝑃ₛ (λ _ → refl) (λ { refl refl → refl })
    (λ x → x) (λ { refl pM → pM }) public
      renaming (preserve-rename to rename-pres-allsafe;
                                preserve-subst to subst-pres-allsafe;
                                preserve-substitution to substitution-allsafe)

  open import GenericPredicate precast
  open GenericPredicatePatterns 𝑉ₛ 𝑃ₛ public
