open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe


open import Types
-- open import Variables
open import Labels
open import PreCastStructureWithBlameSafety



-- Module definition - parameterized by `PreCastStruct` .
module ParamCastSubtypingABT (pcs : PreCastStructWithBlameSafety) where

open PreCastStructWithBlameSafety pcs

open import ParamCastCalculusABT precast



-- Data type `CastsAllSafe` says all casts in M with blame label ℓ are safe casts.
data CastsAllSafe : ∀ (M : Term) → (ℓ : Label) → Set where

  allsafe-cast : ∀ {S T} {M : Term} {c : Cast (S ⇒ T)} {ℓ}
    → CastBlameSafe c ℓ
    → CastsAllSafe M ℓ
      -------------------------------------
    → CastsAllSafe (M ⟨ c ⟩) ℓ

  allsafe-wrap : ∀ {S T} {M : Term} {c : Cast (S ⇒ T)} {i : Inert c} {ℓ}
    → CastBlameSafe c ℓ
    → CastsAllSafe M ℓ
      -------------------------------------
    → CastsAllSafe (M ⟨ c ₍ i ₎⟩) ℓ

  allsafe-var : ∀ {x} {ℓ}
      ------------------------------
    → CastsAllSafe (` x) ℓ

  allsafe-ƛ : ∀ {A} {N : Term} {ℓ}
    → CastsAllSafe N ℓ
      -----------------------
    → CastsAllSafe (ƛ A ˙ N) ℓ

  allsafe-· : ∀ {L M : Term} {ℓ}
    → CastsAllSafe L ℓ
    → CastsAllSafe M ℓ
      -------------------------
    → CastsAllSafe (L · M) ℓ

  allsafe-prim : ∀ {A} {r : rep A} {p : Prim A} {ℓ}
      --------------------------------------------
    → CastsAllSafe ($ r # p) ℓ

  allsafe-if : ∀ {L M N : Term} {ℓ}
    → CastsAllSafe L ℓ
    → CastsAllSafe M ℓ
    → CastsAllSafe N ℓ
      -----------------------------
    → CastsAllSafe (if L then M else N endif) ℓ

  allsafe-cons : ∀ {M N : Term} {ℓ}
    → CastsAllSafe M ℓ
    → CastsAllSafe N ℓ
      ----------------------------
    → CastsAllSafe ⟦ M , N ⟧ ℓ

  allsafe-fst : ∀ {M : Term} {ℓ}
    → CastsAllSafe M ℓ
      -------------------------
    → CastsAllSafe (fst M) ℓ

  allsafe-snd : ∀ {M : Term} {ℓ}
    → CastsAllSafe M ℓ
      -------------------------
    → CastsAllSafe (snd M) ℓ

  allsafe-inl : ∀ {B} {M : Term} {ℓ}
    → CastsAllSafe M ℓ
      ---------------------------------
    → CastsAllSafe (inl M other B) ℓ

  allsafe-inr : ∀ {A} {N : Term} {ℓ}
    → CastsAllSafe N ℓ
      ----------------------------------
    → CastsAllSafe (inr N other A) ℓ

  allsafe-case : ∀ {A B} {L M N} {ℓ}
    → CastsAllSafe L ℓ
    → CastsAllSafe M ℓ
    → CastsAllSafe N ℓ
      ------------------------------
    → CastsAllSafe (case L of A ⇒ M ∣ B ⇒ N) ℓ

  -- {- NOTE:
  --   A well-typed surface language term can never be compiled into a blame in the cast calculus (CC).
  --   However we still have a case for `blame ℓ` here since it has such a case in CC.
  -- -}
  allsafe-blame-diff-ℓ : ∀ {ℓ ℓ′}
    → ℓ ≢̂ ℓ′
      ------------------------------------
    → CastsAllSafe (blame ℓ′) ℓ
