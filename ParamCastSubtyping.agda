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
open import Variables
open import Labels
open import PreCastStructure



-- Module definition - parameterized by `PreCastStruct` .
module ParamCastSubtyping (pcs : PreCastStruct) where

open PreCastStruct pcs

import ParamCastCalculus
open ParamCastCalculus Cast



-- Data type `CastsAllSafe` says all casts in M with blame label ℓ are safe casts.
data CastsAllSafe : ∀ {Γ A} → (M : Γ ⊢ A) → (ℓ : Label) → Set where

  -- {- NOTE:
  --   If the cast has the same blame label as ℓ , which is what the data type is quantified over,
  --   we require that it satisfies safety (the source & target types respect subtyping <: ).
  -- -}
  allsafe-cast-same-ℓ : ∀ {Γ S T} {M : Γ ⊢ S} {c : Cast (S ⇒ T)} {ℓ}
    → Safe c
    → labC c ≡ just ℓ
    → CastsAllSafe M ℓ
      -------------------------------------
    → CastsAllSafe (M ⟨ c ⟩) ℓ

  -- {- NOTE:
  --   If the blame label ℓ′ on the cast is different from what the data type is quantified over,
  --   this is fine and we don't impose any restriction on this cast.
  -- -}
  allsafe-cast-diff-ℓ : ∀ {Γ S T} {M : Γ ⊢ S} {c : Cast (S ⇒ T)} {ℓ}
    → labC c ≢ just ℓ
    → CastsAllSafe M ℓ
      ----------------------------------------------
    → CastsAllSafe (M ⟨ c ⟩) ℓ

  allsafe-var : ∀ {Γ A} {x : Γ ∋ A} {ℓ}
      ------------------------------
    → CastsAllSafe (` x) ℓ

  allsafe-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {ℓ}
    → CastsAllSafe N ℓ
      -----------------------
    → CastsAllSafe (ƛ N) ℓ

  allsafe-· : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} {ℓ}
    → CastsAllSafe L ℓ
    → CastsAllSafe M ℓ
      -------------------------
    → CastsAllSafe (L · M) ℓ

  allsafe-prim : ∀ {Γ A} {p : rep A} {f : Prim A} {ℓ}
      --------------------------------------------
    → CastsAllSafe ($_ {Γ} p {f}) ℓ

  allsafe-if : ∀ {Γ A} {L : Γ ⊢ ` 𝔹} {M : Γ ⊢ A} {N : Γ ⊢ A} {ℓ}
    → CastsAllSafe L ℓ
    → CastsAllSafe M ℓ
    → CastsAllSafe N ℓ
      -----------------------------
    → CastsAllSafe (if L M N) ℓ

  allsafe-cons : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ ⊢ B} {ℓ}
    → CastsAllSafe M ℓ
    → CastsAllSafe N ℓ
      ----------------------------
    → CastsAllSafe (cons M N) ℓ

  allsafe-fst : ∀ {Γ A B} {M : Γ ⊢ A `× B} {ℓ}
    → CastsAllSafe M ℓ
      -------------------------
    → CastsAllSafe (fst M) ℓ

  allsafe-snd : ∀ {Γ A B} {M : Γ ⊢ A `× B} {ℓ}
    → CastsAllSafe M ℓ
      -------------------------
    → CastsAllSafe (snd M) ℓ

  allsafe-inl : ∀ {Γ A B} {M : Γ ⊢ A} {ℓ}
    → CastsAllSafe M ℓ
      ---------------------------------
    → CastsAllSafe (inl {B = B} M) ℓ

  allsafe-inr : ∀ {Γ A B} {N : Γ ⊢ B} {ℓ}
    → CastsAllSafe N ℓ
      ----------------------------------
    → CastsAllSafe (inr {A = A} N) ℓ

  allsafe-case : ∀ {Γ A B C} {L : Γ ⊢ A `⊎ B} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C} {ℓ}
    → CastsAllSafe L ℓ
    → CastsAllSafe M ℓ
    → CastsAllSafe N ℓ
      ------------------------------
    → CastsAllSafe (case L M N) ℓ

  {- NOTE:
    A well-typed surface language term can never be compiled into a blame in the cast calculus (CC).
    However we still have a case for `blame ℓ` here since it has such a case in CC.
  -}
  allsafe-blame-diff-ℓ : ∀ {Γ A} {ℓ ℓ′}
    → ℓ ≢ ℓ′
      ------------------------------------
    → CastsAllSafe (blame {Γ} {A} ℓ′) ℓ




{- NOTE:
  Renaming (rebasing a type derivation) preserves `CR<:` . The statement of this lemma is similar to the
  one about well-typedness in `Properties` chapter, PLFA.
-}
rename-pres-allsafe : ∀ {Γ Δ A} {M : Γ ⊢ A} {ℓ}
  → (ρ : Rename Γ Δ)
    ----------------------------------------------------
  → CastsAllSafe M ℓ → CastsAllSafe (rename ρ M) ℓ
rename-pres-allsafe ρ (allsafe-cast-same-ℓ safe eq allsafe) = allsafe-cast-same-ℓ safe eq (rename-pres-allsafe ρ allsafe)
rename-pres-allsafe ρ (allsafe-cast-diff-ℓ neq allsafe) = allsafe-cast-diff-ℓ neq (rename-pres-allsafe ρ allsafe)
rename-pres-allsafe ρ allsafe-var = allsafe-var
rename-pres-allsafe ρ (allsafe-ƛ allsafe) = allsafe-ƛ (rename-pres-allsafe (λ {X} → ext ρ) allsafe)
rename-pres-allsafe ρ (allsafe-· allsafe-L allsafe-M) =
  allsafe-· (rename-pres-allsafe ρ allsafe-L) (rename-pres-allsafe ρ allsafe-M)
rename-pres-allsafe ρ allsafe-prim = allsafe-prim
rename-pres-allsafe ρ (allsafe-if allsafe-L allsafe-M allsafe-N) =
  allsafe-if (rename-pres-allsafe ρ allsafe-L) (rename-pres-allsafe ρ allsafe-M)
             (rename-pres-allsafe ρ allsafe-N)
rename-pres-allsafe ρ (allsafe-cons allsafe-M allsafe-N) =
  allsafe-cons (rename-pres-allsafe ρ allsafe-M) (rename-pres-allsafe ρ allsafe-N)
rename-pres-allsafe ρ (allsafe-fst allsafe) = allsafe-fst (rename-pres-allsafe ρ allsafe)
rename-pres-allsafe ρ (allsafe-snd allsafe) = allsafe-snd (rename-pres-allsafe ρ allsafe)
rename-pres-allsafe ρ (allsafe-inl allsafe) = allsafe-inl (rename-pres-allsafe ρ allsafe)
rename-pres-allsafe ρ (allsafe-inr allsafe) = allsafe-inr (rename-pres-allsafe ρ allsafe)
rename-pres-allsafe ρ (allsafe-case allsafe-L allsafe-M allsafe-N) =
  allsafe-case (rename-pres-allsafe ρ allsafe-L) (rename-pres-allsafe ρ allsafe-M)
               (rename-pres-allsafe ρ allsafe-N)
rename-pres-allsafe ρ (allsafe-blame-diff-ℓ ℓ≢ℓ′) = allsafe-blame-diff-ℓ ℓ≢ℓ′

{- NOTE:
  Substitution preserves `CR<:` .
-}

-- What it means for a substitution to respect `CR<:` .
CastsAllSafe-σ : ∀ {Γ Δ} → Subst Γ Δ → Label → Set
CastsAllSafe-σ {Γ} {Δ} σ ℓ = ∀ {X} → (x : Γ ∋ X) → CastsAllSafe {A = X} (σ x) ℓ

-- We need a lemma about `exts`, as always.
exts-allsafe : ∀ {Γ Δ X} {σ : Subst Γ Δ} {ℓ}
  → CastsAllSafe-σ σ ℓ → CastsAllSafe-σ (exts σ {B = X}) ℓ
exts-allsafe allsafe-σ Z = allsafe-var
exts-allsafe allsafe-σ (S x) = rename-pres-allsafe S_ (allsafe-σ x)

subst-pres-allsafe : ∀ {Γ Δ A} {M : Γ ⊢ A} {σ : Subst Γ Δ} {ℓ}
  → CastsAllSafe-σ σ ℓ
    ---------------------------------------------------
  → CastsAllSafe M ℓ → CastsAllSafe (subst σ M) ℓ
subst-pres-allsafe allsafe-σ (allsafe-cast-same-ℓ safe eq allsafe) = allsafe-cast-same-ℓ safe eq (subst-pres-allsafe allsafe-σ allsafe)
subst-pres-allsafe allsafe-σ (allsafe-cast-diff-ℓ neq allsafe) = allsafe-cast-diff-ℓ neq (subst-pres-allsafe allsafe-σ allsafe)
subst-pres-allsafe allsafe-σ (allsafe-var {x = x}) = allsafe-σ x
-- Need to prove that `exts σ` satisfies `CR<:-σ` .
subst-pres-allsafe allsafe-σ (allsafe-ƛ allsafe) = allsafe-ƛ (subst-pres-allsafe (exts-allsafe allsafe-σ) allsafe)
subst-pres-allsafe allsafe-σ (allsafe-· allsafe-L allsafe-M) = allsafe-· (subst-pres-allsafe allsafe-σ allsafe-L) (subst-pres-allsafe allsafe-σ allsafe-M)
subst-pres-allsafe allsafe-σ allsafe-prim = allsafe-prim
subst-pres-allsafe allsafe-σ (allsafe-if allsafe-L allsafe-M allsafe-N) =
  allsafe-if (subst-pres-allsafe allsafe-σ allsafe-L) (subst-pres-allsafe allsafe-σ allsafe-M)
                                                      (subst-pres-allsafe allsafe-σ allsafe-N)
subst-pres-allsafe allsafe-σ (allsafe-cons allsafe-M allsafe-N) =
  allsafe-cons (subst-pres-allsafe allsafe-σ allsafe-M) (subst-pres-allsafe allsafe-σ allsafe-N)
subst-pres-allsafe allsafe-σ (allsafe-fst allsafe) = allsafe-fst (subst-pres-allsafe allsafe-σ allsafe)
subst-pres-allsafe allsafe-σ (allsafe-snd allsafe) = allsafe-snd (subst-pres-allsafe allsafe-σ allsafe)
subst-pres-allsafe allsafe-σ (allsafe-inl allsafe) = allsafe-inl (subst-pres-allsafe allsafe-σ allsafe)
subst-pres-allsafe allsafe-σ (allsafe-inr allsafe) = allsafe-inr (subst-pres-allsafe allsafe-σ allsafe)
subst-pres-allsafe allsafe-σ (allsafe-case allsafe-L allsafe-M allsafe-N) =
  allsafe-case (subst-pres-allsafe allsafe-σ allsafe-L) (subst-pres-allsafe allsafe-σ allsafe-M)
                                                        (subst-pres-allsafe allsafe-σ allsafe-N)
subst-pres-allsafe allsafe-σ (allsafe-blame-diff-ℓ ℓ≢ℓ′) = allsafe-blame-diff-ℓ ℓ≢ℓ′

subst-zero-allafe : ∀ {Γ A} {M : Γ ⊢ A} {ℓ}
  → CastsAllSafe M ℓ
  → CastsAllSafe-σ (subst-zero M) ℓ
subst-zero-allafe allsafe Z = allsafe
subst-zero-allafe allsafe (S x) = allsafe-var

substitution-allsafe : ∀ {Γ A B} {N : Γ , A ⊢ B} {M : Γ ⊢ A} {ℓ}
  → CastsAllSafe N ℓ
  → CastsAllSafe M ℓ
    -----------------------------
  → CastsAllSafe ( N [ M ] ) ℓ
substitution-allsafe allsafe-N allsafe-M = subst-pres-allsafe (subst-zero-allafe allsafe-M) allsafe-N
