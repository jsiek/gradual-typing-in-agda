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

  open import ParamCastCalculusABT precast hiding (𝑉; 𝑃)

  private
    𝑉 : List Label → Var → Label → Label → Set
    𝑃 : (op : Op) → Vec Label (length (sig op)) → BTypes Label (sig op) → Label → Set

  -- data CastsAllSafe : ∀ (M : Term) → (ℓ : Label) → Set where

  --   allsafe-var : ∀ {x} {ℓ}
  --       ------------------------------
  --     → CastsAllSafe (` x) ℓ
  𝑉 _ _ ℓ′ ℓ = ℓ ≡ ℓ′

  --   allsafe-cast : ∀ {S T} {M : Term} {c : Cast (S ⇒ T)} {ℓ}
  --     → CastBlameSafe c ℓ
  --     → CastsAllSafe M ℓ
  --       -------------------------------------
  --     → CastsAllSafe (M ⟨ c ⟩) ℓ
  𝑃 (op-cast c) (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = CastBlameSafe c ℓ × ℓ ≡ ℓₘ

  --   allsafe-wrap : ∀ {S T} {M : Term} {c : Cast (S ⇒ T)} {i : Inert c} {ℓ}
  --     → CastBlameSafe c ℓ
  --     → CastsAllSafe M ℓ
  --       -------------------------------------
  --     → CastsAllSafe (M ⟨ c ₍ i ₎⟩) ℓ
  𝑃 (op-wrap c i) (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = CastBlameSafe c ℓ × ℓ ≡ ℓₘ

  --   allsafe-ƛ : ∀ {A} {N : Term} {ℓ}
  --     → CastsAllSafe N ℓ
  --       -----------------------
  --     → CastsAllSafe (ƛ A ˙ N) ℓ
  𝑃 (op-lam _) (ℓₙ ∷ᵥ []ᵥ) ⟨ ⟨ ℓ′ , tt ⟩ , tt ⟩ ℓ = ℓ ≡ ℓ′ × ℓ ≡ ℓₙ

  --   allsafe-· : ∀ {L M : Term} {ℓ}
  --     → CastsAllSafe L ℓ
  --     → CastsAllSafe M ℓ
  --       -------------------------
  --     → CastsAllSafe (L · M) ℓ
  𝑃 op-app (ℓₗ ∷ᵥ ℓₘ ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , tt ⟩ ⟩ ℓ = ℓ ≡ ℓₗ × ℓ ≡ ℓₘ

  --   allsafe-prim : ∀ {A} {r : rep A} {p : Prim A} {ℓ}
  --       --------------------------------------------
  --     → CastsAllSafe ($ r # p) ℓ
  𝑃 (op-lit r p) []ᵥ tt ℓ = ⊤

  --   allsafe-if : ∀ {L M N : Term} {ℓ}
  --     → CastsAllSafe L ℓ
  --     → CastsAllSafe M ℓ
  --     → CastsAllSafe N ℓ
  --       -----------------------------
  --     → CastsAllSafe (if L then M else N endif) ℓ
  𝑃 op-if (ℓₗ ∷ᵥ ℓₘ ∷ᵥ ℓₙ ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , ⟨ tt , tt ⟩ ⟩ ⟩ ℓ = ℓ ≡ ℓₗ × ℓ ≡ ℓₘ × ℓ ≡ ℓₙ

  --   allsafe-cons : ∀ {M N : Term} {ℓ}
  --     → CastsAllSafe M ℓ
  --     → CastsAllSafe N ℓ
  --       ----------------------------
  --     → CastsAllSafe ⟦ M , N ⟧ ℓ
  𝑃 op-cons (ℓₘ ∷ᵥ ℓₙ ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , tt ⟩ ⟩ ℓ = ℓ ≡ ℓₘ × ℓ ≡ ℓₙ

  --   allsafe-fst : ∀ {M : Term} {ℓ}
  --     → CastsAllSafe M ℓ
  --       -------------------------
  --     → CastsAllSafe (fst M) ℓ
  𝑃 op-fst (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = ℓ ≡ ℓₘ

  --   allsafe-snd : ∀ {M : Term} {ℓ}
  --     → CastsAllSafe M ℓ
  --       -------------------------
  --     → CastsAllSafe (snd M) ℓ
  𝑃 op-snd (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = ℓ ≡ ℓₘ

  --   allsafe-inl : ∀ {B} {M : Term} {ℓ}
  --     → CastsAllSafe M ℓ
  --       ---------------------------------
  --     → CastsAllSafe (inl M other B) ℓ
  𝑃 (op-inl _) (ℓₘ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = ℓ ≡ ℓₘ

  --   allsafe-inr : ∀ {A} {N : Term} {ℓ}
  --     → CastsAllSafe N ℓ
  --       ----------------------------------
  --     → CastsAllSafe (inr N other A) ℓ
  𝑃 (op-inr _) (ℓₙ ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ ℓ = ℓ ≡ ℓₙ

  --   allsafe-case : ∀ {A B} {L M N} {ℓ}
  --     → CastsAllSafe L ℓ
  --     → CastsAllSafe M ℓ
  --     → CastsAllSafe N ℓ
  --       ------------------------------
  --     → CastsAllSafe (case L of A ⇒ M ∣ B ⇒ N) ℓ
  𝑃 (op-case _ _) (ℓₗ ∷ᵥ ℓₘ ∷ᵥ ℓₙ ∷ᵥ []ᵥ) ⟨ tt , ⟨ ⟨ _ , tt ⟩ , ⟨ ⟨ _ , tt ⟩ , tt ⟩ ⟩ ⟩ ℓ =
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
  𝑃 (op-blame ℓ′) []ᵥ tt ℓ = ℓ ≢̂ ℓ′

  open import ABTPredicate Op sig 𝑉 𝑃 public
    renaming (_⊢_⦂_ to predicate-allsafe;
                    _∣_∣_⊢ₐ_⦂_ to predicateₐ-allsafe;
                    _∣_∣_⊢₊_⦂_ to predicate₊-allsafe)

  CastsAllSafe : Term → Label → Set  -- CastsAllSafe M ℓ
  CastsAllSafe = predicate-allsafe []

  {- NOTE: The `op-p`, `cons-p` ... here refer to the constructors of
    `predicate-allsafe` so we can't directly reuse the patterns defined
    in the typing rules, although they're structually the same. -}
  pattern pₛ` ∋x = var-p ∋x refl

  pattern pₛƛ A ⊢N eq = op-p {op = op-lam A} (cons-p (bind-p (ast-p ⊢N)) nil-p) eq

  pattern pₛ· ⊢L ⊢M eq = op-p {op = op-app}
                              (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq
    -- predicate-allsafe.op-p {op = op-app}
    --   (predicate₊-allsafe.cons-p (predicateₐ-allsafe.ast-p ⊢L)
    --     (predicate₊-allsafe.cons-p (predicateₐ-allsafe.ast-p ⊢M) predicate₊-allsafe.nil-p)) eq

  pattern pₛ$ r p eq = op-p {op = op-lit r p} nil-p eq

  pattern pₛif ⊢L ⊢M ⊢N eq = op-p {op = op-if}
                                  (cons-p (ast-p ⊢L)
                                          (cons-p (ast-p ⊢M)
                                                  (cons-p (ast-p ⊢N) nil-p))) eq

  pattern pₛcons ⊢M ⊢N eq = op-p {op = op-cons}
                            (cons-p (ast-p ⊢M) (cons-p (ast-p ⊢N) nil-p)) eq

  pattern pₛfst ⊢M eq = op-p {op = op-fst} (cons-p (ast-p ⊢M) nil-p) eq

  pattern pₛsnd ⊢M eq = op-p {op = op-snd} (cons-p (ast-p ⊢M) nil-p) eq

  pattern pₛinl B ⊢M eq = op-p {op = op-inl B} (cons-p (ast-p ⊢M) nil-p) eq

  pattern pₛinr A ⊢M eq = op-p {op = op-inr A} (cons-p (ast-p ⊢M) nil-p) eq

  pattern pₛcase A B ⊢L ⊢M ⊢N eq = op-p {op = op-case A B}
                                        (cons-p (ast-p ⊢L)
                                                (cons-p (bind-p (ast-p ⊢M))
                                                        (cons-p (bind-p (ast-p ⊢N)) nil-p))) eq

  pattern pₛcast c ⊢M eq = op-p {op = op-cast c} (cons-p (ast-p ⊢M) nil-p) eq

  pattern pₛwrap c i ⊢M eq = op-p {op = op-wrap c i} (cons-p (ast-p ⊢M) nil-p) eq

  pattern pₛblame ℓ eq = op-p {op = op-blame ℓ} nil-p eq


  open import SubstPreserve Op sig Label 𝑉 𝑃 (λ _ → refl) (λ { refl refl → refl })
    (λ x → x) (λ { refl pM → pM }) public
      renaming (preserve-rename to rename-pres-allsafe;
                                preserve-subst to subst-pres-allsafe;
                                preserve-substitution to substitution-allsafe)
