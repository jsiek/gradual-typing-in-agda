open import Data.Unit using (⊤) renaming (tt to unit)
open import Data.List
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; cong-app)

open import Types
open import Labels
open import PreCastStructure

open import Syntax

module ParamCastCalculusABT (pcs : PreCastStruct) where

  open import ParamCCSyntaxABT pcs public

  {-
    Here we define the Cast Calculus in a way that parameterizes over the
    actual casts, to enable succinct definitions and proofs of type safety
    for many different cast calculi.  The Agda type constructor for
    representing casts is given by the module parameter named Cast.  The
    Type argument to Cast is typically a function type whose domain is the
    source of the cast and whose codomain is the target type of the
    cast. However, in cast calculi with fancy types such as intersections,
    the type of a cast may not literally be a function type.
  -}

  private
    𝑉⊢ : List Type → Var → Type → Type → Set
    𝑃⊢ : (op : Op) → Vec Type (length (sig op)) → BTypes Type (sig op) → Type → Set

  --   ⊢var : ∀ {Γ A} {x : ℕ}
  --     → Γ ∋ x ⦂ A
  --       --------------
  --     → Γ ⊢ ` x ⦂ A
  𝑉⊢ Γ x A B = A ≡ B

  --   ⊢lam : ∀ {Γ A B} {N}
  --     → Γ , A ⊢ N ⦂ B
  --       -------------------
  --     → Γ ⊢ ƛ A ˙ N ⦂ A ⇒ B
  𝑃⊢ (op-lam A₁) (B ∷ᵥ []ᵥ) ⟨ ⟨ A , tt ⟩ , tt ⟩ C =
    C ≡ A ⇒ B × A ≡ A₁

  --   ⊢app : ∀ {Γ A B} {L M}
  --     → Γ ⊢ L ⦂ A ⇒ B
  --     → Γ ⊢ M ⦂ A
  --       --------------------
  --     → Γ ⊢ L · M ⦂ B
  𝑃⊢ op-app (C ∷ᵥ A ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , tt ⟩ ⟩ B =
    C ≡ A ⇒ B

  --   ⊢lit : ∀ {Γ A} {r : rep A} {p : Prim A}
  --       ------------------
  --     → Γ ⊢ $ r # p ⦂ A
  𝑃⊢ (op-lit {A₁} r p) []ᵥ tt A = A ≡ A₁

  --   ⊢if : ∀ {Γ A} {L M N}
  --     → Γ ⊢ L ⦂ ` 𝔹
  --     → Γ ⊢ M ⦂ A
  --     → Γ ⊢ N ⦂ A
  --       --------------------------------------
  --     → Γ ⊢ if L then M else N endif ⦂ A
  𝑃⊢ op-if (B ∷ᵥ A₁ ∷ᵥ A₂ ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , ⟨ tt , tt ⟩ ⟩ ⟩ A =
    (A ≡ A₁ × A₁ ≡ A₂) × B ≡ ` 𝔹

  --   ⊢cons : ∀ {Γ A B} {M N}
  --     → Γ ⊢ M ⦂ A
  --     → Γ ⊢ N ⦂ B
  --       -------------------------
  --     → Γ ⊢ ⟦ M , N ⟧ ⦂ A `× B
  𝑃⊢ op-cons (A ∷ᵥ B ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , tt ⟩ ⟩ C = C ≡ A `× B

  --   ⊢fst : ∀ {Γ A B} {M}
  --     → Γ ⊢ M ⦂ A `× B
  --       ---------------------
  --     → Γ ⊢ fst M ⦂ A
  𝑃⊢ op-fst (C ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ A = ∃[ B ] C ≡ A `× B

  --   ⊢snd : ∀ {Γ A B} {M}
  --     → Γ ⊢ M ⦂ A `× B
  --       ---------------------
  --     → Γ ⊢ snd M ⦂ B
  𝑃⊢ op-snd (C ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ B = ∃[ A ] C ≡ A `× B

  --   ⊢inl : ∀ {Γ A B} {M}
  --     → Γ ⊢ M ⦂ A
  --       --------------------------
  --     → Γ ⊢ inl M other B ⦂ A `⊎ B
  𝑃⊢ (op-inl B) (A ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ C = C ≡ A `⊎ B

  --   ⊢inr : ∀ {Γ A B} {M}
  --     → Γ ⊢ M ⦂ B
  --       --------------------------
  --     → Γ ⊢ inr M other A ⦂ A `⊎ B
  𝑃⊢ (op-inr A) (B ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ C = C ≡ A `⊎ B

  --   ⊢case : ∀ {Γ A B C} {L M N}
  --     → Γ ⊢ L ⦂ A `⊎ B
  --     → Γ , A ⊢ M ⦂ C
  --     → Γ , B ⊢ N ⦂ C
  --       -----------------------------------------
  --     → Γ ⊢ case L of A ⇒ M ∣ B ⇒ N ⦂ C
  𝑃⊢ (op-case A₁ B₁) (X ∷ᵥ C₁ ∷ᵥ C₂ ∷ᵥ []ᵥ) ⟨ tt , ⟨ ⟨ A , tt ⟩ , ⟨ ⟨ B , tt ⟩ , tt ⟩ ⟩ ⟩ C =
    (C ≡ C₁ × C₁ ≡ C₂) × (X ≡ A `⊎ B × A ≡ A₁ × B ≡ B₁)

  --   ⊢cast : ∀ {Γ A B} {M}
  --     → Γ ⊢ M ⦂ A
  --     → (c : Cast (A ⇒ B))
  --       --------------------
  --     → Γ ⊢ M ⟨ c ⟩ ⦂ B
  𝑃⊢ (op-cast {A₁} {B₁} c) (A ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ B = A ≡ A₁ × B ≡ B₁

  --   ⊢wrap : ∀ {Γ A B} {M}
  --     → Γ ⊢ M ⦂ A
  --     → (c : Cast (A ⇒ B))
  --     → (i : Inert c)
  --       ---------------------
  --     → Γ ⊢ M ⟨ c ₍ i ₎⟩ ⦂ B
  𝑃⊢ (op-wrap {A₁} {B₁} c i) (A ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ B = A ≡ A₁ × B ≡ B₁

  --   ⊢blame : ∀ {Γ A} {ℓ}
  --       -----------------
  --     → Γ ⊢ blame ℓ ⦂ A
  𝑃⊢ (op-blame _) []ᵥ tt A = ⊤

  pattern 𝐶⊢-ƛ = ⟨ refl , refl ⟩
  pattern 𝐶⊢-· = refl
  pattern 𝐶⊢-$ = refl
  pattern 𝐶⊢-if = ⟨ ⟨ refl , refl ⟩ , refl ⟩
  pattern 𝐶⊢-cons = refl
  pattern 𝐶⊢-fst = ⟨ _ , refl ⟩
  pattern 𝐶⊢-snd = ⟨ _ , refl ⟩
  pattern 𝐶⊢-inl = refl
  pattern 𝐶⊢-inr = refl
  pattern 𝐶⊢-case = ⟨ ⟨ refl , refl ⟩ , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩
  pattern 𝐶⊢-cast = ⟨ refl , refl ⟩
  pattern 𝐶⊢-wrap = ⟨ refl , refl ⟩
  pattern 𝐶⊢-blame = unit

  infix  4  _⊢_⦂_
  open import ABTPredicate Op sig 𝑉⊢ 𝑃⊢ public renaming (_⊢_⦂_ to predicate)
  _⊢_⦂_ = predicate

  open import SubstPreserve Op sig Type 𝑉⊢ 𝑃⊢ (λ x → refl) (λ { refl refl → refl })
    (λ x → x) (λ { refl ⊢M → ⊢M }) public
      using (preserve-rename; preserve-subst; preserve-substitution)

  open import GenericPredicate pcs
  open GenericPredicatePatterns 𝑉⊢ 𝑃⊢ public
