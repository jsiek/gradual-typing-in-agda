open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Product using (_×_; Σ; Σ-syntax)

open import Types
open import Labels
open import PreCastStructure


module PreCastStructureWithPrecision where

{- This record contains precision relations and corresponding lemmas. -}
record PreCastStructWithPrecision : Set₁ where
  field
    pcss : PreCastStructWithSafety
  open PreCastStructWithSafety pcss public
  infix 6 ⟪_⟫⊑⟪_⟫
  infix 6 ⟪_⟫⊑_
  infix 6 _⊑⟪_⟫
  field
    {- ****** Precision relations of (inert) casts: ****** -}
    ⟪_⟫⊑⟪_⟫ : ∀ {A A′ B B′} → {c : Cast (A ⇒ B)} → {c′ : Cast (A′ ⇒ B′)}
                            → (i : Inert c) → (i′ : Inert c′) → Set
    ⟪_⟫⊑_ : ∀ {A B} → {c : Cast (A ⇒ B)} → Inert c → Type → Set
    _⊑⟪_⟫ : ∀ {A′ B′} → {c′ : Cast (A′ ⇒ B′)} → Type → Inert c′ → Set

    {- ****** The definitions above need to satisfy the following lemmas: ****** -}
    {- If an inert injection is less precise than another inert cast,
       the latter must also be an injection from the same type. -}
    inj-⊑-inj : ∀ {A A′ B′} {c : Cast (A ⇒ ⋆)} {c′ : Cast (A′ ⇒ B′)}
      → (i : Inert c) → (i′ : Inert c′)
      → ⟪ i ⟫⊑⟪ i′ ⟫
        --------------------
      → (A′ ≡ A) × (B′ ≡ ⋆)
    {- Dynamic type ⋆ is never less precise than any inert cast. -}
    ⋆-⋢-inert : ∀ {A′ B′} {c′ : Cast (A′ ⇒ B′)}
      → (i′ : Inert c′)
        ----------------
      → ¬ (⋆ ⊑⟪ i′ ⟫)

    ⊑→lpit : ∀ {A B A′} {c : Cast (A ⇒ B)}
      → (i : Inert c) → A ⊑ A′ → B ⊑ A′ → ⟪ i ⟫⊑ A′
    lpii→⊑ : ∀ {A A′ B B′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)} {i : Inert c} {i′ : Inert c′}
      → ⟪ i ⟫⊑⟪ i′ ⟫ → (A ⊑ A′) × (B ⊑ B′)
    lpit→⊑ : ∀ {A A′ B} {c : Cast (A ⇒ B)} {i : Inert c}
      → ⟪ i ⟫⊑ A′    → (A ⊑ A′) × (B ⊑ A′)
    lpti→⊑ : ∀ {A A′ B′} {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
      → A ⊑⟪ i′ ⟫    → (A ⊑ A′) × (A ⊑ B′)
