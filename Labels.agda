module Labels where

  open import Data.Nat
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

  data Label : Set where
    pos : ℕ → Label
    neg : ℕ → Label

  flip : Label → Label
  flip (pos ℓ) = (neg ℓ)
  flip (neg ℓ) = (pos ℓ)

  label→ℕ : Label → ℕ
  label→ℕ (pos ℓ) = ℓ
  label→ℕ (neg ℓ) = ℓ

  {- NOTE:
    Polarity-unaware blame label comparison.
    Positive and negative labels are considered the same as long as they have the same number.
  -}
  infix 10 _≡̂_
  infix 10 _≢̂_

  data _≡̂_ : Label → Label → Set where
    refl++ : ∀ {n} → pos n ≡̂ pos n
    refl+- : ∀ {n} → pos n ≡̂ neg n
    refl-+ : ∀ {n} → neg n ≡̂ pos n
    refl-- : ∀ {n} → neg n ≡̂ neg n

  _≢̂_ : Label → Label → Set
  ℓ₁ ≢̂ ℓ₂ = ¬ ℓ₁ ≡̂ ℓ₂

  ≡̂-refl : ∀ {ℓ} → ℓ ≡̂ ℓ
  ≡̂-refl {pos n} = refl++
  ≡̂-refl {neg n} = refl--

  ≢̂→≢̂flip : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≢̂ ℓ₂ → ℓ₁ ≢̂ flip ℓ₂
  ≢̂→≢̂flip {pos n₁} {pos .n₁} neq refl+- = neq refl++
  ≢̂→≢̂flip {pos n₁} {neg .n₁} neq refl++ = neq refl+-
  ≢̂→≢̂flip {neg n₁} {pos .n₁} neq refl-- = neq refl-+
  ≢̂→≢̂flip {neg n₁} {neg .n₁} neq refl-+ = neq refl--

  -- ≡̂ implies labels are numbered the same.
  ≡̂-inv : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≡̂ ℓ₂ → (label→ℕ ℓ₁) ≡ (label→ℕ ℓ₂)
  ≡̂-inv refl++ = refl
  ≡̂-inv refl+- = refl
  ≡̂-inv refl-+ = refl
  ≡̂-inv refl-- = refl

  label-eq? : ∀ (ℓ₁ ℓ₂ : Label) → Dec (ℓ₁ ≡ ℓ₂)
  label-eq? (pos x₁) (pos x₂) with x₁ ≟ x₂
  ... | yes x₁≡x₂ = yes (cong pos x₁≡x₂)
  ... | no  x₁≢x₂ = no λ { refl → x₁≢x₂ refl }
  label-eq? (pos _) (neg _) = no λ ()
  label-eq? (neg _) (pos _) = no λ ()
  label-eq? (neg x₁) (neg x₂) with x₁ ≟ x₂
  ... | yes x₁≡x₂ = yes (cong neg x₁≡x₂)
  ... | no  x₁≢x₂ = no λ { refl → x₁≢x₂ refl }
