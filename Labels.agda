module Labels where

  open import Data.Nat

  data Label : Set where
    pos : ℕ → Label
    neg : ℕ → Label

  flip : Label → Label
  flip (pos ℓ) = (neg ℓ)
  flip (neg ℓ) = (pos ℓ)

  label→ℕ : Label → ℕ
  label→ℕ (pos ℓ) = ℓ
  label→ℕ (neg ℓ) = ℓ
