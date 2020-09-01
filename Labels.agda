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

  label-eq? : ∀ (𝓁₁ 𝓁₂ : Label) → Dec (𝓁₁ ≡ 𝓁₂)
  label-eq? (pos x₁) (pos x₂) with x₁ ≟ x₂
  ... | yes x₁≡x₂ = yes (cong pos x₁≡x₂)
  ... | no  x₁≢x₂ = no λ { refl → x₁≢x₂ refl }
  label-eq? (pos _) (neg _) = no λ ()
  label-eq? (neg _) (pos _) = no λ ()
  label-eq? (neg x₁) (neg x₂) with x₁ ≟ x₂
  ... | yes x₁≡x₂ = yes (cong neg x₁≡x₂)
  ... | no  x₁≢x₂ = no λ { refl → x₁≢x₂ refl }
