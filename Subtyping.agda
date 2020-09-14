module Subtyping where

open import Types


-- The subtyping relation.
--   NOTE: Since simple cast is D, using traditional subtyping is fine.
infix 5 _<:₁_

data _<:₁_ : Type → Type → Set where

  T<:⋆ : ∀ {T}
       --------
    → T <:₁ ⋆

  <:-B : ∀ {B}
       -----------
    → ` B <:₁ ` B

  -- Product and sum are monotone with respect to subtyping.
  <:-× : ∀ {S₁ S₂ T₁ T₂}
    → S₁ <:₁ T₁ → S₂ <:₁ T₂
      -----------------------
    → S₁ `× S₂ <:₁ T₁ `× T₂

  <:-⊎ : ∀ {S₁ S₂ T₁ T₂}
    → S₁ <:₁ T₁ → S₂ <:₁ T₂
      -----------------------
    → S₁ `⊎ S₂ <:₁ T₁ `⊎ T₂

  <:-⇒ : ∀ {S₁ S₂ T₁ T₂}
    → T₁ <:₁ S₁ → S₂ <:₁ T₂
      -----------------------
    → S₁ ⇒ S₂ <:₁ T₁ ⇒ T₂
