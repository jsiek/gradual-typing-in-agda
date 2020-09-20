module Subtyping where

open import Types


-- The subtyping relation(s).
infix 5 _<:₁_
infix 5 _<:₂_
infix 5 _<:₃_

{-
  Traditional subtyping, where Dyn (⋆) is at its top.
  (The subtyping relations are in the same order as Fig. 3 in the 'Exploring the Design Space' paper. )
-}
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

{-
  Subtyping of WF-1. This is the rarely used one.
-}
data _<:₂_ : Type → Type → Set where

  <:-⋆ : ⋆ <:₂ ⋆

  <:-B : ∀ {B}
       -----------
    → ` B <:₂ ` B

  -- Product and sum are monotone with respect to subtyping.
  <:-× : ∀ {S₁ S₂ T₁ T₂}
    → S₁ <:₂ T₁ → S₂ <:₂ T₂
      -----------------------
    → S₁ `× S₂ <:₂ T₁ `× T₂

  <:-⊎ : ∀ {S₁ S₂ T₁ T₂}
    → S₁ <:₂ T₁ → S₂ <:₂ T₂
      -----------------------
    → S₁ `⊎ S₂ <:₂ T₁ `⊎ T₂

  <:-⇒ : ∀ {S₁ S₂ T₁ T₂}
    → T₁ <:₂ S₁ → S₂ <:₂ T₂
      -----------------------
    → S₁ ⇒ S₂ <:₂ T₁ ⇒ T₂

{-
  Subtyping of WF-2.
  This is usually used to characterize the cast safety of UD (which routes through ground types).
-}
data _<:₃_ : Type → Type → Set where

  <:-⋆ : ⋆ <:₃ ⋆

  <:-B : ∀ {B}
       -----------
    → ` B <:₃ ` B

  <:-G : ∀ {S G}
    → S <:₃ G → Ground G
      --------------------------
    → S <:₃ ⋆

  -- Product and sum are monotone with respect to subtyping.
  <:-× : ∀ {S₁ S₂ T₁ T₂}
    → S₁ <:₃ T₁ → S₂ <:₃ T₂
      -----------------------
    → S₁ `× S₂ <:₃ T₁ `× T₂

  <:-⊎ : ∀ {S₁ S₂ T₁ T₂}
    → S₁ <:₃ T₁ → S₂ <:₃ T₂
      -----------------------
    → S₁ `⊎ S₂ <:₃ T₁ `⊎ T₂

  <:-⇒ : ∀ {S₁ S₂ T₁ T₂}
    → T₁ <:₃ S₁ → S₂ <:₃ T₂
      -----------------------
    → S₁ ⇒ S₂ <:₃ T₁ ⇒ T₂
