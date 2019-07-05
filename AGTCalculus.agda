open import Types

module AGTCalculus
  (convert : Type → Type → Set)
  (dom : Type → Type)
  (cod : Type → Type)
  (fst-ty : Type → Type)
  (snd-ty : Type → Type)
  (inl-ty : Type → Type)
  (inr-ty : Type → Type)
  (join : Type → Type → Type)
  (Label : Set)
  where

open import Variables

infix  4 _⊢_
infix 7 _·_

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ} {A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_ :  ∀ {Γ B A}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ} {A B}
    → Γ ⊢ A  →  Γ ⊢ B  → convert B (dom A)
      ------------------------------------
    → Γ ⊢ B

  $_ : ∀ {Γ A}
    → rep A
    → {f : Prim A}
      -----
    → Γ ⊢ A

  if : ∀ {Γ A B C}
    → Γ ⊢ A → Γ ⊢ B → Γ ⊢ C
    → convert A (` 𝔹)
      ---------------------
    → Γ ⊢ join A B

  cons : ∀ {Γ A B}
    → Γ ⊢ A → Γ ⊢ B
      ---------------------
    → Γ ⊢ A `× B

  fst : ∀ {Γ A}
    → Γ ⊢ A
      ---------------------
    → Γ ⊢ fst-ty A

  snd : ∀ {Γ A}
    → Γ ⊢ A
      ---------------------
    → Γ ⊢ snd-ty A

  inl : ∀ {Γ A B}
    → Γ ⊢ A
      ----------
    → Γ ⊢ A `⊎ B

  inr : ∀ {Γ A B}
    → Γ ⊢ B
      ----------
    → Γ ⊢ A `⊎ B

  case : ∀ {Γ A B C D E}
    → Γ ⊢ A
    → Γ ⊢ B ⇒ C
    → Γ ⊢ D ⇒ E
    → convert (inl-ty A) B
    → convert (inr-ty A) D
      --------------------
    → Γ ⊢ join C E

  blame : ∀ {Γ A} → Label → Γ ⊢ A
