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


ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → (Γ , B) ∋ A → (Δ , B) ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)


rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          = ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ ((L · M) c)    =  ((rename ρ L) · (rename ρ M)) c
rename ρ (($ k) {f})    = ($ k) {f}
rename ρ (if L M N c)   =  if (rename ρ L) (rename ρ M) (rename ρ N) c
rename ρ (cons L M)     = cons (rename ρ L) (rename ρ M)
rename ρ (fst M)        = fst (rename ρ M)
rename ρ (snd M)        = snd (rename ρ M)
rename ρ (inl M)        = inl (rename ρ M)
rename ρ (inr M)        = inr (rename ρ M)
rename ρ (case L M N cl cr) = case (rename ρ L) (rename ρ M) (rename ρ N) cl cr
rename ρ (blame ℓ)      =  blame ℓ

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)          =  σ x
subst σ (ƛ  N)         =  ƛ (subst (exts σ) N)
subst σ ((L · M) c)    =  ((subst σ L) · (subst σ M)) c
subst σ (($ k){f})     =  ($ k){f}
subst σ (if L M N c)   =  if (subst σ L) (subst σ M) (subst σ N) c
subst σ (cons M N)     =  cons (subst σ M) (subst σ N)
subst σ (fst M)     =  fst (subst σ M)
subst σ (snd M)     =  snd (subst σ M)
subst σ (inl M)     =  inl (subst σ M)
subst σ (inr M)     =  inr (subst σ M)
subst σ (case L M N cl cr) =  case (subst σ L) (subst σ M) (subst σ N) cl cr
subst σ (blame ℓ)      =  blame ℓ

subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x


_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N

