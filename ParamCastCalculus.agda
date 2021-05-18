open import Types

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
module ParamCastCalculus (Cast : Type → Set) (Inert : ∀ {A} → Cast A → Set) where

open import Variables
open import Labels
open import Data.Nat
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

{-

We define well-typed expressions with the following typing judgment.
Compared to the STLC, there are two important new features.
The cast is written M ⟨ c ⟩, where M is an expression and c
is a cast (whatever that may be). We also have blame ℓ for
raising uncatchable exceptions.  

-}

infix  4 _⊢_
infix 7 _·_
infix 8 _⟨_⟩

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
    → Γ ⊢ A ⇒ B  →  Γ ⊢ A
      ------------------
    → Γ ⊢ B

  $_ : ∀ {Γ A}
    → rep A
    → {f : Prim A}       {- todo: change side condition to irrelevant -}
      -----
    → Γ ⊢ A

  if : ∀ {Γ A}
    → Γ ⊢ ` 𝔹 → Γ ⊢ A → Γ ⊢ A
      -----------------------
    → Γ ⊢ A

  cons : ∀ {Γ A B}
    → Γ ⊢ A → Γ ⊢ B
      ---------------------
    → Γ ⊢ A `× B

  fst : ∀ {Γ A B}
    → Γ ⊢ A `× B
      ---------------------
    → Γ ⊢ A

  snd : ∀ {Γ A B}
    → Γ ⊢ A `× B
      ---------------------
    → Γ ⊢ B

  inl : ∀ {Γ A B}
    → Γ ⊢ A
      ----------
    → Γ ⊢ A `⊎ B

  inr : ∀ {Γ A B}
    → Γ ⊢ B
      ----------
    → Γ ⊢ A `⊎ B

  case : ∀ {Γ A B C}
    → Γ ⊢ A `⊎ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
      ----------
    → Γ ⊢ C

  _⟨_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Cast (A ⇒ B)
      --------------
    → Γ ⊢ B

  {- I would prefer that the cast be an explicit
     parameter and that Inert c be an implicit,
     "irrelevant" parameter, as in .{ i : Inert c}. -Jeremy -}
  _⟪_⟫ : ∀ {Γ A B} {c : Cast (A ⇒ B)}
    → Γ ⊢ A
    → Inert c
      --------
    → Γ ⊢ B

  blame : ∀ {Γ A} → Label → Γ ⊢ A

{-

The addition of casts and blame does not introduce any
complications regarding substitution. So the following
definitions are essentially the same as for the STLC.

-}


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
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (($ k) {f})    = ($ k) {f}
rename ρ (if L M N)     =  if (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (cons L M)     = cons (rename ρ L) (rename ρ M)
rename ρ (fst M)        = fst (rename ρ M)
rename ρ (snd M)        = snd (rename ρ M)
rename ρ (inl M)        = inl (rename ρ M)
rename ρ (inr M)        = inr (rename ρ M)
rename ρ (case L M N)   = case (rename ρ L) (rename (ext ρ) M) (rename (ext ρ) N)
rename ρ (M ⟨ c ⟩)      =  ((rename ρ M) ⟨ c ⟩)
rename ρ (M ⟪ c ⟫)      =  ((rename ρ M) ⟪ c ⟫)
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
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (($ k){f})     =  ($ k){f}
subst σ (if L M N)     =  if (subst σ L) (subst σ M) (subst σ N)
subst σ (cons M N)     =  cons (subst σ M) (subst σ N)
subst σ (fst M)     =  fst (subst σ M)
subst σ (snd M)     =  snd (subst σ M)
subst σ (inl M)     =  inl (subst σ M)
subst σ (inr M)     =  inr (subst σ M)
subst σ (case L M N)     =  case (subst σ L) (subst (exts σ) M) (subst (exts σ) N)
subst σ (M ⟨ c ⟩)      =  (subst σ M) ⟨ c ⟩
subst σ (M ⟪ c ⟫)      =  (subst σ M) ⟪ c ⟫
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

{-
  The type signatures for `rename` and `substitution`.
-}
Rename : Context → Context → Set
Rename Γ Δ = ∀ {X} → Γ ∋ X → Δ ∋ X

Subst : Context → Context → Set
Subst Γ Δ = ∀ {X} → Γ ∋ X → Δ ⊢ X
