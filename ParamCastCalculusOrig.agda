open import Types

{-

This module is the same as `ParamCastCalculus` except it doesn't contain the `wrap` clause for
inert cast - any cast term is represented with a single constructor `cast`.

-}


module ParamCastCalculusOrig (Cast : Type → Set) where

open import Variables
open import Labels
open import Data.Nat
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

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
    → {f : Prim A}
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

  {- NOTE: We currently do *not* build binders in here,
    since otherwise it requires changing each representation.
    If we would like to do the gradual guarantee proof, it is
    worthwhile to change this, similar to `ParamCastCalculus`.
    -}
  case : ∀ {Γ A B C}
    → Γ ⊢ A `⊎ B
    → Γ ⊢ A ⇒ C
    → Γ ⊢ B ⇒ C
      ----------
    → Γ ⊢ C

  _⟨_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Cast (A ⇒ B)
      ----------------------
    → Γ ⊢ B

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
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (($ k) {f})    = ($ k) {f}
rename ρ (if L M N)     =  if (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (cons L M)     = cons (rename ρ L) (rename ρ M)
rename ρ (fst M)        = fst (rename ρ M)
rename ρ (snd M)        = snd (rename ρ M)
rename ρ (inl M)        = inl (rename ρ M)
rename ρ (inr M)        = inr (rename ρ M)
rename ρ (case L M N)   = case (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (M ⟨ c ⟩)      =  ((rename ρ M) ⟨ c ⟩)
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
subst σ (case L M N)     =  case (subst σ L) (subst σ M) (subst σ N)
subst σ (M ⟨ c ⟩)      =  (subst σ M) ⟨ c ⟩
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



size : ∀{Γ A} → Γ ⊢ A → ℕ
size (` x) = 1
size (ƛ M) = suc (size M)
size (L · M) = suc (size L + size M)
size ($ x) = 1
size (if L M N) = suc (size L + size M + size N)
size (cons M N) = suc (size M + size N)
size (fst M) = suc (size M)
size (snd M) = suc (size M)
size (inl M) = suc (size M)
size (inr M) = suc (size M)
size (case L M N) = suc (size L + size M + size N)
size (M ⟨ c ⟩) = suc (size M)
size (blame ℓ) = 1

ideal-size : ∀{Γ A} → Γ ⊢ A → ℕ
ideal-size (` x) = 1
ideal-size (ƛ M) = suc (ideal-size M)
ideal-size (L · M) = suc (ideal-size L + ideal-size M)
ideal-size ($ x) = 1
ideal-size (if L M N) = suc (ideal-size L + ideal-size M + ideal-size N)
ideal-size (cons M N) = suc (ideal-size M + ideal-size N)
ideal-size (fst M) = suc (ideal-size M)
ideal-size (snd M) = suc (ideal-size M)
ideal-size (inl M) = suc (ideal-size M)
ideal-size (inr M) = suc (ideal-size M)
ideal-size (case L M N) = suc (ideal-size L + ideal-size M + ideal-size N)
ideal-size (M ⟨ c ⟩) = ideal-size M
ideal-size (blame ℓ) = 1

data _∣_⊢_ok : ∀{Γ A} → ℕ → Bool → Γ ⊢ A  → Set where
  castulOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}
           → n ∣ true ⊢ M ok  →  n ≤ 1
           → suc n ∣ true ⊢ M ⟨ c ⟩ ok
  castOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}
           → n ∣ false ⊢ M ok  →  n ≤ 2
           → suc n ∣ false ⊢ M ⟨ c ⟩ ok
  varOK : ∀{Γ A}{∋x : Γ ∋ A}{ul}
         {- We pre-count a 1 here because a value may have 1 cast
            and get substituted for this variable. -}
        → 1 ∣ ul ⊢ (` ∋x) ok
  lamOK : ∀{Γ B A}{N : Γ , A ⊢ B}{n}{ul}
        → n ∣ true ⊢ N ok
        → 0 ∣ ul ⊢ (ƛ N) ok
  appOK : ∀{Γ A B}{L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}{ul}{n}{m}
        → n ∣ ul ⊢ L ok → m ∣ ul ⊢ M ok
        → 0 ∣ ul ⊢ (L · M) ok
  litOK : ∀{Γ : Context}{A}{r : rep A}{p : Prim A}{ul}
        → 0 ∣ ul ⊢ ($_ {Γ} r {p}) ok
  ifOK : ∀{Γ A}{L : Γ ⊢ ` 𝔹}{M N : Γ ⊢ A}{n m k}{ul}
        → n ∣ ul ⊢ L ok → m ∣ true ⊢ M ok → k ∣ true ⊢ N ok
        → 0 ∣ ul ⊢ (if L M N) ok
  consOK : ∀{Γ A B}{M : Γ ⊢ A}{N : Γ ⊢ B}{n m}{ul}
        → n ∣ ul ⊢ M ok → m ∣ ul ⊢ N ok
        → 0 ∣ ul ⊢ (cons M N) ok
  fstOK : ∀{Γ A B}{M : Γ ⊢ A `× B}{n}{ul}
        → n ∣ ul ⊢ M ok
        → 0 ∣ ul ⊢ fst M ok
  sndOK : ∀{Γ A B}{M : Γ ⊢ A `× B}{n}{ul}
        → n ∣ ul ⊢ M ok
        → 0 ∣ ul ⊢ snd M ok
  inlOK : ∀{Γ A B}{M : Γ ⊢ A}{n}{ul}
        → n ∣ ul ⊢ M ok
        → 0 ∣ ul ⊢ (inl {B = B} M) ok
  inrOK : ∀{Γ A B}{M : Γ ⊢ B}{n}{ul}
        → n ∣ ul ⊢ M ok
        → 0 ∣ ul ⊢ (inr {A = A} M) ok
  caseOK : ∀{Γ A B C}{L : Γ ⊢ A `⊎ B}{M : Γ ⊢ A ⇒ C}{N : Γ ⊢ B ⇒ C}{n m k}{ul}
         → n ∣ ul ⊢ L ok → m ∣ true ⊢ M ok → k ∣ true ⊢ N ok
         → 0 ∣ ul ⊢ (case L M N) ok
  blameOK : ∀{Γ A ℓ}{ul}
         → 0 ∣ ul ⊢ (blame {Γ}{A} ℓ) ok
