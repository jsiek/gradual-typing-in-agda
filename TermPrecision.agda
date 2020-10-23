open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

-- We're using simple cast with inert cross cast - at least for now.
open import GroundInertX using (Cast)
open import Types
open import Variables
open import Labels

open import GTLC
import ParamCastCalculus
open ParamCastCalculus Cast


infix 6 _,_⊢_⊑ᴳ_
infix 6 _,_⊢_⊑ᶜ_

-- Term precision for GTLC - M₁ ⊑ᴳ M₂ means that M₂ is *more precise* than M₁ .
data _,_⊢_⊑ᴳ_ : ∀ (Γ Γ′ : Context) → {A A′ : Type} → Γ ⊢G A → Γ′ ⊢G A′ → Set where

  ⊑ᴳ-prim : ∀ {Γ Γ′ A} {k : rep A} {i : Prim A}
      ------------------------------
    → Γ , Γ′ ⊢ $_ {Γ} k {i} ⊑ᴳ $_ {Γ′} k {i}

  ⊑ᴳ-var : ∀ {Γ Γ′ A A′} {x : Γ ∋ A} {x′ : Γ′ ∋ A′}
    → ∋→ℕ x ≡ ∋→ℕ x′
      -----------------
    → Γ , Γ′ ⊢ ` x ⊑ᴳ ` x′

  ⊑ᴳ-ƛ : ∀ {Γ Γ′ A A′ B B′} {N : Γ , A ⊢G B} {N′ : Γ′ , A′ ⊢G B′}
    → A ⊑ A′
    → (Γ , A) , (Γ′ , A′) ⊢ N ⊑ᴳ N′
      ------------------------------
    → Γ , Γ′ ⊢ ƛ A ˙ N ⊑ᴳ ƛ A′ ˙ N′

  ⊑ᴳ-· : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′ B B′} {L : Γ ⊢G A} {L′ : Γ′ ⊢G A′} {M : Γ ⊢G B} {M′ : Γ′ ⊢G B′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ L ⊑ᴳ L′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → {m : A ▹ A₁ ⇒ A₂} {cn : A₁ ~ B} {m′ : A′ ▹ A₁′ ⇒ A₂′} {cn′ : A₁′ ~ B′}
      --------------------------------------------------------------
    → Γ , Γ′ ⊢ (L · M at ℓ) {m} {cn} ⊑ᴳ (L′ · M′ at ℓ′) {m′} {cn′}

  ⊑ᴳ-if : ∀ {Γ Γ′ A₁ A₁′ A₂ A₂′ B B′} {L : Γ ⊢G B} {L′ : Γ′ ⊢G B′} {M : Γ ⊢G A₁} {M′ : Γ′ ⊢G A₁′} {N : Γ ⊢G A₂} {N′ : Γ′ ⊢G A₂′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ L ⊑ᴳ L′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → Γ , Γ′ ⊢ N ⊑ᴳ N′
    → {bb : B ~ ` 𝔹} {bb′ : B′ ~ ` 𝔹} {aa : A₁ ~ A₂} {aa′ : A₁′ ~ A₂′}
      ------------------------------------------------------------------
    → Γ , Γ′ ⊢ if L M N ℓ {bb} {aa} ⊑ᴳ if L′ M′ N′ ℓ′ {bb′} {aa′}

  ⊑ᴳ-cons : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢G A} {M′ : Γ′ ⊢G A′} {N : Γ ⊢G B} {N′ : Γ′ ⊢G B′}
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → Γ , Γ′ ⊢ N ⊑ᴳ N′
      --------------------------------
    → Γ , Γ′ ⊢ cons M N ⊑ᴳ cons M′ N′

  ⊑ᴳ-fst : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′} {M : Γ ⊢G A} {M′ : Γ′ ⊢G A′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → {m : A ▹ A₁ × A₂} {m′ : A′ ▹ A₁′ × A₂′}
      ------------------------------------------
    → Γ , Γ′ ⊢ fst M ℓ {m} ⊑ᴳ fst M′ ℓ′ {m′}

  ⊑ᴳ-snd : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′} {M : Γ ⊢G A} {M′ : Γ′ ⊢G A′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → {m : A ▹ A₁ × A₂} {m′ : A′ ▹ A₁′ × A₂′}
      ------------------------------------------
    → Γ , Γ′ ⊢ snd M ℓ {m} ⊑ᴳ snd M′ ℓ′ {m′}

  ⊑ᴳ-inl : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢G A} {M′ : Γ′ ⊢G A′}
    → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
      ------------------------------
    → Γ , Γ′ ⊢ inl B M ⊑ᴳ inl B′ M′

  ⊑ᴳ-inr : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢G B} {M′ : Γ′ ⊢G B′}
    → A ⊑ A′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
      ------------------------------
    → Γ , Γ′ ⊢ inr A M ⊑ᴳ inr A′ M′

  ⊑ᴳ-case : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′ B B′ B₁ B₁′ B₂ B₂′ C C′ C₁ C₁′ C₂ C₂′}
              {L : Γ ⊢G A} {L′ : Γ′ ⊢G A′} {M : Γ ⊢G B} {M′ : Γ′ ⊢G B′} {N : Γ ⊢G C} {N′ : Γ′ ⊢G C′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ L ⊑ᴳ L′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → Γ , Γ′ ⊢ N ⊑ᴳ N′
    → {ma : A ▹ A₁ ⊎ A₂} {ma′ : A′ ▹ A₁′ ⊎ A₂′} {mb : B ▹ B₁ ⇒ B₂} {mb′ : B′ ▹ B₁′ ⇒ B₂′} {mc : C ▹ C₁ ⇒ C₂} {mc′ : C′ ▹ C₁′ ⇒ C₂′}
    → {ab : A₁ ~ B₁} {ab′ : A₁′ ~ B₁′} {ac : A₂ ~ C₁} {ac′ : A₂′ ~ C₁′} {bc : B₂ ~ C₂} {bc′ : B₂′ ~ C₂′}
      ------------------------------------------------------------------------------------------------------------
    → Γ , Γ′ ⊢ case L M N ℓ {ma} {mb} {mc} {ab} {ac} {bc} ⊑ᴳ case L′ M′ N′ ℓ′ {ma′} {mb′} {mc′} {ab′} {ac′} {bc′}


-- Term precision of CC.
data _,_⊢_⊑ᶜ_ : ∀ (Γ Γ′ : Context) → {A A′ : Type} → Γ ⊢ A → Γ′ ⊢ A′ → Set where

  ⊑ᶜ-prim : ∀ {Γ Γ′ A} {k : rep A} {i : Prim A}
      ------------------------------
    → Γ , Γ′ ⊢ $_ {Γ} k {i} ⊑ᶜ $_ {Γ′} k {i}

  ⊑ᴳ-var : ∀ {Γ Γ′ A A′} {x : Γ ∋ A} {x′ : Γ′ ∋ A′}
    → ∋→ℕ x ≡ ∋→ℕ x′
      -----------------
    → Γ , Γ′ ⊢ ` x ⊑ᶜ ` x′

  ⊑ᶜ-ƛ : ∀ {Γ Γ′ A A′ B B′} {N : Γ , A ⊢ B} {N′ : Γ′ , A′ ⊢ B′}
    → A ⊑ A′
    → (Γ , A) , (Γ′ , A′) ⊢ N ⊑ᶜ N′
      ------------------------------
    → Γ , Γ′ ⊢ ƛ N ⊑ᶜ ƛ N′

  ⊑ᶜ-· : ∀ {Γ Γ′ A A′ B B′} {L : Γ ⊢ A ⇒ B} {L′ : Γ′ ⊢ A′ ⇒ B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      --------------------------
    → Γ , Γ′ ⊢ L · M ⊑ᶜ L′ · M′

  ⊑ᶜ-if : ∀ {Γ Γ′ A A′} {L : Γ ⊢ ` 𝔹} {L′ : Γ′ ⊢ ` 𝔹} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {N : Γ ⊢ A} {N′ : Γ′ ⊢ A′}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → Γ , Γ′ ⊢ N ⊑ᶜ N′
      ---------------------------------
    → Γ , Γ′ ⊢ if L M N ⊑ᶜ if L′ M′ N′

  ⊑ᶜ-cons : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {N : Γ ⊢ B} {N′ : Γ′ ⊢ B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → Γ , Γ′ ⊢ N ⊑ᶜ N′
      --------------------------------
    → Γ , Γ′ ⊢ cons M N ⊑ᶜ cons M′ N′

  ⊑ᶜ-fst : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A `× B} {M′ : Γ′ ⊢ A′ `× B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -------------------------
    → Γ , Γ′ ⊢ fst M ⊑ᶜ fst M′

  ⊑ᶜ-snd : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A `× B} {M′ : Γ′ ⊢ A′ `× B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -------------------------
    → Γ , Γ′ ⊢ snd M ⊑ᶜ snd M′

  ⊑ᶜ-inl : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inl {B = B} M ⊑ᶜ inl {B = B′} M′

  ⊑ᶜ-inr : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ B} {M′ : Γ′ ⊢ B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inr {A = A} M ⊑ᶜ inr {A = A′} M′

  ⊑ᶜ-case : ∀ {Γ Γ′ A A′ B B′ C C′} {L : Γ ⊢ A `⊎ B} {L′ : Γ′ ⊢ A′ `⊎ B′} {M : Γ ⊢ A ⇒ C} {M′ : Γ′ ⊢ A′ ⇒ C′} {N : Γ ⊢ B ⇒ C} {N′ : Γ′ ⊢ B′ ⇒ C′}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → Γ , Γ′ ⊢ N ⊑ᶜ N′
      -------------------------------------
    → Γ , Γ′ ⊢ case L M N ⊑ᶜ case L′ M′ N′

  ⊑ᶜ-cast : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → A ⊑ A′ → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------
    → Γ , Γ′ ⊢ M ⟨ c ⟩ ⊑ᶜ M′ ⟨ c′ ⟩

  ⊑ᶜ-castl : ∀ {Γ Γ′ A A′ B} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
    → A ⊑ A′ → B ⊑ A′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -----------------------
    → Γ , Γ′ ⊢ M ⟨ c ⟩ ⊑ᶜ M′

  ⊑ᶜ-castr : ∀ {Γ Γ′ A A′ B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {c′ : Cast (A′ ⇒ B′)}
    → A ⊑ A′ → A ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ M′ ⟨ c′ ⟩

  ⊑ᶜ-blame : ∀ {Γ Γ′ A A′} {M : Γ ⊢ A} {ℓ}
    → A ⊑ A′
      -------------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ blame {Γ′} {A′} ℓ


-- Similar to the example in Fig. 5, Refined Criteria.
_ : ∅ , ∅ ⊢ ((ƛ ⋆ ˙ (` Z)) · ($_ 42 {P-Base}) at pos 0) {match⇒⇒} {unk~L} ⊑ᴳ ((ƛ (` Nat) ˙ (` Z)) · ($_ 42 {P-Base}) at pos 0) {match⇒⇒} {base~}
_ = ⊑ᴳ-· (⊑ᴳ-ƛ unk⊑ (⊑ᴳ-var refl)) ⊑ᴳ-prim

_ : ∅ , ∅ ⊢ ƛ_ {B = ⋆} {⋆} (` Z) ⊑ᶜ ƛ_ {B = ` Nat} {` Nat} (` Z)
_ = ⊑ᶜ-ƛ unk⊑ (⊑ᴳ-var refl)
