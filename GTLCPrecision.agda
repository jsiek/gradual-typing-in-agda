open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Types
open import Variables
open import Labels

open import GTLC



module GTLCPrecision where

infix 6 _⊑ᴳ_


-- Term precision for GTLC - M₁ ⊑ᴳ M₂ means that M₂ is *more precise* than M₁ .
data _⊑ᴳ_ : ∀ (M M′ : Term) → Set where

  ⊑ᴳ-prim : ∀ {A} {r : rep A} {p : Prim A}
      ------------------------------
    → $ r # p ⊑ᴳ $ r # p

  ⊑ᴳ-var : ∀ {x : ℕ}
      -----------------
    → ` x ⊑ᴳ ` x

  ⊑ᴳ-ƛ : ∀ {A A′} {N N′ : Term}
    → A ⊑ A′
    → N ⊑ᴳ N′
      ---------------------
    → ƛ A ˙ N ⊑ᴳ ƛ A′ ˙ N′

  ⊑ᴳ-· : ∀ {L L′ M M′} {ℓ ℓ′}
    → L ⊑ᴳ L′
    → M ⊑ᴳ M′
      ----------------------------
    → L · M at ℓ ⊑ᴳ L′ · M′ at ℓ′

  ⊑ᴳ-if : ∀ {L L′ M M′ N N′} {ℓ ℓ′}
    → L ⊑ᴳ L′
    → M ⊑ᴳ M′
    → N ⊑ᴳ N′
      -------------------------------------------------------
    → if L then M else N at ℓ ⊑ᴳ if L′ then M′ else N′ at ℓ′

  ⊑ᴳ-cons : ∀ {M M′ N N′}
    → M ⊑ᴳ M′
    → N ⊑ᴳ N′
      --------------------------
    → ⟦ M , N ⟧ ⊑ᴳ ⟦ M′ , N′ ⟧

  ⊑ᴳ-fst : ∀ {M M′} {ℓ ℓ′}
    → M ⊑ᴳ M′
      ---------------------------
    → fst M at ℓ ⊑ᴳ fst M′ at ℓ′

  ⊑ᴳ-snd : ∀ {M M′} {ℓ ℓ′}
    → M ⊑ᴳ M′
      ---------------------------
    → snd M at ℓ ⊑ᴳ snd M′ at ℓ′

  ⊑ᴳ-inl : ∀ {B B′} {M M′}
    → B ⊑ B′
    → M ⊑ᴳ M′
      ------------------------------
    → inl M other B ⊑ᴳ inl M′ other B′

  ⊑ᴳ-inr : ∀ {A A′} {M M′}
    → A ⊑ A′
    → M ⊑ᴳ M′
      ------------------------------
    → inr M other A ⊑ᴳ inr M′ other A′

  ⊑ᴳ-case : ∀ {B₁ B₁′ C₁ C₁′} {L L′ M M′ N N′} {ℓ ℓ′}
    → L ⊑ᴳ L′
    → B₁ ⊑ B₁′ → C₁ ⊑ C₁′
    → M ⊑ᴳ M′
    → N ⊑ᴳ N′
      ----------------------------------------------------------------------------
    → case L of B₁ ⇒ M ∣ C₁ ⇒ N at ℓ ⊑ᴳ case L′ of B₁′ ⇒ M′ ∣ C₁′ ⇒ N′ at ℓ′

{- Example(s):
   Similar to the example in Fig. 5, Refined Criteria. -}
_ : (ƛ ⋆ ˙ (` 0)) · ($ 42 # P-Base) at pos 0 ⊑ᴳ (ƛ (` Nat) ˙ (` 0)) · ($ 42 # P-Base) at pos 0
_ = ⊑ᴳ-· (⊑ᴳ-ƛ unk⊑ ⊑ᴳ-var) ⊑ᴳ-prim
