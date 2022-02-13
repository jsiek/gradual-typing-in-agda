open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Types
open import Variables
open import Labels
open import PreCastStructureWithPrecision



module ParamCCPrecision (pcsp : PreCastStructWithPrecision) where

open PreCastStructWithPrecision pcsp

open import ParamCastCalculus Cast Inert

{- The precision relation for the cast calculus. -}
infix 6 _,_⊢_⊑ᶜ_
{- The precision relation for substitution. -}
infix 6 _,_,_,_⊢_⊑ˢ_

-- Term precision of CC.
data _,_⊢_⊑ᶜ_ : ∀ (Γ Γ′ : Context) → {A A′ : Type} → Γ ⊢ A → Γ′ ⊢ A′ → Set where

  ⊑ᶜ-prim : ∀ {Γ Γ′ A} {k : rep A} {i : Prim A}
      ------------------------------
    → Γ , Γ′ ⊢ $_ {Γ} k {i} ⊑ᶜ $_ {Γ′} k {i}

  ⊑ᶜ-var : ∀ {Γ Γ′ A A′} {x : Γ ∋ A} {x′ : Γ′ ∋ A′}
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
    → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inl {B = B} M ⊑ᶜ inl {B = B′} M′

  ⊑ᶜ-inr : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ B} {M′ : Γ′ ⊢ B′}
    → A ⊑ A′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inr {A = A} M ⊑ᶜ inr {A = A′} M′

  ⊑ᶜ-case : ∀ {Γ Γ′ A A′ B B′ C C′} {L : Γ ⊢ A `⊎ B} {L′ : Γ′ ⊢ A′ `⊎ B′} {M : Γ , A ⊢ C} {M′ : Γ′ , A′ ⊢ C′} {N : Γ , B ⊢ C} {N′ : Γ′ , B′ ⊢ C′}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → A ⊑ A′ → B ⊑ B′
    → (Γ , A) , (Γ′ , A′) ⊢ M ⊑ᶜ M′
    → (Γ , B) , (Γ′ , B′) ⊢ N ⊑ᶜ N′
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

  {- The cases below are for wrapped inert casts. -}
  ⊑ᶜ-wrap : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
              {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
              {i : Inert c} {i′ : Inert c′}
    → ⟪ i ⟫⊑⟪ i′ ⟫
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → (B ≡ ⋆ → B′ ≡ ⋆)
      ------------------------------
    → Γ , Γ′ ⊢ M ⟪ i ⟫ ⊑ᶜ M′ ⟪ i′ ⟫

  ⊑ᶜ-wrapl : ∀ {Γ Γ′ A A′ B} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
               {c : Cast (A ⇒ B)} {i : Inert c}
    → ⟪ i ⟫⊑ A′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    -- NOTE: Not sure if we need to require Value M′ here.
      -----------------------
    → Γ , Γ′ ⊢ M ⟪ i ⟫ ⊑ᶜ M′

  ⊑ᶜ-wrapr : ∀ {Γ Γ′ A A′ B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
               {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
    → A ⊑⟪ i′ ⟫
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → A ≢ ⋆
      ------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ M′ ⟪ i′ ⟫

  ⊑ᶜ-blame : ∀ {Γ Γ′ A A′} {M : Γ ⊢ A} {ℓ}
    → A ⊑ A′
      -------------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ blame {Γ′} {A′} ℓ

data _,_,_,_⊢_⊑ˢ_ : (Γ Δ Γ′ Δ′ : Context) → Subst Γ Δ → Subst Γ′ Δ′ → Set where

  ⊑ˢ-σ₀ : ∀ {Δ Δ′ A A′} {M : Δ ⊢ A} {M′ : Δ′ ⊢ A′}
    → Δ , Δ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → (Δ , A) , Δ , (Δ′ , A′) , Δ′ ⊢ (subst-zero M) ⊑ˢ (subst-zero M′)

  ⊑ˢ-exts : ∀ {Γ Γ′ Δ Δ′ B B′} {σ : Subst Γ Δ} {σ′ : Subst Γ′ Δ′}
    → Γ , Δ , Γ′ , Δ′ ⊢ σ ⊑ˢ σ′
      -------------------------------------------------------------------
    → (Γ ,  B) , (Δ , B) , (Γ′ , B′) , (Δ′ , B′) ⊢ (exts σ) ⊑ˢ (exts σ′)

-- Example(s):
_ : ∅ , ∅ ⊢ ƛ_ {B = ⋆} {⋆} (` Z) ⊑ᶜ ƛ_ {B = ` Nat} {` Nat} (` Z)
_ = ⊑ᶜ-ƛ unk⊑ (⊑ᶜ-var refl)
