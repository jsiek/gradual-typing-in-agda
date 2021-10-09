open import Data.List
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

open import Types
open import Labels
open import PreCastStructure

open import Syntax


module ParamCCPrecisionABT (precast : PreCastStruct) where

open PreCastStruct precast

open import ParamCastCalculusABT precast

{- The precision relation for the cast calculus. -}
infix 4 _,_⊢_⊑_

data _,_⊢_⊑_ : ∀ (Γ Γ′ : List Type) → (M M′ : Term) → Set where

  ⊑-$ : ∀ {Γ Γ′ A} {r : rep A} {p : Prim A}
      --------------------------------------
    → Γ , Γ′ ⊢ $ r # p ⊑ $ r # p

  ⊑-` : ∀ {Γ Γ′} {x : Var}
      ---------------------
    → Γ , Γ′ ⊢ ` x ⊑ ` x

  ⊑-ƛ : ∀ {Γ Γ′ A A′} {N N′ : Term}
    → A ⊑ A′
    → A ∷ Γ , A′ ∷ Γ′ ⊢ N ⊑ N′
      ------------------------------
    → Γ , Γ′ ⊢ ƛ A ˙ N ⊑ ƛ A′ ˙ N′

  ⊑-· : ∀ {Γ Γ′} {L L′ M M′ : Term}
    → Γ , Γ′ ⊢ L ⊑ L′
    → Γ , Γ′ ⊢ M ⊑ M′
      --------------------------
    → Γ , Γ′ ⊢ L · M ⊑ L′ · M′

  ⊑-if : ∀ {Γ Γ′} {L L′ M M′ N N′ : Term}
    → Γ , Γ′ ⊢ L ⊑ L′
    → Γ , Γ′ ⊢ M ⊑ M′
    → Γ , Γ′ ⊢ N ⊑ N′
      ----------------------------------------
    → Γ , Γ′ ⊢ if L  then M  else N  endif ⊑
                if L′ then M′ else N′ endif

  ⊑-cons : ∀ {Γ Γ′} {M M′ N N′ : Term}
    → Γ , Γ′ ⊢ M ⊑ M′
    → Γ , Γ′ ⊢ N ⊑ N′
      ----------------------------------
    → Γ , Γ′ ⊢ ⟦ M , N ⟧ ⊑ ⟦ M′ , N′ ⟧

  ⊑-fst : ∀ {Γ Γ′} {M M′ : Term}
    → Γ , Γ′ ⊢ M ⊑ M′
      -------------------------
    → Γ , Γ′ ⊢ fst M ⊑ fst M′

  ⊑-snd : ∀ {Γ Γ′} {M M′ : Term}
    → Γ , Γ′ ⊢ M ⊑ M′
      -------------------------
    → Γ , Γ′ ⊢ snd M ⊑ snd M′

  ⊑-inl : ∀ {Γ Γ′ B B′} {M M′ : Term}
    → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inl M other B ⊑ inl M′ other B′

  ⊑-inr : ∀ {Γ Γ′ A A′} {M M′ : Term}
    → A ⊑ A′
    → Γ , Γ′ ⊢ M ⊑ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inr M other A ⊑ inr M′ other A′

  ⊑-case : ∀ {Γ Γ′ A A′ B B′} {L L′ M M′ N N′ : Term}
    → Γ , Γ′ ⊢ L ⊑ L′
    → A ⊑ A′
    → B ⊑ B′
    → A ∷ Γ , A′ ∷ Γ′ ⊢ M ⊑ M′
    → B ∷ Γ , B′ ∷ Γ′ ⊢ N ⊑ N′
      ------------------------------------------
    → Γ , Γ′ ⊢ case L  of A  ⇒ M  ∣ B  ⇒ N ⊑
                case L′ of A′ ⇒ M′ ∣ B′ ⇒ N′

  ⊑-cast : ∀ {Γ Γ′ A A′ B B′} {M M′ : Term}
             {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → A ⊑ A′
    → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ M′
      ------------------------------
    → Γ , Γ′ ⊢ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩

  ⊑-castl : ∀ {Γ Γ′ A A′ B} {M M′ : Term}
              {c : Cast (A ⇒ B)}
    → A ⊑ A′
    → B ⊑ A′
    → Γ′     ⊢ M′ ⦂ A′
    → Γ , Γ′ ⊢ M ⊑ M′
      -----------------------
    → Γ , Γ′ ⊢ M ⟨ c ⟩ ⊑ M′

  ⊑-castr : ∀ {Γ Γ′ A A′ B′} {M M′ : Term}
              {c′ : Cast (A′ ⇒ B′)}
    → A ⊑ A′
    → A ⊑ B′
    → Γ      ⊢ M ⦂ A
    → Γ , Γ′ ⊢ M ⊑ M′
      ------------------------
    → Γ , Γ′ ⊢ M ⊑ M′ ⟨ c′ ⟩

  ⊑-wrap : ∀ {Γ Γ′ A A′ B B′} {M M′ : Term}
             {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
             {i : Inert c}       {i′ : Inert c′}
    → A ⊑ A′
    → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ M′
    -- → (B ≡ ⋆ → B′ ≡ ⋆)
      -----------------------------------------
    → Γ , Γ′ ⊢ M ⟨ c ₍ i ₎⟩ ⊑ M′ ⟨ c′ ₍ i′ ₎⟩

  ⊑-wrapl : ∀ {Γ Γ′ A A′ B} {M M′ : Term}
              {c : Cast (A ⇒ B)} {i : Inert c}
    → A ⊑ A′
    → B ⊑ A′
    → Γ′     ⊢ M′ ⦂ A′
    → Γ , Γ′ ⊢ M ⊑ M′
      ---------------------------
    → Γ , Γ′ ⊢ M ⟨ c ₍ i ₎⟩ ⊑ M′

  ⊑-wrapr : ∀ {Γ Γ′ A A′ B′} {M M′ : Term}
              {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
    → A ⊑ A′
    → A ⊑ B′
    → Γ      ⊢ M ⦂ A
    → Γ , Γ′ ⊢ M ⊑ M′
    -- → A ≢ ⋆
      -----------------------------
    → Γ , Γ′ ⊢ M ⊑ M′ ⟨ c′ ₍ i′ ₎⟩

  ⊑-blame : ∀ {Γ Γ′ A A′} {M : Term} {ℓ}
    → Γ ⊢ M ⦂ A
    → A ⊑ A′
      -------------------------------
    → Γ , Γ′ ⊢ M ⊑ blame A′ ℓ

-- Example(s):
private
  _ : [] , [] ⊢ ƛ ⋆ ˙ (` 0) ⊑ ƛ (` Nat) ˙ (` 0)
  _ = ⊑-ƛ unk⊑ ⊑-`
