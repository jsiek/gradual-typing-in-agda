open import Data.List
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

open import Types
open import Labels
open import PreCastStructureWithPrecisionABT

open import Syntax using (Var)


module ParamCCPrecisionABT (pcsp : PreCastStructWithPrecision) where

open PreCastStructWithPrecision pcsp

open import ParamCastCalculusABT precast

{- The precision relation for the cast calculus. -}
infix 6 _,_⊢_⊑ᶜ_
{- The precision relation for substitution. -}
-- infix 6 _,_,_,_⊢_⊑ˢ_

-- Term precision of CC.
data _,_⊢_⊑ᶜ_ : ∀ (Γ Γ′ : List Type) → (M M′ : Term) → Set where

  ⊑ᶜ-$ : ∀ {Γ Γ′ A} {r : rep A} {p : Prim A}
      --------------------------------------
    → Γ , Γ′ ⊢ $ r # p ⊑ᶜ $ r # p

  ⊑ᶜ-` : ∀ {Γ Γ′} {x : Var}
      ---------------------
    → Γ , Γ′ ⊢ ` x ⊑ᶜ ` x

  ⊑ᶜ-ƛ : ∀ {Γ Γ′ A A′} {N N′ : Term}
    → A ⊑ A′
    → (A ∷ Γ) , (A′ ∷ Γ′) ⊢ N ⊑ᶜ N′
      ------------------------------
    → Γ , Γ′ ⊢ ƛ A ˙ N ⊑ᶜ ƛ A′ ˙ N′

  ⊑ᶜ-· : ∀ {Γ Γ′} {L L′ M M′ : Term}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      --------------------------
    → Γ , Γ′ ⊢ L · M ⊑ᶜ L′ · M′

  ⊑ᶜ-if : ∀ {Γ Γ′} {L L′ M M′ N N′ : Term}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → Γ , Γ′ ⊢ N ⊑ᶜ N′
      ----------------------------------------
    → Γ , Γ′ ⊢ if L  then M  else N  endif ⊑ᶜ
                if L′ then M′ else N′ endif

  ⊑ᶜ-cons : ∀ {Γ Γ′} {M M′ N N′ : Term}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → Γ , Γ′ ⊢ N ⊑ᶜ N′
      ----------------------------------
    → Γ , Γ′ ⊢ ⟦ M , N ⟧ ⊑ᶜ ⟦ M′ , N′ ⟧

  ⊑ᶜ-fst : ∀ {Γ Γ′} {M M′ : Term}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -------------------------
    → Γ , Γ′ ⊢ fst M ⊑ᶜ fst M′

  ⊑ᶜ-snd : ∀ {Γ Γ′} {M M′ : Term}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -------------------------
    → Γ , Γ′ ⊢ snd M ⊑ᶜ snd M′

  ⊑ᶜ-inl : ∀ {Γ Γ′ B B′} {M M′ : Term}
    → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inl M other B ⊑ᶜ inl M′ other B′

  ⊑ᶜ-inr : ∀ {Γ Γ′ A A′} {M M′ : Term}
    → A ⊑ A′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inr M other A ⊑ᶜ inr M′ other A′

  ⊑ᶜ-case : ∀ {Γ Γ′ A A′ B B′} {L L′ M M′ N N′ : Term}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → A ⊑ A′
    → B ⊑ B′
    → (A ∷ Γ) , (A′ ∷ Γ′) ⊢ M ⊑ᶜ M′
    → (B ∷ Γ) , (B′ ∷ Γ′) ⊢ N ⊑ᶜ N′
      ------------------------------------------
    → Γ , Γ′ ⊢ case L  of A  ⇒ M  ∣ B  ⇒ N ⊑ᶜ
                case L′ of A′ ⇒ M′ ∣ B′ ⇒ N′

  ⊑ᶜ-cast : ∀ {Γ Γ′ A A′ B B′} {M M′ : Term}
              {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → A ⊑ A′
    → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------
    → Γ , Γ′ ⊢ M ⟨ c ⟩ ⊑ᶜ M′ ⟨ c′ ⟩

  ⊑ᶜ-castl : ∀ {Γ Γ′ A A′ B} {M M′ : Term}
               {c : Cast (A ⇒ B)}
    → A ⊑ A′
    → B ⊑ A′
    → Γ′     ⊢ M′ ⦂ A′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -----------------------
    → Γ , Γ′ ⊢ M ⟨ c ⟩ ⊑ᶜ M′

  ⊑ᶜ-castr : ∀ {Γ Γ′ A A′ B′} {M M′ : Term}
               {c′ : Cast (A′ ⇒ B′)}
    → A ⊑ A′
    → A ⊑ B′
    → Γ      ⊢ M ⦂ A
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ M′ ⟨ c′ ⟩

  ⊑ᶜ-wrap : ∀ {Γ Γ′ A A′ B B′} {M M′ : Term}
              {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
              {i : Inert c} {i′ : Inert c′}
    → c ₍ i ₎⊑ c′ ₍ i′ ₎
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → (B ≡ ⋆ → B′ ≡ ⋆)  -- note the side condition
      -----------------------------------------
    → Γ , Γ′ ⊢ M ⟨ c ₍ i ₎⟩ ⊑ᶜ M′ ⟨ c′ ₍ i′ ₎⟩

  ⊑ᶜ-wrapl : ∀ {Γ Γ′ A A′ B} {M M′ : Term}
               {c : Cast (A ⇒ B)} {i : Inert c}
    → c ₍ i ₎⊑ A′
    → Γ′     ⊢ M′ ⦂ A′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -----------------------
    → Γ , Γ′ ⊢ M ⟨ c ₍ i ₎⟩ ⊑ᶜ M′

  ⊑ᶜ-wrapr : ∀ {Γ Γ′ A A′ B′} {M M′ : Term}
               {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
    → A ⊑ c′ ₍ i′ ₎
    → Γ ⊢ M ⦂ A
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → A ≢ ⋆             -- note the side condition
      ------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ M′ ⟨ c′ ₍ i′ ₎⟩

  ⊑ᶜ-blame : ∀ {Γ Γ′} {M : Term} {ℓ}
      -------------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ blame ℓ

-- data _,_,_,_⊢_⊑ˢ_ : (Γ Δ Γ′ Δ′ : Context) → Subst Γ Δ → Subst Γ′ Δ′ → Set where

--   ⊑ˢ-σ₀ : ∀ {Δ Δ′ A A′} {M : Δ ⊢ A} {M′ : Δ′ ⊢ A′}
--     → Δ , Δ′ ⊢ M ⊑ᶜ M′
--       ------------------------------------------
--     → (Δ , A) , Δ , (Δ′ , A′) , Δ′ ⊢ (subst-zero M) ⊑ˢ (subst-zero M′)

--   ⊑ˢ-exts : ∀ {Γ Γ′ Δ Δ′ B B′} {σ : Subst Γ Δ} {σ′ : Subst Γ′ Δ′}
--     → Γ , Δ , Γ′ , Δ′ ⊢ σ ⊑ˢ σ′
--       -------------------------------------------------------------------
--     → (Γ ,  B) , (Δ , B) , (Γ′ , B′) , (Δ′ , B′) ⊢ (exts σ) ⊑ˢ (exts σ′)

-- -- Example(s):
-- _ : ∅ , ∅ ⊢ ƛ_ {B = ⋆} {⋆} (` Z) ⊑ᶜ ƛ_ {B = ` Nat} {` Nat} (` Z)
-- _ = ⊑ᶜ-ƛ unk⊑ (⊑ᶜ-var refl)
