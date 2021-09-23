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
infix 6 _,_⊢_⊑_

data _,_⊢_⊑_ : ∀ (Γ Γ′ : List Type) → (M M′ : Term) → Set where

  ⊑-$ : ∀ {Γ Γ′ A} {r : rep A} {p : Prim A}
      --------------------------------------
    → Γ , Γ′ ⊢ $ r # p ⊑ $ r # p

  ⊑-` : ∀ {Γ Γ′} {x : Var}
      ---------------------
    → Γ , Γ′ ⊢ ` x ⊑ ` x

  ⊑-ƛ : ∀ {Γ Γ′ A A′} {N N′ : Term}
    → A ⊑ A′
    → (A ∷ Γ) , (A′ ∷ Γ′) ⊢ N ⊑ N′
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
    → (A ∷ Γ) , (A′ ∷ Γ′) ⊢ M ⊑ M′
    → (B ∷ Γ) , (B′ ∷ Γ′) ⊢ N ⊑ N′
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
              {i : Inert c} {i′ : Inert c′}
    → c ₍ i ₎⊑ c′ ₍ i′ ₎
    → Γ , Γ′ ⊢ M ⊑ M′
    → (B ≡ ⋆ → B′ ≡ ⋆)  -- note the side condition
      -----------------------------------------
    → Γ , Γ′ ⊢ M ⟨ c ₍ i ₎⟩ ⊑ M′ ⟨ c′ ₍ i′ ₎⟩

  ⊑-wrapl : ∀ {Γ Γ′ A A′ B} {M M′ : Term}
               {c : Cast (A ⇒ B)} {i : Inert c}
    → c ₍ i ₎⊑ A′
    → Γ′     ⊢ M′ ⦂ A′
    → Γ , Γ′ ⊢ M ⊑ M′
      -----------------------
    → Γ , Γ′ ⊢ M ⟨ c ₍ i ₎⟩ ⊑ M′

  ⊑-wrapr : ∀ {Γ Γ′ A A′ B′} {M M′ : Term}
               {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
    → A ⊑ c′ ₍ i′ ₎
    → Γ ⊢ M ⦂ A
    → Γ , Γ′ ⊢ M ⊑ M′
    → A ≢ ⋆             -- note the side condition
      ------------------------
    → Γ , Γ′ ⊢ M ⊑ M′ ⟨ c′ ₍ i′ ₎⟩

  ⊑-blame : ∀ {Γ Γ′} {M : Term} {ℓ}
      -------------------------------
    → Γ , Γ′ ⊢ M ⊑ blame ℓ

-- Example(s):
private
  _ : [] , [] ⊢ ƛ ⋆ ˙ (` 0) ⊑ ƛ (` Nat) ˙ (` 0)
  _ = ⊑-ƛ unk⊑ ⊑-`

-- data _,_,_,_⊢_⊑ˢ_ : (Γ Δ Γ′ Δ′ : Context) → Subst Γ Δ → Subst Γ′ Δ′ → Set where

--   ⊑ˢ-σ₀ : ∀ {Δ Δ′ A A′} {M : Δ ⊢ A} {M′ : Δ′ ⊢ A′}
--     → Δ , Δ′ ⊢ M ⊑ M′
--       ------------------------------------------
--     → (Δ , A) , Δ , (Δ′ , A′) , Δ′ ⊢ (subst-zero M) ⊑ˢ (subst-zero M′)

--   ⊑ˢ-exts : ∀ {Γ Γ′ Δ Δ′ B B′} {σ : Subst Γ Δ} {σ′ : Subst Γ′ Δ′}
--     → Γ , Δ , Γ′ , Δ′ ⊢ σ ⊑ˢ σ′
--       -------------------------------------------------------------------
--     → (Γ ,  B) , (Δ , B) , (Γ′ , B′) , (Δ′ , B′) ⊢ (exts σ) ⊑ˢ (exts σ′)

infix 6 _⊑ˢ_

_⊑ˢ_ : Subst → Subst → Set
σ ⊑ˢ σ′ = ∀ {Δ Δ′} → ∀ (x : Var) → Δ , Δ′ ⊢ σ x ⊑ σ′ x

open import MapPreserve Op sig Type 𝑉⊢ 𝑃⊢
  using (MapPreservable; _⦂_⇒_)

private
  instance
    _ : MapPreservable Term
    _ = record {
          _⊢v_⦂_ = _⊢_⦂_ ;
          ⊢v-var→val0 = ⊢` refl ;
          shift-⊢v = λ ⊢M → preserve-rename _ ⊢M λ ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩ ;
          quote-⊢v = λ ⊢v → ⊢v ;
          𝑉-⊢v = λ { refl ⊢M → ⊢M }
        }

subst-pres-⊑ : ∀ {Γ Δ Γ′ Δ′ : List Type} {M M′ : Term} {σ σ′}
  → σ ⊑ˢ σ′
  → σ ⦂ Γ ⇒ Δ → σ′ ⦂ Γ′ ⇒ Δ′
  → Γ , Γ′ ⊢ M ⊑ M′
    -----------------------------
  → Δ , Δ′ ⊢ ⟪ σ ⟫ M ⊑ ⟪ σ′ ⟫ M′
subst-pres-⊑ lps ⊢σ ⊢σ′ ⊑-$ = ⊑-$
subst-pres-⊑ lps ⊢σ ⊢σ′ ⊑-` = lps _
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-ƛ x lpM) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-· lpM lpM₁) = ⊑-· {!!} {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-if lpM lpM₁ lpM₂) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-cons lpM lpM₁) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-fst lpM) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-snd lpM) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-inl lp lpM) =
  ⊑-inl lp (subst-pres-⊑ lps ⊢σ ⊢σ′ lpM)
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-inr x lpM) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-case lpM x x₁ lpM₁ lpM₂) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-cast x x₁ lpM) = {!!}
subst-pres-⊑ σ⊑ ⊢σ ⊢σ′ (⊑-castl lpA lpB ⊢M′ M⊑) =
  ⊑-castl lpA lpB (preserve-subst _ ⊢M′ ⊢σ′) (subst-pres-⊑ σ⊑ ⊢σ ⊢σ′ M⊑)
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-castr x x₁ x₂ lpM) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-wrap x lpM x₁) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-wrapl x x₁ lpM) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ (⊑-wrapr x x₁ lpM x₂) = {!!}
subst-pres-⊑ lps ⊢σ ⊢σ′ ⊑-blame = {!!}
