open import Data.Nat
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

open import Syntax


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


open import MapPreserve Op sig Type 𝑉⊢ 𝑃⊢
  using (MapPreservable; _⦂_⇒_; ext-pres)

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
  _⊢v_⦂_ : List Type → Var → Type → Set
  Γ ⊢v x ⦂ B = ∃[ A ] Γ ∋ x ⦂ A × 𝑉⊢ Γ x A B
  instance
    _ : MapPreservable Var
    _ = record {
        _⊢v_⦂_ = _⊢v_⦂_ ;
        ⊢v-var→val0 = λ {A} → ⟨ A , ⟨ refl , refl ⟩ ⟩ ;
        shift-⊢v = λ { ⟨ A , ⟨ ∋x , Vx ⟩ ⟩ → ⟨ A , ⟨ ∋x , Vx ⟩ ⟩ } ;
        quote-⊢v = λ { ⟨ B , ⟨ ∋x , Vx ⟩ ⟩ → var-p ∋x Vx } ;
        𝑉-⊢v = λ { refl ⟨ C , ⟨ ∋x , Vx' ⟩ ⟩ → ⟨ C , ⟨ ∋x , Vx' ⟩ ⟩ }
      }

infix 6 _⇒_,_⇒_⊢_⊑ˢ_

_⇒_,_⇒_⊢_⊑ˢ_ : ∀ (Γ Δ Γ′ Δ′ : List Type) →  Subst → Subst → Set
Γ ⇒ Δ , Γ′ ⇒ Δ′ ⊢ σ ⊑ˢ σ′ =
  (σ ⦂ Γ ⇒ Δ) → (σ′ ⦂ Γ′ ⇒ Δ′) →
  ∀ (x : Var)
  → ∃[ A ] Γ ∋ x ⦂ A
  → ∃[ A′ ] Γ′ ∋ x ⦂ A′
  → Δ , Δ′ ⊢ σ x ⊑ σ′ x

rename-pres-⊑ : ∀ {Γ Γ′ Δ Δ′} {M M′ : Term} {ρ : Rename}
  → ρ ⦂ Γ ⇒ Δ → ρ ⦂ Γ′ ⇒ Δ′
  → Γ , Γ′ ⊢ M ⊑ M′
    ----------------------------------
  → Δ , Δ′ ⊢ rename ρ M ⊑ rename ρ M′
rename-pres-⊑ ⊢ρ ⊢ρ′ ⊑-$ = ⊑-$
rename-pres-⊑ ⊢ρ ⊢ρ′ ⊑-` = ⊑-`
rename-pres-⊑ {ρ = ρ} ⊢ρ ⊢ρ′ (⊑-ƛ A⊑ M⊑) =
  ⊑-ƛ A⊑ (rename-pres-⊑ {ρ = ext ρ}
                        (λ {x} ∋x → ext-pres ⊢ρ  {x} ∋x)
                        (λ {x} ∋x → ext-pres ⊢ρ′ {x} ∋x) M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-· L⊑ M⊑) =
  ⊑-· (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-if L⊑ M⊑ N⊑) =
  ⊑-if (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑) (rename-pres-⊑ ⊢ρ ⊢ρ′ N⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-cons M⊑ N⊑) =
  ⊑-cons (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑) (rename-pres-⊑ ⊢ρ ⊢ρ′ N⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-fst M⊑) =
  ⊑-fst (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-snd M⊑) =
  ⊑-snd (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-inl B⊑ M⊑) =
  ⊑-inl B⊑ (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-inr A⊑ M⊑) =
  ⊑-inr A⊑ (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ {ρ = ρ} ⊢ρ ⊢ρ′ (⊑-case L⊑ A⊑ B⊑ M⊑ N⊑) =
  ⊑-case (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑) A⊑ B⊑
    (rename-pres-⊑ {ρ = ext ρ}
      (λ {x} ∋x → ext-pres ⊢ρ  {x} ∋x)
      (λ {x} ∋x → ext-pres ⊢ρ′ {x} ∋x) M⊑)
    (rename-pres-⊑ {ρ = ext ρ}
      (λ {x} ∋x → ext-pres ⊢ρ  {x} ∋x)
      (λ {x} ∋x → ext-pres ⊢ρ′ {x} ∋x) N⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-cast A⊑ B⊑ M⊑) =
  ⊑-cast A⊑ B⊑ (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-castl A⊑A′ B⊑A′ ⊢M′ M⊑) =
  ⊑-castl A⊑A′ B⊑A′ (preserve-rename _ ⊢M′ ⊢ρ′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-castr A⊑A′ A⊑B′ ⊢M M⊑) =
  ⊑-castr A⊑A′ A⊑B′ (preserve-rename _ ⊢M ⊢ρ) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-wrap lpii M⊑ dd) =
  ⊑-wrap lpii (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑) dd
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-wrapl lpit ⊢M′ M⊑) =
  ⊑-wrapl lpit (preserve-rename _ ⊢M′ ⊢ρ′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-wrapr lpti ⊢M M⊑ nd) =
  ⊑-wrapr lpti (preserve-rename _ ⊢M ⊢ρ) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑) nd
rename-pres-⊑ _ _ ⊑-blame = ⊑-blame

ext-pres-⊑ˢ : ∀ {Γ Γ′ Δ Δ′} {A A′} {σ σ′ : Subst}
  → σ ⦂ Γ ⇒ Δ → σ′ ⦂ Γ′ ⇒ Δ′
  → Γ ⇒ Δ , Γ′ ⇒ Δ′ ⊢ σ ⊑ˢ σ′
  → (A ∷ Γ) ⇒ (A ∷ Δ) , (A′ ∷ Γ′) ⇒ (A′ ∷ Δ′) ⊢ ext σ ⊑ˢ ext σ′
ext-pres-⊑ˢ ⊢σ ⊢σ′ σ⊑ ⊢extσ ⊢extσ′ 0 ⟨ X , x⦂X ⟩ ⟨ X′ , x⦂X′ ⟩ = ⊑-`
ext-pres-⊑ˢ {σ = σ} ⊢σ ⊢σ′ σ⊑ ⊢extσ ⊢extσ′ (suc x) lookup-x lookup-x′
  rewrite exts-suc' σ x =
  -- rename ⇑ (σ x) ⊑ rename ⇑ (σ′ x)
  rename-pres-⊑ (λ ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩)  {- ⇑ ⦂ Γ ⇒ A ∷ Γ -}
                (λ ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩)
                (σ⊑ ⊢σ ⊢σ′ x lookup-x lookup-x′)

subst-pres-⊑ : ∀ {Γ Γ′ Δ Δ′} {A A′} {M M′ : Term} {σ σ′}
  → σ ⦂ Γ ⇒ Δ → σ′ ⦂ Γ′ ⇒ Δ′
  → Γ ⊢ M ⦂ A → Γ′ ⊢ M′ ⦂ A′
  → Γ ⇒ Δ , Γ′ ⇒ Δ′ ⊢ σ ⊑ˢ σ′
  → Γ , Γ′ ⊢ M ⊑ M′
    -----------------------------
  → Δ , Δ′ ⊢ ⟪ σ ⟫ M ⊑ ⟪ σ′ ⟫ M′
subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ ⊑-$ = ⊑-$
subst-pres-⊑ {M = ` x} {` x} ⊢σ ⊢σ′ (⊢` Γ∋x⦂A) (⊢` Γ′∋x⦂A′) σ⊑ ⊑-` =
    σ⊑ ⊢σ ⊢σ′ x ⟨ _ , Γ∋x⦂A ⟩ ⟨ _ , Γ′∋x⦂A′ ⟩
subst-pres-⊑ ⊢σ ⊢σ′ (⊢ƛ _ ⊢N 𝐶⊢-ƛ) (⊢ƛ _ ⊢N′ 𝐶⊢-ƛ) σ⊑ (⊑-ƛ A⊑ N⊑) =
  ⊑-ƛ A⊑ (subst-pres-⊑
    (λ {x} ∋x → ext-pres ⊢σ  {x} ∋x) {- ext σ ⦂ A ∷ Γ ⇒ A ∷ Δ -}
    (λ {x} ∋x → ext-pres ⊢σ′ {x} ∋x) ⊢N ⊢N′ (ext-pres-⊑ˢ ⊢σ ⊢σ′ σ⊑) N⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· ⊢L′ ⊢M′ 𝐶⊢-·) σ⊑ (⊑-· L⊑ M⊑) =
  ⊑-· (subst-pres-⊑ ⊢σ ⊢σ′ ⊢L ⊢L′ σ⊑ L⊑)
      (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢if ⊢L ⊢M ⊢N 𝐶⊢-if) (⊢if ⊢L′ ⊢M′ ⊢N′ 𝐶⊢-if) σ⊑ (⊑-if L⊑ M⊑ N⊑) =
  ⊑-if (subst-pres-⊑ ⊢σ ⊢σ′ ⊢L ⊢L′ σ⊑ L⊑)
       (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
       (subst-pres-⊑ ⊢σ ⊢σ′ ⊢N ⊢N′ σ⊑ N⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢cons ⊢M ⊢N 𝐶⊢-cons) (⊢cons ⊢M′ ⊢N′ 𝐶⊢-cons) σ⊑ (⊑-cons M⊑ N⊑) =
  ⊑-cons (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
         (subst-pres-⊑ ⊢σ ⊢σ′ ⊢N ⊢N′ σ⊑ N⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢fst ⊢M 𝐶⊢-fst) (⊢fst ⊢M′ 𝐶⊢-fst) σ⊑ (⊑-fst M⊑) =
  ⊑-fst (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢snd ⊢M 𝐶⊢-snd) (⊢snd ⊢M′ 𝐶⊢-snd) σ⊑ (⊑-snd M⊑) =
  ⊑-snd (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢inl _ ⊢M 𝐶⊢-inl) (⊢inl _ ⊢M′ 𝐶⊢-inl) σ⊑ (⊑-inl B⊑B′ M⊑) =
  ⊑-inl B⊑B′ (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢inr _ ⊢M 𝐶⊢-inr) (⊢inr _ ⊢M′ 𝐶⊢-inr) σ⊑ (⊑-inr A⊑A′ M⊑) =
  ⊑-inr A⊑A′ (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢case _ _ ⊢L ⊢M ⊢N 𝐶⊢-case)
                    (⊢case _ _ ⊢L′ ⊢M′ ⊢N′ 𝐶⊢-case) σ⊑ (⊑-case L⊑ A⊑ B⊑ M⊑ N⊑) =
  ⊑-case (subst-pres-⊑ ⊢σ ⊢σ′ ⊢L ⊢L′ σ⊑ L⊑) A⊑ B⊑
    (subst-pres-⊑ (λ {x} ∋x → ext-pres ⊢σ  {x} ∋x)
                  (λ {x} ∋x → ext-pres ⊢σ′ {x} ∋x)
                  ⊢M ⊢M′ (ext-pres-⊑ˢ ⊢σ ⊢σ′ σ⊑) M⊑)
    (subst-pres-⊑ (λ {x} ∋x → ext-pres ⊢σ  {x} ∋x)
                  (λ {x} ∋x → ext-pres ⊢σ′ {x} ∋x)
                  ⊢N ⊢N′ (ext-pres-⊑ˢ ⊢σ ⊢σ′ σ⊑) N⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢cast _ ⊢M 𝐶⊢-cast) (⊢cast _ ⊢M′ 𝐶⊢-cast) σ⊑ (⊑-cast A⊑ B⊑ M⊑) =
  ⊑-cast A⊑ B⊑ (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢cast _ ⊢M 𝐶⊢-cast) ⊢M′ σ⊑ (⊑-castl A⊑A′ B⊑A′ ⊢M′₁ M⊑) =
  ⊑-castl A⊑A′ B⊑A′ (preserve-subst _ ⊢M′₁ ⊢σ′) (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ ⊢M (⊢cast _ ⊢M′ 𝐶⊢-cast) σ⊑ (⊑-castr A⊑A′ A⊑B′ ⊢M₁  M⊑) =
  ⊑-castr A⊑A′ A⊑B′ (preserve-subst _ ⊢M₁ ⊢σ) (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ (⊢wrap _ _ ⊢M 𝐶⊢-wrap) (⊢wrap _ _ ⊢M′ 𝐶⊢-wrap) σ⊑ (⊑-wrap lpii M⊑ dd) =
  ⊑-wrap lpii (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑) dd
subst-pres-⊑ ⊢σ ⊢σ′ (⊢wrap _ _ ⊢M 𝐶⊢-wrap) ⊢M′ σ⊑ (⊑-wrapl lpit ⊢M′₁ M⊑) =
  ⊑-wrapl lpit (preserve-subst _ ⊢M′₁ ⊢σ′) (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ ⊢M (⊢wrap _ _ ⊢M′ 𝐶⊢-wrap) σ⊑ (⊑-wrapr lpti ⊢M₁ M⊑ nd) =
  ⊑-wrapr lpti (preserve-subst _ ⊢M₁ ⊢σ) (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑) nd
subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ ⊑-blame = ⊑-blame
