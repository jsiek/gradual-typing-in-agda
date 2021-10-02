open import Data.Nat
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

open import Types
open import Labels
open import PreCastStructureWithPrecisionABT

open import Utils
open import Syntax



module PreservePrecisionABT (pcsp : PreCastStructWithPrecision) where

open PreCastStructWithPrecision pcsp
open import ParamCastCalculusABT precast
open import ParamCCPrecisionABT pcsp

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
  → ρ ⦂ Γ  ⇒ Δ
  → ρ ⦂ Γ′ ⇒ Δ′
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
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-wrap lpii M⊑ imp) =
  ⊑-wrap lpii (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑) imp
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-wrapl lpit ⊢M′ M⊑) =
  ⊑-wrapl lpit (preserve-rename _ ⊢M′ ⊢ρ′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-wrapr lpti ⊢M M⊑ nd) =
  ⊑-wrapr lpti (preserve-rename _ ⊢M ⊢ρ) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑) nd
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-blame ⊢M A⊑A′) =
  ⊑-blame (preserve-rename _ ⊢M ⊢ρ) A⊑A′

ext-pres-⊑ˢ : ∀ {Γ Γ′ Δ Δ′} {A A′} {σ σ′ : Subst}
  → σ  ⦂ Γ  ⇒ Δ
  → σ′ ⦂ Γ′ ⇒ Δ′
  → Γ ⇒ Δ , Γ′ ⇒ Δ′ ⊢ σ ⊑ˢ σ′
    --------------------------------------------------------------
  → (A ∷ Γ) ⇒ (A ∷ Δ) , (A′ ∷ Γ′) ⇒ (A′ ∷ Δ′) ⊢ ext σ ⊑ˢ ext σ′
ext-pres-⊑ˢ ⊢σ ⊢σ′ σ⊑ ⊢extσ ⊢extσ′ 0 ⟨ X , x⦂X ⟩ ⟨ X′ , x⦂X′ ⟩ = ⊑-`
ext-pres-⊑ˢ {σ = σ} ⊢σ ⊢σ′ σ⊑ ⊢extσ ⊢extσ′ (suc x) lookup-x lookup-x′
  rewrite exts-suc' σ x =
  -- rename ⇑ (σ x) ⊑ rename ⇑ (σ′ x)
  rename-pres-⊑ (λ ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩)  {- ⇑ ⦂ Γ ⇒ A ∷ Γ -}
                (λ ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩)
                (σ⊑ ⊢σ ⊢σ′ x lookup-x lookup-x′)

subst-pres-⊑ : ∀ {Γ Γ′ Δ Δ′} {A A′} {M M′ : Term} {σ σ′}
  → σ  ⦂ Γ  ⇒ Δ
  → σ′ ⦂ Γ′ ⇒ Δ′
  → Γ  ⊢ M  ⦂ A
  → Γ′ ⊢ M′ ⦂ A′
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
subst-pres-⊑ ⊢σ ⊢σ′ (⊢wrap _ _ ⊢M 𝐶⊢-wrap) (⊢wrap _ _ ⊢M′ 𝐶⊢-wrap) σ⊑ (⊑-wrap lpii M⊑ imp) =
  ⊑-wrap lpii (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑) imp
subst-pres-⊑ ⊢σ ⊢σ′ (⊢wrap _ _ ⊢M 𝐶⊢-wrap) ⊢M′ σ⊑ (⊑-wrapl lpit ⊢M′₁ M⊑) =
  ⊑-wrapl lpit (preserve-subst _ ⊢M′₁ ⊢σ′) (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑)
subst-pres-⊑ ⊢σ ⊢σ′ ⊢M (⊢wrap _ _ ⊢M′ 𝐶⊢-wrap) σ⊑ (⊑-wrapr lpti ⊢M₁ M⊑ nd) =
  ⊑-wrapr lpti (preserve-subst _ ⊢M₁ ⊢σ) (subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ M⊑) nd
subst-pres-⊑ ⊢σ ⊢σ′ ⊢M ⊢M′ σ⊑ (⊑-blame ⊢M₁ A⊑A′) =
  ⊑-blame (preserve-subst _ ⊢M₁ ⊢σ) A⊑A′

substitution-pres-⊑ : ∀ {Γ Γ′ A A′ B B′} {N N′ M M′}
  → A  ∷ Γ  ⊢ N ⦂ B
  → A′ ∷ Γ′ ⊢ N′ ⦂ B′
  → Γ  ⊢ M ⦂ A
  → Γ′ ⊢ M′ ⦂ A′
  → (A ∷ Γ) , (A′ ∷ Γ′) ⊢ N ⊑ N′
  → Γ , Γ′ ⊢ M ⊑ M′
    -----------------------------
  → Γ , Γ′ ⊢ N [ M ] ⊑ N′ [ M′ ]
substitution-pres-⊑ ⊢N ⊢N′ ⊢M ⊢M′ N⊑ M⊑ =
  subst-pres-⊑
    (λ { {0} refl → ⊢M  ; {suc k} ∋x → ⊢` ∋x })
    (λ { {0} refl → ⊢M′ ; {suc k} ∋x → ⊢` ∋x })
    ⊢N ⊢N′
    (λ { ⊢σ ⊢σ′ 0       lookup-x lookup-x′ → M⊑ ;
         ⊢σ ⊢σ′ (suc x) lookup-x lookup-x′ → ⊑-` })
    N⊑



infix 4 _⊑*_

_⊑*_ : List Type → List Type → Set
Γ ⊑* Γ′ = ∀ {A A′} → (x : Var) → Γ ∋ x ⦂ A → Γ′ ∋ x ⦂ A′ → A ⊑ A′

⊑*-ext : ∀ {Γ Γ′} {A A′}
  → Γ ⊑* Γ′
  → A ⊑  A′
    -----------------
  → A ∷ Γ ⊑* A′ ∷ Γ′
⊑*-ext Γ⊑Γ′ A⊑A′ 0 refl refl = A⊑A′
⊑*-ext Γ⊑Γ′ A⊑A′ (suc x) ∋x ∋x′ = Γ⊑Γ′ x ∋x ∋x′

cc-prec→⊑ : ∀ {Γ Γ′} {A A′} {M M′}
  → Γ ⊑* Γ′
  → Γ  ⊢ M  ⦂ A
  → Γ′ ⊢ M′ ⦂ A′
  → Γ , Γ′ ⊢ M ⊑ M′
    ----------------
  → A ⊑ A′
cc-prec→⊑ Γ⊑Γ′ (⊢$ r p 𝐶⊢-$) (⊢$ r′ p′ 𝐶⊢-$) ⊑-$ = Refl⊑
cc-prec→⊑ Γ⊑Γ′ (⊢` ∋x) (⊢` ∋x′) ⊑-` = Γ⊑Γ′ _ ∋x ∋x′
cc-prec→⊑ Γ⊑Γ′ (⊢ƛ A ⊢N 𝐶⊢-ƛ) (⊢ƛ A′ ⊢N′ 𝐶⊢-ƛ) (⊑-ƛ A⊑A′ N⊑N′) =
  fun⊑ A⊑A′ (cc-prec→⊑ (⊑*-ext Γ⊑Γ′ A⊑A′) ⊢N ⊢N′ N⊑N′)
cc-prec→⊑ Γ⊑Γ′ (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· ⊢L′ ⊢M′ 𝐶⊢-·) (⊑-· L⊑L′ M⊑M′) =
  case cc-prec→⊑ Γ⊑Γ′ ⊢L ⊢L′ L⊑L′ of λ where
    (fun⊑ _ B⊑B′) → B⊑B′
cc-prec→⊑ Γ⊑Γ′ (⊢if ⊢L ⊢M ⊢N 𝐶⊢-if) (⊢if ⊢L′ ⊢M′ ⊢N′ 𝐶⊢-if) (⊑-if L⊑L′ M⊑M′ N⊑N′) =
  cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ M⊑M′
cc-prec→⊑ Γ⊑Γ′ (⊢cons ⊢L ⊢M 𝐶⊢-cons) (⊢cons ⊢L′ ⊢M′ 𝐶⊢-cons) (⊑-cons L⊑L′ M⊑M′) =
  pair⊑ (cc-prec→⊑ Γ⊑Γ′ ⊢L ⊢L′ L⊑L′) (cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ M⊑M′)
cc-prec→⊑ Γ⊑Γ′ (⊢fst ⊢M 𝐶⊢-fst) (⊢fst ⊢M′ 𝐶⊢-fst) (⊑-fst M⊑M′) =
  {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-snd M⊑M′) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-inl x M⊑M′) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-inr x M⊑M′) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-case M⊑M′ x x₁ M⊑M′₁ M⊑M′₂) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-cast x x₁ M⊑M′) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-castl x x₁ x₂ M⊑M′) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-castr x x₁ x₂ M⊑M′) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-wrap x M⊑M′ x₁) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-wrapl x x₁ M⊑M′) = {!!}
cc-prec→⊑ Γ⊑Γ′ ⊢M ⊢M′ (⊑-wrapr x x₁ M⊑M′ x₂) = {!!}
cc-prec→⊑ Γ⊑Γ′ _ (⊢blame A ℓ 𝐶⊢-blame) (⊑-blame ⊢M A⊑A′) = {!!}
