{-# OPTIONS --rewriting #-}

module PolyBlame.Consistency where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.List.Properties using (map-∘)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (_∨_; _≤_)
open import Data.Bool.Properties
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Bool
open import Relation.Nullary using (¬_)

import Relation.Binary.PropositionalEquality as Eq
--open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import PolyBlame.Types
open import PolyBlame.TypePrecision

{-- Consistency --}

infixr 6 _∣_⊢_∼_
data _∣_⊢_∼_ : (Δ : TyCtx) → SubCtx Δ → Type Δ → Type Δ → Set where
  ℕ∼ℕ : ∀{Δ}{Ψ}
      ------------------
     → Δ ∣ Ψ ⊢ `ℕ ∼ `ℕ
     
  X∼X : ∀{Δ}{Ψ}{X}
      --------------------
     → Δ ∣ Ψ ⊢ ` X ∼ ` X

  ★∼★ : ∀{Δ}{Ψ}
      ----------------
     → Δ ∣ Ψ ⊢ ★ ∼ ★

  ★∼X : ∀{Δ}{Ψ}{X : TyVar Δ}
     → Ψ ∋ˢ X
      ------------------
     → Δ ∣ Ψ ⊢ ★ ∼ ` X

  X∼★ : ∀{Δ}{Ψ}{X : TyVar Δ}
     → Ψ ∋ˢ X
      -----------------
     → Δ ∣ Ψ ⊢ ` X ∼ ★

  ★∼ℕ : ∀{Δ}{Ψ}
     --------------------
     → Δ ∣ Ψ ⊢ ★ ∼ `ℕ

  ℕ∼★ : ∀{Δ}{Ψ}
     ------------------
     → Δ ∣ Ψ ⊢ `ℕ ∼ ★

  ⇒∼★ : ∀{Δ}{Ψ}{A B}
     → Δ ∣ Ψ ⊢ A ∼ ★
     → Δ ∣ Ψ ⊢ B ∼ ★
       ------------------
     → Δ ∣ Ψ ⊢ A ⇒ B ∼ ★

  ★∼⇒ : ∀{Δ}{Ψ}{A B}
     → Δ ∣ Ψ ⊢ ★ ∼ A
     → Δ ∣ Ψ ⊢ ★ ∼ B
       ------------------
     → Δ ∣ Ψ ⊢ ★ ∼ A ⇒ B

  ⇒∼⇒ : ∀{Δ}{Ψ}{A B C D}
     →  Δ ∣ Ψ ⊢ A ∼ C
     →  Δ ∣ Ψ ⊢ B ∼ D
      ------------------------
     → Δ ∣ Ψ ⊢ A ⇒ B ∼ C ⇒ D

  ∀∼∀ : ∀{Δ}{Ψ}{A B}
     → (Δ ,typ) ∣ (Ψ , false) ⊢ A ∼ B
      --------------------------------
     → Δ ∣ Ψ ⊢ `∀ A ∼ `∀ B

  ∼∀ : ∀{Δ}{Ψ}{A B}
     → (Δ ,typ) ∣ (Ψ , true) ⊢ ⇑ᵗ A ∼ B
      ----------------------------------
     → Δ ∣ Ψ ⊢ A ∼ `∀ B

  ∀∼ : ∀{Δ}{Ψ}{A B}
     → (Δ ,typ) ∣ (Ψ , true) ⊢ A ∼ ⇑ᵗ B
      ----------------------------------
     → Δ ∣ Ψ ⊢ `∀ A ∼ B

_⊑_ : ∀{Δ} → SubCtx Δ → SubCtx Δ → Set
∅ ⊑ ∅ = ⊤
(Ψ , b) ⊑ (Ψ′ , b′) = (Ψ ⊑ Ψ′) × (b ≤ b′)

_⊔_ : ∀{Δ} → SubCtx Δ → SubCtx Δ → SubCtx Δ
∅ ⊔ ∅ = ∅
(Ψ , b) ⊔ (Ψ′ , b′) = (Ψ ⊔ Ψ′) , b ∨ b′

less-refl : ∀{Δ}(Ψ : SubCtx Δ)
  → Ψ ⊑ Ψ
less-refl ∅ = tt
less-refl (Ψ , b) = less-refl Ψ , _≤_.b≤b

less-lub-left : ∀{Δ}(Ψ Ψ′ : SubCtx Δ)
  → Ψ ⊑ (Ψ ⊔ Ψ′)
less-lub-left {Δ} ∅ ∅ = tt
less-lub-left {Δ} (Ψ , b) (Ψ′ , b′) = (less-lub-left Ψ Ψ′) , ≤-or-left b b′

less-lub-right : ∀{Δ}(Ψ Ψ′ : SubCtx Δ)
  → Ψ′ ⊑ (Ψ ⊔ Ψ′)
less-lub-right {Δ} ∅ ∅ = tt
less-lub-right {Δ} (Ψ , b) (Ψ′ , b′) = (less-lub-right Ψ Ψ′) , ≤-or-right b b′

weaken-∋ : ∀{Δ}{Ψ Ψ′}{X : TyVar Δ}
  → Ψ ⊑ Ψ′
  → Ψ ∋ˢ X
  → Ψ′ ∋ˢ X
weaken-∋ {Ψ′ = Ψ′ , true} Ψ⊑Ψ′ Zˢ = Zˢ
weaken-∋ {Ψ′ = Ψ′ , b′} Ψ⊑Ψ′ (Sˢ ∋X) = Sˢ (weaken-∋ (Ψ⊑Ψ′ .proj₁) ∋X)

weaken-⊑ : ∀{Δ}{Ψ Ψ′}{A B : Type Δ}
  → Ψ ⊑ Ψ′
  → Δ ∣ Ψ ⊢ A ⊑ B
  → Δ ∣ Ψ′ ⊢ A ⊑ B
weaken-⊑ Ψ⊑Ψ′ ℕ⊑ℕ = ℕ⊑ℕ
weaken-⊑ Ψ⊑Ψ′ X⊑X = X⊑X
weaken-⊑ Ψ⊑Ψ′ ★⊑★ = ★⊑★
weaken-⊑ Ψ⊑Ψ′ (★⊑X ∋X) = ★⊑X (weaken-∋ Ψ⊑Ψ′ ∋X)
weaken-⊑ Ψ⊑Ψ′ ★⊑ℕ = ★⊑ℕ
weaken-⊑ Ψ⊑Ψ′ (★⊑⇒ ★⊑A ★⊑B) = ★⊑⇒ (weaken-⊑ Ψ⊑Ψ′ ★⊑A) (weaken-⊑ Ψ⊑Ψ′ ★⊑B)
weaken-⊑ Ψ⊑Ψ′ (⇒⊑⇒ A⊑C B⊑D) = ⇒⊑⇒ (weaken-⊑ Ψ⊑Ψ′ A⊑C) (weaken-⊑ Ψ⊑Ψ′ B⊑D)
weaken-⊑ Ψ⊑Ψ′ (∀⊑∀ A⊑B) = ∀⊑∀ (weaken-⊑ (Ψ⊑Ψ′ , _≤_.b≤b) A⊑B)
weaken-⊑ Ψ⊑Ψ′ (⊑∀ A⊑B) = ⊑∀ (weaken-⊑ (Ψ⊑Ψ′ , _≤_.b≤b) A⊑B)

weaken-∼ : ∀{Δ}{Ψ Ψ′}{A B : Type Δ}
  → Ψ ⊑ Ψ′
  → Δ ∣ Ψ ⊢ A ∼ B
  → Δ ∣ Ψ′ ⊢ A ∼ B
weaken-∼ Ψ⊑Ψ′ ℕ∼ℕ = ℕ∼ℕ
weaken-∼ Ψ⊑Ψ′ X∼X = X∼X
weaken-∼ Ψ⊑Ψ′ ★∼★ = ★∼★
weaken-∼ Ψ⊑Ψ′ (★∼X ∋X) = ★∼X (weaken-∋ Ψ⊑Ψ′ ∋X)
weaken-∼ Ψ⊑Ψ′ (X∼★ ∋X) = X∼★ (weaken-∋ Ψ⊑Ψ′ ∋X)
weaken-∼ Ψ⊑Ψ′ ★∼ℕ = ★∼ℕ
weaken-∼ Ψ⊑Ψ′ ℕ∼★ = ℕ∼★
weaken-∼ Ψ⊑Ψ′ (⇒∼★ A∼★ B∼★) = ⇒∼★ (weaken-∼ Ψ⊑Ψ′ A∼★) (weaken-∼ Ψ⊑Ψ′ B∼★)
weaken-∼ Ψ⊑Ψ′ (★∼⇒ ★∼A ★∼B) = ★∼⇒ (weaken-∼ Ψ⊑Ψ′ ★∼A) (weaken-∼ Ψ⊑Ψ′ ★∼B)
weaken-∼ Ψ⊑Ψ′ (⇒∼⇒ A∼C B∼D) = ⇒∼⇒ (weaken-∼ Ψ⊑Ψ′ A∼C) (weaken-∼ Ψ⊑Ψ′ B∼D)
weaken-∼ Ψ⊑Ψ′ (∀∼∀ A∼B) = ∀∼∀ (weaken-∼ (Ψ⊑Ψ′ , _≤_.b≤b) A∼B)
weaken-∼ Ψ⊑Ψ′ (∼∀ A∼B) = ∼∀ (weaken-∼ (Ψ⊑Ψ′ , _≤_.b≤b) A∼B)
weaken-∼ Ψ⊑Ψ′ (∀∼ A∼B) = ∀∼ (weaken-∼ (Ψ⊑Ψ′ , _≤_.b≤b) A∼B)

injective : ∀{A B : Set} → (A → B) → Set
injective{A} f = ∀ (x y : A) → (f x ≡ f y) → (x ≡ y)

injective-Sᵗ : ∀{Δ} → injective (Sᵗ{Δ})
injective-Sᵗ x y refl = refl

injective-ext : ∀{Δ Δ′}
    → (ρ : Δ ⇒ᵗ Δ′)
    → injective ρ
    → injective (extᵗ ρ)
injective-ext ρ inj Zᵗ Zᵗ eq = refl
injective-ext ρ inj (Sᵗ x) (Sᵗ y) eq =
  cong Sᵗ (inj x y (injective-Sᵗ (ρ x) (ρ y) eq))

X≡Y⇒X∼Y : ∀{Δ}{Ψ}{X Y : TyVar Δ}
  → X ≡ Y
  → Δ ∣ Ψ ⊢ ` X ∼ ` Y
X≡Y⇒X∼Y refl = X∼X

X∼Y⇒X≡Y : ∀{Δ}{Ψ}{X Y : TyVar Δ}
  → Δ ∣ Ψ ⊢ ` X ∼ ` Y
  → X ≡ Y
X∼Y⇒X≡Y X∼X = refl

-- Capture the initial one and changes needed for the IH
data Pres-⇑ : ∀{Δ Δ′} → (ρ : Δ ⇒ᵗ Δ′)
    → (Ψ : SubCtx Δ) → (Ψ′ : SubCtx Δ′) → Set where
    
  Pres-Sᵗ : ∀{Δ}{Ψ}{b} → Pres-⇑{Δ}{Δ ,typ} Sᵗ Ψ (Ψ , b)
  
  Pres-ext : ∀{Δ Δ′}{Ψ Ψ′}{b}{ρ : Δ ⇒ᵗ Δ′}
    → Pres-⇑ ρ Ψ Ψ′
    → Pres-⇑ (extᵗ ρ) (Ψ , b) (Ψ′ , b)

-- Prove that the each case has the desired property
Pres-⇑⇒∋ : ∀{Δ Δ′}{Ψ Ψ′}{X}
  → (ρ : Δ ⇒ᵗ Δ′)
  → Pres-⇑ ρ Ψ Ψ′
  → Ψ′ ∋ˢ ρ X
  → Ψ ∋ˢ X
Pres-⇑⇒∋ ρ Pres-Sᵗ (Sˢ ∋ρX) = ∋ρX
Pres-⇑⇒∋ {X = Zᵗ} ρ (Pres-ext IH) Zˢ = Zˢ
Pres-⇑⇒∋ {X = Sᵗ X} ρ (Pres-ext {ρ = ρ′} IH) (Sˢ ∋ρX) =
  Sˢ (Pres-⇑⇒∋ ρ′ IH ∋ρX)

ren-type-∼ : ∀{Δ Δ′}{Ψ Ψ′}{A B : Type Δ}
    → (ρ : Δ ⇒ᵗ Δ′)
    → Δ′ ∣ Ψ′ ⊢ renᵗ ρ A ∼ renᵗ ρ B
    → injective ρ
    → Pres-⇑ ρ Ψ Ψ′
    → Δ ∣ Ψ ⊢ A ∼ B
ren-type-∼ {A = `ℕ} {`ℕ} ρ ρA∼ρB inj p = ℕ∼ℕ
ren-type-∼ {A = `ℕ} {★} ρ ρA∼ρB inj p = ℕ∼★
ren-type-∼ {A = `ℕ} {`∀ B} ρ (∼∀ ρA∼ρB) inj p =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext p))
ren-type-∼ {A = ★} {`ℕ} ρ ρA∼ρB inj pres = ★∼ℕ
ren-type-∼ {A = ★} {★} ρ ρA∼ρB inj pres = ★∼★
ren-type-∼ {A = ★} {` X} ρ (★∼X ∋ρX) inj pres =
  ★∼X (Pres-⇑⇒∋ ρ pres ∋ρX)
ren-type-∼ {A = ★} {B₁ ⇒ B₂} ρ (★∼⇒ ρA∼ρB ρA∼ρB₁) inj pres =
  ★∼⇒ (ren-type-∼ ρ ρA∼ρB inj pres) (ren-type-∼ ρ ρA∼ρB₁ inj pres)
ren-type-∼ {A = ★} {`∀ B} ρ (∼∀ ρA∼ρB) inj pres =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = ` X} {★} ρ (X∼★ ∋ρX) inj pres =
  X∼★ (Pres-⇑⇒∋ ρ pres ∋ρX)
ren-type-∼ {A = ` X} {` Y} ρ ρA∼ρB inj pres =
  X≡Y⇒X∼Y (inj X Y (X∼Y⇒X≡Y ρA∼ρB))
ren-type-∼ {A = ` X} {`∀ B} ρ (∼∀ ρA∼ρB) inj pres =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = A₁ ⇒ A₂} {★} ρ (⇒∼★ ρA∼ρB ρA∼ρB₁) inj pres =
  ⇒∼★ (ren-type-∼ ρ ρA∼ρB inj pres) (ren-type-∼ ρ ρA∼ρB₁ inj pres)
ren-type-∼ {A = A₁ ⇒ A₂} {B₁ ⇒ B₂} ρ (⇒∼⇒ ρA∼ρB ρA∼ρB₁) inj pres =
  ⇒∼⇒ (ren-type-∼ ρ ρA∼ρB inj pres) (ren-type-∼ ρ ρA∼ρB₁ inj pres)
ren-type-∼ {A = A₁ ⇒ A₂} {`∀ B} ρ (∼∀ ρA∼ρB) inj pres =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {`ℕ} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {★} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {` x} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {B₁ ⇒ B₂} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {`∀ B} ρ (∀∼∀ ρA∼ρB) inj pres =
  ∀∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {`∀ B} ρ (∼∀ ρA∼ρB) inj pres =
  ∼∀ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))
ren-type-∼ {A = `∀ A} {`∀ B} ρ (∀∼ ρA∼ρB) inj pres =
  ∀∼ (ren-type-∼ (extᵗ ρ) ρA∼ρB (injective-ext ρ inj) (Pres-ext pres))

dec-∼ : ∀{Δ}{Ψ}{A B : Type Δ}{b}
    → (Δ ,typ) ∣ Ψ , b ⊢ ⇑ᵗ A ∼ ⇑ᵗ B
    → Δ ∣ Ψ ⊢ A ∼ B
dec-∼ ⇑A∼⇑B = ren-type-∼ Sᵗ ⇑A∼⇑B injective-Sᵗ Pres-Sᵗ

UB⇒consistent : ∀{Δ}{Ψ₁ Ψ₂}{A B C : Type Δ}
  → Δ ∣ Ψ₁ ⊢ A ⊑ C
  → Δ ∣ Ψ₂ ⊢ B ⊑ C
  → Δ ∣ Ψ₁ ⊔ Ψ₂ ⊢ A ∼ B
UB⇒consistent{Ψ₁ = Ψ₁} ℕ⊑ℕ ℕ⊑ℕ = ℕ∼ℕ
UB⇒consistent{Ψ₁ = Ψ₁} ℕ⊑ℕ ★⊑ℕ = ℕ∼★
UB⇒consistent{Ψ₁ = Ψ₁} X⊑X X⊑X =  X∼X
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} X⊑X (★⊑X ∋X) =
  X∼★ (weaken-∋ (less-lub-right Ψ₁ Ψ₂) ∋X)
UB⇒consistent{Ψ₁ = Ψ₁} ★⊑★ ★⊑★ = ★∼★
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (★⊑X ∋X) X⊑X =
  ★∼X (weaken-∋ (less-lub-left Ψ₁ Ψ₂) ∋X)
UB⇒consistent{Ψ₁ = Ψ₁} (★⊑X ∋X) (★⊑X ∋X′) =  ★∼★
UB⇒consistent{Ψ₁ = Ψ₁} ★⊑ℕ ℕ⊑ℕ = ★∼ℕ
UB⇒consistent{Ψ₁ = Ψ₁} ★⊑ℕ ★⊑ℕ = ★∼★
UB⇒consistent{Ψ₁ = Ψ₁} (★⊑⇒ ac ac₁) (★⊑⇒ bc bc₁) = ★∼★
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (★⊑⇒{A = C₁}{B = C₂} ★⊑C₁ ★⊑C₂)
                           (⇒⊑⇒{A = B₁}{B₂} B₁⊑C₁ B₂⊑C₂) =
    ★∼⇒ (UB⇒consistent ★⊑C₁ B₁⊑C₁) (UB⇒consistent ★⊑C₂ B₂⊑C₂)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (⇒⊑⇒ a⊑c b⊑d) (★⊑⇒ ⊑c ⊑d) =
    ⇒∼★ (UB⇒consistent a⊑c ⊑c) (UB⇒consistent b⊑d ⊑d)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (⇒⊑⇒ a⊑c b⊑d) (⇒⊑⇒ ac bd) =
    ⇒∼⇒ (UB⇒consistent a⊑c ac) (UB⇒consistent b⊑d bd)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (∀⊑∀ a⊑b) (∀⊑∀ a′⊑b) =
    ∀∼∀ (UB⇒consistent a⊑b a′⊑b)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (∀⊑∀{B = C} ac) (⊑∀{B = C}  bc) =
  ∀∼ (UB⇒consistent ac bc)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (⊑∀ ac) (∀⊑∀ bc) = ∼∀ (UB⇒consistent ac bc)
UB⇒consistent{Ψ₁ = Ψ₁}{Ψ₂} (⊑∀ ac) (⊑∀ bc) = dec-∼ (UB⇒consistent ac bc)

postulate
  ∼-sym : ∀{Δ}{Ψ : SubCtx Δ}{Σ : BindCtx Δ}{A B : Type Δ}
    → Δ ∣ Ψ ⊢ A ∼ B
    → Δ ∣ Ψ ⊢ B ∼ A
  
data _∌_ : ∀{Δ : TyCtx} → BindCtx Δ → TyVar Δ → Set where
  ∌-[] : ∀ {Δ}{Σ : BindCtx Δ}{X : TyVar Δ}
    → [] ∌ X
  ∌-∷ : ∀ {Δ}{Σ : BindCtx Δ}{X Y : TyVar Δ}{B : Type Δ}
    → Σ ∌ X
    → X ≢ Y
    → ((Y , B) ∷ Σ) ∌ X

