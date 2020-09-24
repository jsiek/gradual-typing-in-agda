module Variables where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Types

infixl 5 _,_

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context


infix  4 _∋_
infix  9 S_

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

∋→ℕ : ∀{Γ}{A} → Γ ∋ A → ℕ
∋→ℕ {.(_ , A)} {A} Z = 0
∋→ℕ {.(_ , _)} {A} (S Γ∋A) = suc (∋→ℕ Γ∋A)

var-eq? : ∀ {Γ A}
  → (x₁ x₂ : Γ ∋ A)
  → Dec (x₁ ≡ x₂)
var-eq? Z Z = yes refl
var-eq? Z (S _) = no λ ()
var-eq? (S _) Z = no λ ()
var-eq? (S x₁) (S x₂) with var-eq? x₁ x₂
... | yes x₁≡x₂ = yes (cong S_ x₁≡x₂)
... | no  x₁≢x₂ = no λ { refl → x₁≢x₂ refl }
