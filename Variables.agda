module Variables where

open import Data.Nat using (ℕ; zero; suc)
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
