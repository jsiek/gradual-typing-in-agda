module Utils where

open import Data.Unit using (⊤)
open import Data.List using ([])
open import Reflection hiding (name; Type)
open import Function using (_$_)

macro
  db0 : Term → TC ⊤
  db0 hole = unify hole (var 0 [])

{- Reference: https://agda.readthedocs.io/en/v2.6.2/language/with-abstraction.html
   Only works for non-dependent functions: -}
case_of_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A → (A → B) → B
case_of_ a f = f a

{- For dependent functions the target type will in most cases not be inferrable: -}
case_return_of_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (x : A) (B : A → Set ℓ₂) → (∀ x → B x) → B x
case x return B of f = f x
