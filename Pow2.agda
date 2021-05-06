module Pow2 where

  open import Data.Nat
  open import Data.Nat.Properties
  
  pow2 : ℕ → ℕ
  pow2 0 = 1
  pow2 (suc n) = 2 * pow2 n

  pow2-pos : ∀ n → 1 ≤ pow2 n
  pow2-pos zero = s≤s z≤n
  pow2-pos (suc n) = let IH = pow2-pos n in ≤-trans IH (m≤m+n _ _)

  pow2-mono-≤ : ∀{n m} → n ≤ m → pow2 n ≤ pow2 m
  pow2-mono-≤ {n}{m} z≤n = pow2-pos m
  pow2-mono-≤ (s≤s n≤m) = +-mono-≤ (pow2-mono-≤ n≤m) (+-mono-≤ (pow2-mono-≤ n≤m) z≤n)
