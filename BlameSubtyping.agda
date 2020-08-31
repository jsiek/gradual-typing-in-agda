open import Data.Nat using (ℕ; zero; suc)

open import SimpleCast using (Cast)
open Cast
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast
open import CastSubtyping using (CastsRespect<:)

-- Test
M : ∅ ⊢ ⋆
M = ($_ zero {Prim.P-Base}) ⟨ _⇒⟨_⟩_ (` Nat) (Label.pos zero) ⋆ {unk~R} ⟩

{-
  This file is a stub.
-}
