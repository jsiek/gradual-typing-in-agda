open import Data.Nat using (ℕ; zero; suc)

open import SimpleCast using (Cast)
open Cast
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast

-- test
-- M : ∅ ⊢ ⋆
-- M = ($_ zero {Prim.P-Base}) ⟨ _⇒⟨_⟩_ (` Nat) (Label.pos zero) ⋆ {unk~R} ⟩

-- The inductively defined datatype `HasCast` talks about what it means for a cast `c` to appear in a term `M` .
data HasCast : ∀ {Γ A S T} → (M : Γ ⊢ A) → (c : Cast (S ⇒ T)) → Set where

  -- Base
  HasCast-cast : ∀ {Γ S T} {M : Γ ⊢ S} {c : Cast (S ⇒ T)}
    → HasCast (M ⟨ c ⟩) c

  -- Ind
  HasCast-castᵢ : ∀ {Γ S S′ T T′} {M : Γ ⊢ S′} {c : Cast (S ⇒ T)} {c′ : Cast (S′ ⇒ T′)}
    → HasCast M c
    → HasCast (M ⟨ c′ ⟩) c

  HasCast-ƛ : ∀ {Γ A B S T} {N : Γ , A ⊢ B} {c : Cast (S ⇒ T)}
    → HasCast N c
    → HasCast (ƛ N) c

  HasCast-·ₗ : ∀ {Γ A B S T} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} {c : Cast (S ⇒ T)}
    → HasCast L c
    → HasCast (L · M) c

  HasCast-·ᵣ : ∀ {Γ A B S T} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} {c : Cast (S ⇒ T)}
    → HasCast M c
    → HasCast (L · M) c

  HasCast-ifₗ : ∀ {Γ A S T} {L : Γ ⊢ ` 𝔹} {M : Γ ⊢ A} {N : Γ ⊢ A} {c : Cast (S ⇒ T)}
    → HasCast L c
    → HasCast (if L M N) c

  HasCast-ifₘ : ∀ {Γ A S T} {L : Γ ⊢ ` 𝔹} {M : Γ ⊢ A} {N : Γ ⊢ A} {c : Cast (S ⇒ T)}
    → HasCast M c
    → HasCast (if L M N) c

  HasCast-ifᵣ : ∀ {Γ A S T} {L : Γ ⊢ ` 𝔹} {M : Γ ⊢ A} {N : Γ ⊢ A} {c : Cast (S ⇒ T)}
    → HasCast N c
    → HasCast (if L M N) c

  HasCast-consₗ : ∀ {Γ A B S T} {M : Γ ⊢ A} {N : Γ ⊢ B} {c : Cast (S ⇒ T)}
    → HasCast M c
    → HasCast (cons M N) c

  HasCast-consᵣ : ∀ {Γ A B S T} {M : Γ ⊢ A} {N : Γ ⊢ B} {c : Cast (S ⇒ T)}
    → HasCast N c
    → HasCast (cons M N) c

  HasCast-fst : ∀ {Γ A B S T} {M : Γ ⊢ A `× B} {c : Cast (S ⇒ T)}
    → HasCast M c
    → HasCast (fst M) c

  HasCast-snd : ∀ {Γ A B S T} {M : Γ ⊢ A `× B} {c : Cast (S ⇒ T)}
    → HasCast M c
    → HasCast (snd M) c

  HasCast-inl : ∀ {Γ A B S T} {M : Γ ⊢ A} {c : Cast (S ⇒ T)}
    → HasCast M c
    → HasCast (inl {B = B} M) c

  HasCast-inr : ∀ {Γ A B S T} {N : Γ ⊢ B} {c : Cast (S ⇒ T)}
    → HasCast N c
    → HasCast (inr {A = A} N) c

  HasCast-caseₗ : ∀ {Γ A B C S T} {L : Γ ⊢ A `⊎ B} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C} {c : Cast (S ⇒ T)}
    → HasCast L c
    → HasCast (case L M N) c

  HasCast-caseₘ : ∀ {Γ A B C S T} {L : Γ ⊢ A `⊎ B} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C} {c : Cast (S ⇒ T)}
    → HasCast M c
    → HasCast (case L M N) c

  HasCast-caseᵣ : ∀ {Γ A B C S T} {L : Γ ⊢ A `⊎ B} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C} {c : Cast (S ⇒ T)}
    → HasCast N c
    → HasCast (case L M N) c
