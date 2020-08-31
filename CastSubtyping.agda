module CastSubtyping where

open import SimpleCast using (Cast)
open Cast
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast



-- The subtyping relation.
--   NOTE: Since simple cast is D, using traditional subtyping is fine.
infix 5 _<:_

data _<:_ : Type → Type → Set where

  T<:⋆ : ∀ {T} → T <: ⋆

  <:-B : ∀ {B} → ` B <: ` B

  -- Product and sum are monotone with respect to subtyping.
  <:-× : ∀ {S₁ S₂ T₁ T₂}
    → S₁ <: T₁ → S₂ <: T₂
      ---------------------
    → S₁ `× S₂ <: T₁ `× T₂

  <:-⊎ : ∀ {S₁ S₂ T₁ T₂}
    → S₁ <: T₁ → S₂ <: T₂
      ---------------------
    → S₁ `⊎ S₂ <: T₁ `⊎ T₂

  <:-⇒ : ∀ {S₁ S₂ T₁ T₂}
    → T₁ <: S₁ → S₂ <: T₂
      ---------------------
    → S₁ ⇒ S₂ <: T₁ ⇒ T₂



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

-- Data type `CastsRespect<:` says all casts in M respect subtyping.
data CastsRespect<: : ∀ {Γ A} → (M : Γ ⊢ A) → Set where

  CastsRespect<:-cast : ∀ {Γ S T} {M : Γ ⊢ S} {c : Cast (S ⇒ T)}
    → S <: T
    → CastsRespect<: M
    → CastsRespect<: (M ⟨ c ⟩)

  CastsRespect<:-var : ∀ {Γ A} {x : Γ ∋ A}
    → CastsRespect<: (` x)

  CastsRespect<:-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → CastsRespect<: N
    → CastsRespect<: (ƛ N)

  CastsRespect<:-· : ∀ {Γ A B S T} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} {c : Cast (S ⇒ T)}
    → CastsRespect<: L
    → CastsRespect<: M
    → CastsRespect<: (L · M)

  CastsRespect<:-prim : ∀ {Γ A} {p : rep A} {f : Prim A}
    → CastsRespect<: ($_ {Γ} p {f})

  CastsRespect<:-if : ∀ {Γ A} {L : Γ ⊢ ` 𝔹} {M : Γ ⊢ A} {N : Γ ⊢ A}
    → CastsRespect<: L
    → CastsRespect<: M
    → CastsRespect<: N
    → CastsRespect<: (if L M N)

  CastsRespect<:-cons : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ ⊢ B}
    → CastsRespect<: M
    → CastsRespect<: N
    → CastsRespect<: (cons M N)

  CastsRespect<:-fst : ∀ {Γ A B} {M : Γ ⊢ A `× B}
    → CastsRespect<: M
    → CastsRespect<: (fst M)

  CastsRespect<:-snd : ∀ {Γ A B} {M : Γ ⊢ A `× B}
    → CastsRespect<: M
    → CastsRespect<: (snd M)

  CastsRespect<:-inl : ∀ {Γ A B} {M : Γ ⊢ A}
    → CastsRespect<: M
    → CastsRespect<: (inl {B = B} M)

  CastsRespect<:-inr : ∀ {Γ A B} {N : Γ ⊢ B}
    → CastsRespect<: N
    → CastsRespect<: (inr {A = A} N)

  CastsRespect<:-case : ∀ {Γ A B C} {L : Γ ⊢ A `⊎ B} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C}
    → CastsRespect<: L
    → CastsRespect<: M
    → CastsRespect<: N
    → CastsRespect<: (case L M N)

  CastsRespect<:-blame : ∀ {Γ A 𝓁}
    → CastsRespect<: (blame {Γ} {A} 𝓁)
