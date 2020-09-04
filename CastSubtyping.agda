module CastSubtyping where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SimpleCast using (Cast)
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast
open Cast


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

⋆<:T→T≡⋆ : ∀ {T} → ⋆ <: T → T ≡ ⋆
⋆<:T→T≡⋆ T<:⋆ = refl

-- Subtyping `<:` implies consistency.
<:→~ : ∀ {S T} → S <: T → S ~ T
<:→~ T<:⋆ = unk~R
<:→~ <:-B = base~
<:→~ (<:-× sub₁ sub₂) = pair~ (<:→~ sub₁) (<:→~ sub₂)
<:→~ (<:-⊎ sub₁ sub₂) = sum~ (<:→~ sub₁) (<:→~ sub₂)
<:→~ (<:-⇒ sub₁ sub₂) = fun~ (<:→~ sub₁) (<:→~ sub₂)

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

-- Data type `CastsRespect<:` says all casts in M with blame label ℓ respect subtyping.
data CastsRespect<: : ∀ {Γ A} → (M : Γ ⊢ A) → (ℓ : Label) → Set where

  {-
    If the cast has the same blame label as ℓ , which is what the data type is quantified over,
    we require that the source & target types respect subtyping <: .
  -}
  CR<:-cast-same-ℓ : ∀ {Γ S T} {S~T : S ~ T} {M : Γ ⊢ S} {ℓ}
    → (S<:T : S <: T)
    → CastsRespect<: M ℓ
      -------------------------------------
    → CastsRespect<: (M ⟨ (S ⇒⟨ ℓ ⟩ T) {S~T} ⟩) ℓ

  {-
    If the blame label ℓ′ on the cast is different from what the data type is quantified over,
    this is fine and we don't impose any restriction on this cast.
  -}
  CR<:-cast-diff-ℓ : ∀ {Γ S T} {S~T : S ~ T} {M : Γ ⊢ S} {ℓ ℓ′}
    → ℓ ≢ ℓ′
    → CastsRespect<: M ℓ
      ----------------------------------------------
    → CastsRespect<: (M ⟨ (S ⇒⟨ ℓ′ ⟩ T) {S~T} ⟩) ℓ

  CR<:-var : ∀ {Γ A} {x : Γ ∋ A} {ℓ}
      ------------------------------
    → CastsRespect<: (` x) ℓ

  CR<:-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {ℓ}
    → CastsRespect<: N ℓ
      -----------------------
    → CastsRespect<: (ƛ N) ℓ

  CR<:-· : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} {ℓ}
    → CastsRespect<: L ℓ
    → CastsRespect<: M ℓ
      -------------------------
    → CastsRespect<: (L · M) ℓ

  CR<:-prim : ∀ {Γ A} {p : rep A} {f : Prim A} {ℓ}
      --------------------------------------------
    → CastsRespect<: ($_ {Γ} p {f}) ℓ

  CR<:-if : ∀ {Γ A} {L : Γ ⊢ ` 𝔹} {M : Γ ⊢ A} {N : Γ ⊢ A} {ℓ}
    → CastsRespect<: L ℓ
    → CastsRespect<: M ℓ
    → CastsRespect<: N ℓ
      -----------------------------
    → CastsRespect<: (if L M N) ℓ

  CR<:-cons : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ ⊢ B} {ℓ}
    → CastsRespect<: M ℓ
    → CastsRespect<: N ℓ
      ----------------------------
    → CastsRespect<: (cons M N) ℓ

  CR<:-fst : ∀ {Γ A B} {M : Γ ⊢ A `× B} {ℓ}
    → CastsRespect<: M ℓ
      -------------------------
    → CastsRespect<: (fst M) ℓ

  CR<:-snd : ∀ {Γ A B} {M : Γ ⊢ A `× B} {ℓ}
    → CastsRespect<: M ℓ
      -------------------------
    → CastsRespect<: (snd M) ℓ

  CR<:-inl : ∀ {Γ A B} {M : Γ ⊢ A} {ℓ}
    → CastsRespect<: M ℓ
      ---------------------------------
    → CastsRespect<: (inl {B = B} M) ℓ

  CR<:-inr : ∀ {Γ A B} {N : Γ ⊢ B} {ℓ}
    → CastsRespect<: N ℓ
      ----------------------------------
    → CastsRespect<: (inr {A = A} N) ℓ

  CR<:-case : ∀ {Γ A B C} {L : Γ ⊢ A `⊎ B} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C} {ℓ}
    → CastsRespect<: L ℓ
    → CastsRespect<: M ℓ
    → CastsRespect<: N ℓ
      ------------------------------
    → CastsRespect<: (case L M N) ℓ

  {- NOTE:
    A well-typed surface language term can never be compiled into a blame in the cast calculus (CC).
    However we still have a case for `blame ℓ` here since it has such a case in CC.
  -}
  CR<:-blame-diff-ℓ : ∀ {Γ A} {ℓ ℓ′}
    → ℓ ≢ ℓ′
      ------------------------------------
    → CastsRespect<: (blame {Γ} {A} ℓ′) ℓ
