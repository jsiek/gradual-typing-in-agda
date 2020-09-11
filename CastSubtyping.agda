module CastSubtyping where



open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂; inspect; [_])
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)

open import SimpleCast using (Cast; Active; Cross; applyCast; pcs; cs; dom; cod; fstC; sndC; inlC; inrC)
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast
import ParamCastAux
open ParamCastAux pcs using (Value; Frame; plug; canonical⋆)
import ParamCastReduction
open ParamCastReduction cs


open Active
open Cast
open Frame


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


-- A few lemmas about `<:` :
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

  {- NOTE:
    If the cast has the same blame label as ℓ , which is what the data type is quantified over,
    we require that the source & target types respect subtyping <: .
  -}
  CR<:-cast-same-ℓ : ∀ {Γ S T} {S~T : S ~ T} {M : Γ ⊢ S} {ℓ}
    → (S<:T : S <: T)
    → CastsRespect<: M ℓ
      -------------------------------------
    → CastsRespect<: (M ⟨ (S ⇒⟨ ℓ ⟩ T) {S~T} ⟩) ℓ

  {- NOTE:
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


fun~-dom : ∀ {S₁ S₂ T₁ T₂}
  → (S~T : (S₁ ⇒ S₂) ~ (T₁ ⇒ T₂))
  → T₁ ~ S₁
fun~-dom S~T with ~-relevant S~T
... | fun~ T₁~S₁ _ = T₁~S₁

fun~-cod : ∀ {S₁ S₂ T₁ T₂}
  → (S~T : (S₁ ⇒ S₂) ~ (T₁ ⇒ T₂))
  → S₂ ~ T₂
fun~-cod S~T with ~-relevant S~T
... | fun~ _ S₂~T₂ = S₂~T₂

dom-eq : ∀ {S₁ S₂ T₁ T₂} {ℓ}
  → (S~T : (S₁ ⇒ S₂) ~ (T₁ ⇒ T₂))
  → (x : Cross ((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)))
  → (dom (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {S~T}) x) ≡ ((T₁ ⇒⟨ ℓ ⟩ S₁) {fun~-dom S~T})
dom-eq S~T x with ~-relevant S~T
... | fun~ _ _ = refl

cod-eq : ∀ {S₁ S₂ T₁ T₂} {ℓ}
  → (S~T : (S₁ ⇒ S₂) ~ (T₁ ⇒ T₂))
  → (x : Cross ((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)))
  → (cod (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {S~T}) x) ≡ ((S₂ ⇒⟨ ℓ ⟩ T₂) {fun~-cod S~T})
cod-eq S~T x with ~-relevant S~T
... | fun~ _ _ = refl

pair~-fst : ∀ {A₁ A₂ B₁ B₂}
  → (A~B : (A₁ `× A₂) ~ (B₁ `× B₂))
  → A₁ ~ B₁
pair~-fst A~B with ~-relevant A~B
... | pair~ A₁~B₁ _ = A₁~B₁

pair~-snd : ∀ {A₁ A₂ B₁ B₂}
  → (A~B : (A₁ `× A₂) ~ (B₁ `× B₂))
  → A₂ ~ B₂
pair~-snd A~B with ~-relevant A~B
... | pair~ _ A₂~B₂ = A₂~B₂

fstC-eq : ∀ {A₁ A₂ B₁ B₂} {ℓ}
  → (A~B : (A₁ `× A₂) ~ (B₁ `× B₂))
  → (x : Cross ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))
    -----------------------------------------------
  → (fstC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {A~B}) x) ≡ ((A₁ ⇒⟨ ℓ ⟩ B₁) {pair~-fst A~B}) -- here we use a helper to destruct A~B
fstC-eq A~B x with ~-relevant A~B
... | pair~ _ _ = refl

sndC-eq : ∀ {A₁ A₂ B₁ B₂} {ℓ}
  → (A~B : (A₁ `× A₂) ~ (B₁ `× B₂))
  → (x : Cross ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))
    ------------------------------------------------
  → (sndC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {A~B}) x) ≡ ((A₂ ⇒⟨ ℓ ⟩ B₂) {pair~-snd A~B})
sndC-eq A~B x with ~-relevant A~B
... | pair~ _ _ = refl

sum~-inl : ∀ {A₁ A₂ B₁ B₂}
  → (A~B : (A₁ `⊎ A₂) ~ (B₁ `⊎ B₂))
  → A₁ ~ B₁
sum~-inl A~B with ~-relevant A~B
... | sum~ A₁~B₁ _ = A₁~B₁

sum~-inr : ∀ {A₁ A₂ B₁ B₂}
  → (A~B : (A₁ `⊎ A₂) ~ (B₁ `⊎ B₂))
  → A₂ ~ B₂
sum~-inr A~B with ~-relevant A~B
... | sum~ _ A₂~B₂ = A₂~B₂

inlC-eq : ∀ {A₁ A₂ B₁ B₂} {ℓ}
  → (A~B : (A₁ `⊎ A₂) ~ (B₁ `⊎ B₂))
  → (x : Cross ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))
    -----------------------------------------------
  → (inlC (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {A~B}) x) ≡ ((A₁ ⇒⟨ ℓ ⟩ B₁) {sum~-inl A~B})
inlC-eq A~B x with ~-relevant A~B
... | sum~ _ _ = refl

inrC-eq : ∀ {A₁ A₂ B₁ B₂} {ℓ}
  → (A~B : (A₁ `⊎ A₂) ~ (B₁ `⊎ B₂))
  → (x : Cross ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))
    -----------------------------------------------
  → (inrC (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {A~B}) x) ≡ ((A₂ ⇒⟨ ℓ ⟩ B₂) {sum~-inr A~B})
inrC-eq A~B x with ~-relevant A~B
... | sum~ _ _ = refl

{- Applying (an active) cast on a value preserves CastsRespect<: . -}
-- If the cast has the same blame label with the one that CR<: is quantified with :
applyCast-same-ℓ-pres-CR<: : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {ℓ}
    → (A~B : A ~ B)
    → (a : Active ((A ⇒⟨ ℓ ⟩ B) {A~B})) -- Since the cast can apply, it need to active.
    → A <: B         -- We require A <: B since the label on the cast is the same as the one CR<: is quantified with.
    → (resp-V : CastsRespect<: V ℓ)
      -----------------------------------------------------
    → CastsRespect<: (applyCast V vV (A ⇒⟨ ℓ ⟩ B) {a}) ℓ
applyCast-same-ℓ-pres-CR<: _ (activeId (A ⇒⟨ ℓ ⟩ A)) A<:B resp-V = resp-V
-- For simple cast, the key observation here is that B must be ⋆ .
applyCast-same-ℓ-pres-CR<: {V = V} {vV} A~B (activeProj (⋆ ⇒⟨ ℓ ⟩ B) x) T<:⋆ resp-V
  with canonical⋆ V vV
... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A′ `~ B
...   | no _ = CR<:-blame-diff-ℓ (λ _ → x refl)
...   | yes _ with resp-V
...     | CR<:-cast-same-ℓ _ resp-M′ = CR<:-cast-same-ℓ T<:⋆ resp-M′
...     | CR<:-cast-diff-ℓ _ resp-M′ = CR<:-cast-same-ℓ T<:⋆ resp-M′
applyCast-same-ℓ-pres-CR<: A~B (activeFun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) (<:-⇒ B₁<:A₁ A₂<:B₂) resp-V
  rewrite dom-eq A~B (Cross.C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) | cod-eq A~B (Cross.C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) =
    -- We need to prove renaming preserves CR<: .
    CR<:-ƛ (CR<:-cast-same-ℓ A₂<:B₂ (CR<:-· {!!} (CR<:-cast-same-ℓ B₁<:A₁ CR<:-var)))
applyCast-same-ℓ-pres-CR<: A~B (activePair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) (<:-× A₁<:B₁ A₂<:B₂) resp-V
  rewrite fstC-eq A~B (Cross.C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) | sndC-eq A~B (Cross.C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) =
  -- Prove CastsRespect<: (cons (fst V ⟨ fstC c x ⟩) (snd V ⟨ sndC c x ⟩)) ℓ
    CR<:-cons (CR<:-cast-same-ℓ A₁<:B₁ (CR<:-fst resp-V)) (CR<:-cast-same-ℓ A₂<:B₂ (CR<:-snd resp-V))
applyCast-same-ℓ-pres-CR<: A~B (activeSum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) (<:-⊎ A₁<:B₁ A₂<:B₂) resp-V
  rewrite inlC-eq A~B (Cross.C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) | inrC-eq A~B (Cross.C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) =
    CR<:-case resp-V (CR<:-ƛ (CR<:-inl (CR<:-cast-same-ℓ A₁<:B₁ CR<:-var))) (CR<:-ƛ (CR<:-inr (CR<:-cast-same-ℓ A₂<:B₂ CR<:-var)))

-- This handles the other case when the blame label on the cast is different from the one that CR<: is quantified with :
applyCast-diff-ℓ-pres-CR<: : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {ℓ ℓ′}
    → (A~B : A ~ B)
    → (a : Active ((A ⇒⟨ ℓ′ ⟩ B) {A~B})) -- Since the cast can apply, it need to active.
    → ℓ ≢ ℓ′
    → (resp-V : CastsRespect<: V ℓ)
      -----------------------------------------------------
    → CastsRespect<: (applyCast V vV (A ⇒⟨ ℓ′ ⟩ B) {a}) ℓ
applyCast-diff-ℓ-pres-CR<: _ (activeId (A ⇒⟨ ℓ′ ⟩ A)) ℓ≢ℓ′ resp-V = resp-V
applyCast-diff-ℓ-pres-CR<: {V = V} {vV} {ℓ} A~B (activeProj (⋆ ⇒⟨ ℓ′ ⟩ B) x) ℓ≢ℓ′ resp-V
  with canonical⋆ V vV
... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A′ `~ B
...   | no _ = CR<:-blame-diff-ℓ ℓ≢ℓ′
...   | yes _ with resp-V
...     | CR<:-cast-same-ℓ _ resp-M′ = CR<:-cast-diff-ℓ ℓ≢ℓ′ resp-M′
...     | CR<:-cast-diff-ℓ _ resp-M′ = CR<:-cast-diff-ℓ ℓ≢ℓ′ resp-M′
applyCast-diff-ℓ-pres-CR<: A~B (activeFun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) ℓ≢ℓ′ resp-V
  rewrite dom-eq A~B (Cross.C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) | cod-eq A~B (Cross.C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) =
    -- We need to prove renaming preserves CR<: .
    CR<:-ƛ (CR<:-cast-diff-ℓ ℓ≢ℓ′ (CR<:-· {!!} (CR<:-cast-diff-ℓ ℓ≢ℓ′ CR<:-var)))
applyCast-diff-ℓ-pres-CR<: A~B (activePair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) ℓ≢ℓ′ resp-V
  rewrite fstC-eq A~B (Cross.C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) | sndC-eq A~B (Cross.C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) =
  -- Prove CastsRespect<: (cons (fst V ⟨ fstC c x ⟩) (snd V ⟨ sndC c x ⟩)) ℓ
    CR<:-cons (CR<:-cast-diff-ℓ ℓ≢ℓ′ (CR<:-fst resp-V)) (CR<:-cast-diff-ℓ ℓ≢ℓ′ (CR<:-snd resp-V))
applyCast-diff-ℓ-pres-CR<: A~B (activeSum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) ℓ≢ℓ′ resp-V
  rewrite inlC-eq A~B (Cross.C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) | inrC-eq A~B (Cross.C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) =
    CR<:-case resp-V (CR<:-ƛ (CR<:-inl (CR<:-cast-diff-ℓ ℓ≢ℓ′ CR<:-var))) (CR<:-ƛ (CR<:-inr (CR<:-cast-diff-ℓ ℓ≢ℓ′ CR<:-var)))



plug-blame-CR<:-inv : ∀ {Γ A B} {F : Frame {Γ = Γ} A B} {ℓ ℓ′}
  → CastsRespect<: (plug (blame ℓ′) F) ℓ
    -------------------------------------
  → ℓ ≢ ℓ′
plug-blame-CR<:-inv {F = F-·₁ _} (CR<:-· (CR<:-blame-diff-ℓ ℓ≢ℓ′) _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-·₂ _} (CR<:-· _ (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-if _ _} (CR<:-if (CR<:-blame-diff-ℓ ℓ≢ℓ′) _ _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-×₁ _} (CR<:-cons _ (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-×₂ _} (CR<:-cons (CR<:-blame-diff-ℓ ℓ≢ℓ′) _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-fst} (CR<:-fst (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-snd} (CR<:-snd (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-inl} (CR<:-inl (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-inr} (CR<:-inr (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-case _ _} (CR<:-case (CR<:-blame-diff-ℓ ℓ≢ℓ′) _ _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-cast .(_ ⇒⟨ _ ⟩ _)} (CR<:-cast-same-ℓ _ (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-cast .(_ ⇒⟨ _ ⟩ _)} (CR<:-cast-diff-ℓ _ (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′

{-
  We need to prove preservation w.r.t `CastsRespect<:` .
-}
preserve-CR<:-plug : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B} {ℓ}
  → CastsRespect<: (plug M F) ℓ
  → M —→ M′
    -----------------------------
  → CastsRespect<: (plug M′ F) ℓ

preserve-CR<: : ∀ {Γ A} {M M′ : Γ ⊢ A} {ℓ}
    → CastsRespect<: M ℓ
    → M —→ M′
      --------------------
    → CastsRespect<: M′ ℓ

preserve-CR<:-plug {M = L} {L′} {F = F-·₁ M} (CR<:-· resp-L resp-M) rd = CR<:-· (preserve-CR<: resp-L rd) resp-M
preserve-CR<:-plug {F = F-·₂ L {v}} (CR<:-· resp-L resp-M) rd = CR<:-· resp-L (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-if M N} (CR<:-if resp-L resp-M resp-N) rd = CR<:-if (preserve-CR<: resp-L rd ) resp-M resp-N
preserve-CR<:-plug {F = F-×₁ M} (CR<:-cons resp-M resp-N) rd = CR<:-cons resp-M (preserve-CR<: resp-N rd)
preserve-CR<:-plug {F = F-×₂ N} (CR<:-cons resp-M resp-N) rd = CR<:-cons (preserve-CR<: resp-M rd) resp-N
preserve-CR<:-plug {F = F-fst} (CR<:-fst resp-M) rd = CR<:-fst (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-snd} (CR<:-snd resp-M) rd = CR<:-snd (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-inl} (CR<:-inl resp-M) rd = CR<:-inl (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-inr} (CR<:-inr resp-M) rd = CR<:-inr (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-case M N} (CR<:-case resp-L resp-M resp-N) rd = CR<:-case (preserve-CR<: resp-L rd) resp-M resp-N
preserve-CR<:-plug {F = F-cast c} (CR<:-cast-same-ℓ sub resp-M) rd = CR<:-cast-same-ℓ sub (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-cast c} (CR<:-cast-diff-ℓ neq resp-M) rd = CR<:-cast-diff-ℓ neq (preserve-CR<: resp-M rd)

preserve-CR<: resp (ξ rd) = preserve-CR<:-plug resp rd
preserve-CR<: resp ξ-blame = CR<:-blame-diff-ℓ (plug-blame-CR<:-inv resp)
preserve-CR<: resp (β v) = {!!}
preserve-CR<: resp δ = CR<:-prim
preserve-CR<: (CR<:-if _ resp-M _) β-if-true = resp-M
preserve-CR<: (CR<:-if _ _ resp-M′) β-if-false = resp-M′
preserve-CR<: (CR<:-fst (CR<:-cons resp-M _)) (β-fst _ _) = resp-M
preserve-CR<: (CR<:-snd (CR<:-cons _ resp-N)) (β-snd _ _) = resp-N
preserve-CR<: (CR<:-case (CR<:-inl resp) resp-M _) (β-caseL x) = CR<:-· resp-M resp
preserve-CR<: (CR<:-case (CR<:-inr resp) _ resp-N) (β-caseR x) = CR<:-· resp-N resp
preserve-CR<: (CR<:-cast-same-ℓ {S~T = S~T} S<:T resp) (cast v {a}) =
  applyCast-same-ℓ-pres-CR<: S~T a S<:T resp
preserve-CR<: (CR<:-cast-diff-ℓ {S~T = S~T} ℓ≢ℓ′ resp) (cast v {a}) =
  applyCast-diff-ℓ-pres-CR<: S~T a ℓ≢ℓ′ resp
preserve-CR<: (CR<:-· (CR<:-cast-same-ℓ {S~T = S~T} (<:-⇒ sub-dom sub-cod) resp-V) resp-W) (fun-cast vV vW {x = x})
  rewrite dom-eq S~T x | cod-eq S~T x =
    CR<:-cast-same-ℓ sub-cod (CR<:-· resp-V (CR<:-cast-same-ℓ sub-dom resp-W))
preserve-CR<: (CR<:-· (CR<:-cast-diff-ℓ {S~T = S~T} ℓ≢ resp-V) resp-W) (fun-cast vV vW {x = x})
  rewrite dom-eq S~T x | cod-eq S~T x =
    CR<:-cast-diff-ℓ ℓ≢ (CR<:-· resp-V (CR<:-cast-diff-ℓ ℓ≢ resp-W))
preserve-CR<: (CR<:-fst (CR<:-cast-same-ℓ {S~T = S~T} (<:-× sub-fst sub-snd) resp-V)) (fst-cast vV {x = x})
  rewrite fstC-eq S~T x =
    CR<:-cast-same-ℓ sub-fst (CR<:-fst resp-V)
preserve-CR<: (CR<:-fst (CR<:-cast-diff-ℓ {S~T = S~T} ℓ≢ resp-V)) (fst-cast vV {x = x})
  rewrite fstC-eq S~T x =
    CR<:-cast-diff-ℓ ℓ≢ (CR<:-fst resp-V)
preserve-CR<: (CR<:-snd (CR<:-cast-same-ℓ {S~T = S~T} (<:-× sub-fst sub-snd) resp-V)) (snd-cast vV {x = x})
  rewrite sndC-eq S~T x =
    CR<:-cast-same-ℓ sub-snd (CR<:-snd resp-V)
preserve-CR<: (CR<:-snd (CR<:-cast-diff-ℓ {S~T = S~T} ℓ≢ resp-V)) (snd-cast vV {x = x})
  rewrite sndC-eq S~T x =
    CR<:-cast-diff-ℓ ℓ≢ (CR<:-snd resp-V)
preserve-CR<: (CR<:-case (CR<:-cast-same-ℓ {S~T = S~T} (<:-⊎ sub-l sub-r) resp-V) resp-W₁ resp-W₂) (case-cast vV {x = x})
  rewrite inlC-eq S~T x | inrC-eq S~T x =
    CR<:-case resp-V (CR<:-ƛ (CR<:-· {!!} (CR<:-cast-same-ℓ sub-l CR<:-var))) (CR<:-ƛ (CR<:-· {!!} (CR<:-cast-same-ℓ sub-r CR<:-var)))
preserve-CR<: (CR<:-case (CR<:-cast-diff-ℓ {S~T = S~T} ℓ≢ resp-V) resp-W₁ resp-W₂) (case-cast vV {x = x})
  rewrite inlC-eq S~T x | inrC-eq S~T x =
    CR<:-case resp-V (CR<:-ƛ (CR<:-· {!!} (CR<:-cast-diff-ℓ ℓ≢ CR<:-var))) (CR<:-ƛ (CR<:-· {!!} (CR<:-cast-diff-ℓ ℓ≢ CR<:-var)))
