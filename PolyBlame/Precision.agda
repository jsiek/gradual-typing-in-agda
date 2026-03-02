{-# OPTIONS --rewriting #-}

module PolyBlame.Precision where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.List.Properties using (map-∘)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Bool

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import PolyBlame.Types
open import PolyBlame.TypeSubst
open import PolyBlame.TypePrecision
open import PolyBlame.Variables
open import PolyBlame.Terms
open import PolyBlame.Coercions
open import PolyBlame.ConsistentSubtyping
open import PolyBlame.Gradual
open import PolyBlame.Compile

postulate
  subᵗ-prec : ∀{Δ}{Σ : BindCtx Δ}{A B : Type (Δ ,typ)}{X}
    → (Δ ,typ) ∣ ⤊ Σ ⊢ A ⊑ B
    → Δ ∣ Σ ⊢ A [ X ]ᵗ ⊑ (B [ X ]ᵗ)

_⊆_ : ∀{Δ} (Σ Σ′ : BindCtx Δ) → Set
Σ ⊆ Σ′ = (∀ X → Σ ∋ X := ★ → Σ′ ∋ X := ★)

postulate
  lift-⊆ : ∀{Δ}{Σ Σ′ : BindCtx Δ}
     → Σ ⊆ Σ′
     → ⤊ Σ ⊆ ⤊ Σ′

extend-⊆ : ∀{Δ}{Σ Σ′ : BindCtx Δ}
   → Σ ⊆ Σ′
   → ((Zᵗ , ★) ∷ ⤊ Σ) ⊆ ((Zᵗ , ★) ∷ ⤊ Σ′)
extend-⊆ Σ⊆Σ′ Zᵗ ∋X = (Zᵇ refl refl)
extend-⊆ Σ⊆Σ′ (Sᵗ X) (Sᵇ ∋X) = Sᵇ (lift-⊆ Σ⊆Σ′ (Sᵗ X) ∋X)

extend-right-⊆ : ∀{Δ}{Σ Σ′ : BindCtx Δ}
   → Σ ⊆ Σ′
   → ⤊ Σ ⊆ ((Zᵗ , ★) ∷ ⤊ Σ′)
extend-right-⊆ Σ⊆Σ′ Zᵗ ∋X = Zᵇ refl refl
extend-right-⊆ {Δ}{Σ}{Σ′} Σ⊆Σ′ (Sᵗ X) ∋X = Sᵇ (lift-⊆ Σ⊆Σ′ (Sᵗ X) ∋X)

★-≲→★-⊑ : ∀{Δ}{Σ Σ′} (A : Type Δ)
   → Δ ∣ Σ ⊢ ★ ≲ A
   → Σ ⊆ Σ′
   → Δ ∣ Σ′ ⊢ ★ ⊑ A
   
≲-★→★-⊑ : ∀{Δ}{Σ Σ′} (A : Type Δ)
   → Δ ∣ Σ ⊢ A ≲ ★
   → Σ ⊆ Σ′
   → Δ ∣ Σ′ ⊢ ★ ⊑ A

★-≲→★-⊑ `ℕ ★≲A Σ⊆Σ′ = ★⊑ℕ
★-≲→★-⊑ ★ ★≲A Σ⊆Σ′ = ★⊑★
★-≲→★-⊑ (` x) (★≲X x₁) Σ⊆Σ′ = ★⊑X (Σ⊆Σ′ x x₁)
★-≲→★-⊑ (A ⇒ A₁) (★≲⇒ ★≲A ★≲A₁) Σ⊆Σ′ = ★⊑⇒ (≲-★→★-⊑ A ★≲A Σ⊆Σ′) (★-≲→★-⊑ A₁ ★≲A₁ Σ⊆Σ′)
★-≲→★-⊑ (`∀ A) (≲∀ ★≲A) Σ⊆Σ′ = ⊑∀ (★-≲→★-⊑ A ★≲A (extend-right-⊆ Σ⊆Σ′))

≲-★→★-⊑ {Δ} {Σ} `ℕ A≲★ Σ⊆Σ′ = ★⊑ℕ
≲-★→★-⊑ {Δ} {Σ} ★ A≲★ Σ⊆Σ′ = ★⊑★
≲-★→★-⊑ {Δ} {Σ} (` X) (X≲★ ∋X) Σ⊆Σ′ = ★⊑X (Σ⊆Σ′ X ∋X)
≲-★→★-⊑ {Δ} {Σ} (A ⇒ B) (⇒≲★ A≲★ A≲★₁) Σ⊆Σ′ = ★⊑⇒ (★-≲→★-⊑ A A≲★ Σ⊆Σ′) (≲-★→★-⊑ B A≲★₁ Σ⊆Σ′)
≲-★→★-⊑ {Δ} {Σ} (`∀ A) (∀≲ A≲★) Σ⊆Σ′ = ⊑∀ (≲-★→★-⊑ A A≲★ (extend-⊆ Σ⊆Σ′))

≲⇒-⊑-≲⇒ : ∀ {Δ}{Σ}{Σ′} {A A′ B B′ : Type Δ}
  → (Δ ∣ Σ ⊢ A ⊑ A′)
  → (Δ ∣ Σ ⊢ B ⊑ B′)
  → (ab : Δ ∣ Σ ⊢ A ≲ B)
  → (ab′ : Δ ∣ Σ′ ⊢ A′ ≲ B′)
  → Δ ∣ Σ ∣ Σ′ ⊩ ≲-⇒ Σ ab ⊑ ≲-⇒ Σ′ ab′
{-
  case on A′ ≲ B′, then A ⊑ A′ and B ⊑ B′, and finally on A ≲ B.
-}
≲⇒-⊑-≲⇒ ℕ⊑ℕ ℕ⊑ℕ ℕ≲ℕ ℕ≲ℕ = atom-⊑ ℕ⊑ℕ ℕ⊑ℕ a-id (λ ())
≲⇒-⊑-≲⇒ ℕ⊑ℕ ★⊑ℕ ℕ≲★ ℕ≲ℕ = atom-⊑ ℕ⊑ℕ ★⊑ℕ a-inj (λ ())
≲⇒-⊑-≲⇒ ★⊑ℕ ℕ⊑ℕ ★≲ℕ ℕ≲ℕ = atom-⊑ ★⊑ℕ ℕ⊑ℕ a-proj (λ ())
≲⇒-⊑-≲⇒ ★⊑ℕ ★⊑ℕ ★≲★ ℕ≲ℕ = atom-⊑ ★⊑ℕ ★⊑ℕ a-id (λ ())
≲⇒-⊑-≲⇒ X⊑X X⊑X X≲X X≲X = atom-⊑ X⊑X X⊑X a-id (λ ())
≲⇒-⊑-≲⇒ {Δ}{Σ}{Σ′} (X⊑X{X = X}) (★⊑X ∋x) (X≲★ ∋x₂) X≲X
  with lookup-★ Σ X
... | yes p = atom-⊑ X⊑X (★⊑X p) a-unseal (λ ())
... | no np = ⊥-elim (np ∋x)
≲⇒-⊑-≲⇒ {Δ}{Σ}{Σ′} (★⊑X ∋x) (X⊑X{X = X}) (★≲X ∋x₁) X≲X
  with lookup-★ Σ X
... | yes p = atom-⊑ (★⊑X p) X⊑X a-seal (λ ())
... | no np = ⊥-elim (np ∋x)
≲⇒-⊑-≲⇒ (★⊑X ∋x) (★⊑X x₁) ★≲★ (X≲X{X = X}) = atom-⊑ (★⊑X ∋x) (★⊑X ∋x) a-id (λ ())
≲⇒-⊑-≲⇒ ★⊑★ ★⊑★ ★≲★ ★≲★ = atom-⊑ ★⊑★ ★⊑★ a-id (λ ())
≲⇒-⊑-≲⇒ {Δ}{Σ}{Σ′} ★⊑★ (X⊑X{X = X}) (★≲X ∋x) (★≲X x)
  with lookup-★ Σ X
... | no np = ⊥-elim (np ∋x)
... | yes p
    with lookup-★ Σ′ X
... | no np′ = ⊥-elim (np′ x)
... | yes p′ = atom-⊑ ★⊑★ X⊑X a-seal (λ ())
≲⇒-⊑-≲⇒ {Δ}{Σ}{Σ′} ★⊑★ (★⊑X{X = X} ∋x) ★≲★ (★≲X x)
    with lookup-★ Σ′ X
... | no np′ = ⊥-elim (np′ x)
... | yes p′ = atom-⊑ ★⊑★ (★⊑X ∋x) a-id (λ ())
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (X⊑X{X = X}) ★⊑★ (X≲★ ∋x) (X≲★ ∋x′)
  with lookup-★ Σ X
... | no np = ⊥-elim (np ∋x)
... | yes p
    with lookup-★ Σ′ X
... | no np′ = ⊥-elim (np′ ∋x′)
... | yes p′ = atom-⊑ X⊑X ★⊑★ a-unseal (λ ())
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (★⊑X{X = X} x₁) ★⊑★ ★≲★ (X≲★ x)
    with lookup-★ Σ′ X
... | no np′ = ⊥-elim (np′ x)
... | yes p′ = atom-⊑ (★⊑X x₁) ★⊑★ a-id (λ ())
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} ★⊑★ ℕ⊑ℕ ★≲ℕ ★≲ℕ = atom-⊑ ★⊑★ ℕ⊑ℕ a-proj (λ ())
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} ★⊑★ ★⊑ℕ ★≲★ ★≲ℕ = atom-⊑ ★⊑★ ★⊑ℕ a-id (λ ())
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} ℕ⊑ℕ ★⊑★ ℕ≲★ ℕ≲★ = atom-⊑ ℕ⊑ℕ ★⊑★ a-inj (λ ())
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} ★⊑ℕ ★⊑★ ★≲★ ℕ≲★ = atom-⊑ ★⊑ℕ ★⊑★ a-id (λ ())
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (★⊑⇒ A⊑A′ A⊑A′₁) ★⊑★ ★≲★ (⇒≲★ A′≲B′ A′≲B′₁) =
  ⊑-⨟-1 (atom-⊑ (★⊑⇒ A⊑A′ A⊑A′₁) (★⊑⇒ ★⊑★ ★⊑★) a-id (λ ())) (atom-⊑ (★⊑⇒ ★⊑★ ★⊑★) ★⊑★ a-id (λ ()))
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} {A = A₁ ⇒ A₂}{A′ = A′₁ ⇒ A′₂}{★}{★} (⇒⊑⇒ A₁⊑A′₁ A₂⊑A′₂) ★⊑★
   (⇒≲★ ★≲A₁ A₂≲★) (⇒≲★ ★≲A′₁ A′₂≲★) =
   ⨟-⊑-⨟ (↦-⊑-↦ (≲⇒-⊑-≲⇒ ★⊑★ A₁⊑A′₁ ★≲A₁ ★≲A′₁) (≲⇒-⊑-≲⇒ A₂⊑A′₂ ★⊑★ A₂≲★ A′₂≲★))
         (atom-⊑ (⇒⊑⇒ ★⊑★ ★⊑★) ★⊑★ a-inj (λ ())) 
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} ★⊑★ (★⊑⇒ B⊑B′ B⊑B′₁) ★≲★ (★≲⇒ A′≲B′ A′≲B′₁) =
  ⊑-⨟-1 (atom-⊑ ★⊑★ (★⊑⇒ ★⊑★ ★⊑★) a-id (λ ())) (atom-⊑ (★⊑⇒ ★⊑★ ★⊑★) (★⊑⇒ B⊑B′ B⊑B′₁) a-id (λ ()))
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} ★⊑★ (⇒⊑⇒ B⊑B′ B⊑B′₁) (★≲⇒ A≲B A≲B₁) (★≲⇒ A′≲B′ A′≲B′₁) =
  ⨟-⊑-⨟ (atom-⊑ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★) a-proj (λ ()))
        (↦-⊑-↦ (≲⇒-⊑-≲⇒ B⊑B′ ★⊑★ A≲B A′≲B′)
                (≲⇒-⊑-≲⇒ ★⊑★ B⊑B′₁ A≲B₁ A′≲B′₁))
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (★⊑⇒ A⊑A′ A⊑A′₁) (★⊑⇒ B⊑B′ B⊑B′₁) ★≲★ (⇒≲⇒ A′≲B′ A′≲B′₁) =
  atom-⊑ (★⊑⇒ A⊑A′ A⊑A′₁) (★⊑⇒ B⊑B′ B⊑B′₁) a-id (λ ())
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} {A = ★} {A′ = A′₁ ⇒ A′₂} {B = B₁ ⇒ B₂} {B′ = B′₁ ⇒ B′₂} (★⊑⇒ ★⊑A′₁ ★⊑A′₂) (⇒⊑⇒ B₁⊑B′₁ B₂⊑B′₂) (★≲⇒ B₁≲★ ★≲B₂) (⇒≲⇒ A′≲B′ A′≲B′₁) =
  ⨟-⊑-1 (atom-⊑ (★⊑⇒ ★⊑A′₁ ★⊑A′₂) (⇒⊑⇒ ★⊑A′₁ ★⊑A′₂) a-proj (λ ())) (↦-⊑-↦ (≲⇒-⊑-≲⇒ B₁⊑B′₁ ★⊑A′₁ B₁≲★ A′≲B′) (≲⇒-⊑-≲⇒ ★⊑A′₂ B₂⊑B′₂ ★≲B₂ A′≲B′₁))
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (⇒⊑⇒ A⊑A′ A⊑A′₁) (★⊑⇒ B⊑B′ B⊑B′₁) (⇒≲★ A≲B A≲B₁) (⇒≲⇒ A′≲B′ A′≲B′₁) =
  ⨟-⊑-2 (↦-⊑-↦ (≲⇒-⊑-≲⇒ B⊑B′ A⊑A′ A≲B A′≲B′) (≲⇒-⊑-≲⇒ A⊑A′₁ B⊑B′₁ A≲B₁ A′≲B′₁))
        (atom-⊑ (⇒⊑⇒ B⊑B′ B⊑B′₁) (★⊑⇒ B⊑B′ B⊑B′₁) a-inj (λ ()))
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (⇒⊑⇒ A⊑A′ A⊑A′₁) (⇒⊑⇒ B⊑B′ B⊑B′₁) (⇒≲⇒ A≲B A≲B₁) (⇒≲⇒ A′≲B′ A′≲B′₁) =
  ↦-⊑-↦ (≲⇒-⊑-≲⇒ B⊑B′ A⊑A′ A≲B A′≲B′) (≲⇒-⊑-≲⇒ A⊑A′₁ B⊑B′₁ A≲B₁ A′≲B′₁)
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (∀⊑∀ A⊑A′) (∀⊑∀ B⊑B′) (∀≲∀ A≲B) (∀≲∀ A′≲B′) = ∀-⊑-∀ (≲⇒-⊑-≲⇒ A⊑A′ B⊑B′ A≲B A′≲B′)
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} {`∀ A}{`∀ A′}{`∀ B}{`∀ B′} (∀⊑∀ A⊑A′) (∀⊑∀ B⊑B′) (≲∀ c) (∀≲∀ d) =
  let IH = ≲⇒-⊑-≲⇒ {!!} {!!} {!!} {!!} in
  𝒢-⊑-∀ {!!} -- 𝒢-⊑-∀ (≲⇒-⊑-≲⇒ {!!} {!!} {!!} {!!})
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (∀⊑∀ A⊑A′) (∀⊑∀ B⊑B′) (∀≲ A≲B) (∀≲∀ A′≲B′) = {!!}
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (∀⊑∀ A⊑A′) (⊑∀ B⊑B′) A≲B (∀≲∀ A′≲B′) = {!!}
≲⇒-⊑-≲⇒ {Δ} {Σ} {Σ′} (⊑∀ A⊑A′) B⊑B′ A≲B (∀≲∀ A′≲B′) = {!!}
≲⇒-⊑-≲⇒ {Δ}{Σ}{Σ′} A⊑A′ B⊑B′ A≲B (≲∀ A′≲B′) = {!!}
≲⇒-⊑-≲⇒ {Δ}{Σ}{Σ′} A⊑A′ B⊑B′ A≲B (∀≲ A′≲B′) = {!!}

{-
  Coercion less precise than a type
  (Replace this with coercion less precise than an id coercion.)
 -}
-- infix 3 _∣_⊩_⊑_
-- data _∣_⊩_⊑_ : ∀(Δ : TyCtx)(Σ : BindCtx Δ){A B : Type Δ}
--   → (Δ ∣ Σ ⊢ A ⇒ B) → (Type Δ)
--   →  Set  where

--   id-⊑ : ∀{Δ}{Σ}{A : Type Δ}
--       ------------------------
--      → Δ ∣ Σ ⊩  id{A = A}  ⊑ A

--   ↦-⊑ : ∀{Δ}{Σ}{A B C D E F : Type Δ}
--        {c : Δ ∣ Σ ⊢ C ⇒ A }
--        {d : Δ ∣ Σ ⊢ B ⇒ D }
--      → Δ ∣ Σ ⊩ c ⊑ E
--      → Δ ∣ Σ ⊩ d ⊑ F
--        --------------------------
--      → Δ ∣ Σ ⊩ (c ↦ d) ⊑ (E ⇒ F)

--   ⨟-⊑ : ∀{Δ}{Σ}{A B C D : Type Δ}
--        {c : Δ ∣ Σ ⊢ A ⇒ B }
--        {d : Δ ∣ Σ ⊢ B ⇒ C }
--      → Δ ∣ Σ ⊩ c ⊑ D
--      → Δ ∣ Σ ⊩ d ⊑ D
--        --------------------------
--      → Δ ∣ Σ ⊩ (c ⨟ d) ⊑ D

--   !-⊑ : ∀{Δ}{Σ}{B : Type Δ}{G : Grnd Δ}
--      → Δ ∣ Σ ⊢ ⌈ G ⌉ ⊑ B
--       ---------------------
--      → Δ ∣ Σ ⊩ (G !) ⊑ B

--   ?-⊑ : ∀{Δ}{Σ}{B : Type Δ}{G : Grnd Δ}
--      → Δ ∣ Σ ⊢ ⌈ G ⌉ ⊑ B
--       ---------------------
--      → Δ ∣ Σ ⊩ (G `?) ⊑ B


-- -- ★-⊑-FV-⊆ : ∀{Δ}{Ψ : SubCtx Δ}{A : Type Δ}
-- --   → Δ ∣ Ψ ⊢ ★ ⊑ A
-- --   → FV A ⊆ Ψ
-- -- ★-⊑-FV-⊆ {Δ} {Ψ} {A} ★⊑★ = mt-⊆
-- -- ★-⊑-FV-⊆ {Δ} {Ψ} {A} (★⊑X ∋X) = ∋-single-⊆ ∋X
-- -- ★-⊑-FV-⊆ {Δ} {Ψ} {A} ★⊑ℕ = mt-⊆
-- -- ★-⊑-FV-⊆ {Δ} {Ψ} {A ⇒ B} (★⊑⇒ ★⊑A ★⊑B) =
-- --   let IH1 = ★-⊑-FV-⊆ ★⊑A in
-- --   let IH2 = ★-⊑-FV-⊆ ★⊑B in
-- --   ⊆-∪ IH1 IH2
-- -- ★-⊑-FV-⊆ {Δ} {Ψ} {A} (⊑∀ ★⊑A) = ⊆-⤋ (★-⊑-FV-⊆ ★⊑A)

-- -- ★⇒★-⊑-FV-⊆ : ∀{Δ}{Ψ : SubCtx Δ}{A : Type Δ}
-- --   → Δ ∣ Ψ ⊢ (★ ⇒ ★) ⊑ A
-- --   → FV A ⊆ Ψ
-- -- ★⇒★-⊑-FV-⊆ {Δ} {Ψ} {A ⇒ B} (⇒⊑⇒ ★⊑A ★⊑B) =
-- --   ⊆-∪ (★-⊑-FV-⊆ ★⊑A) (★-⊑-FV-⊆ ★⊑B)
-- -- ★⇒★-⊑-FV-⊆ {Δ} {Ψ} {`∀ A} (⊑∀ ★⇒★⊑A) =
-- --   ⊆-⤋ (★⇒★-⊑-FV-⊆ ★⇒★⊑A)

-- -- ★⇒★-⊑ : ∀{Δ}{Ψ : SubCtx Δ}{A : Type Δ}
-- --   → Δ ∣ Ψ ⊢ (★ ⇒ ★) ⊑ A
-- --   → Σ[ A₁ ∈ Type Δ ] Σ[ A₂ ∈ Type Δ ]
-- --     Δ ∣ Ψ ⊢ ★ ⊑ A₁  ×  Δ ∣ Ψ ⊢ ★ ⊑ A₂
-- -- ★⇒★-⊑ {Δ} {Ψ} {A} (⇒⊑⇒ ★⊑C ★⊑D) = _ , _ , ★⊑C , ★⊑D
-- -- ★⇒★-⊑ {Δ} {Ψ} {A} (⊑∀ ★⇒★⊑A) = ★ , ★ , ★⊑★ , ★⊑★

-- -- ℕ-⊑-FV : ∀{Δ}{Ψ : SubCtx Δ}{A : Type Δ}
-- --   → Δ ∣ Ψ ⊢ `ℕ ⊑ A
-- --   → FV A ⊆ mt Δ
-- -- ℕ-⊑-FV {Δ} {Ψ} {`ℕ} ℕ⊑A = mt-⊆
-- -- ℕ-⊑-FV {Δ} {Ψ} {`∀ A} (⊑∀ ℕ⊑A) = ⊆-⤋ (ℕ-⊑-FV ℕ⊑A)

-- {-
-- ⇒-⊑-⊑ : ∀{Δ}{Σ : BindCtx Δ}{A B C : Type Δ}
--     (c : Δ ∣ Σ ⊢ A ⇒ B)
--   → Δ ∣ Σ ⊩ c ⊑ C
--   → Δ ∣ mt Δ ⊢ A ⊑ C  ×  Δ ∣ mt Δ ⊢ B ⊑ C
-- ⇒-⊑-⊑ {Δ} {Σ} {A} {B} c id-⊑ = Refl⊑ A , Refl⊑ A
-- ⇒-⊑-⊑ {Δ} {Σ} {A₁ ⇒ A₂} {B₁ ⇒ B₂} {C₁ ⇒ C₂} (c ↦ d) (↦-⊑ c⊑C₁ d⊑C₂) =
--     (⇒⊑⇒ (⇒-⊑-⊑ c c⊑C₁ .proj₂) (⇒-⊑-⊑ d d⊑C₂ .proj₁))
--   , (⇒⊑⇒ (⇒-⊑-⊑ c c⊑C₁ .proj₁) (⇒-⊑-⊑ d d⊑C₂ .proj₂))
-- ⇒-⊑-⊑ {Δ} {Σ} {A} {B} (c ⨟ d) (⨟-⊑ c⊑C c⊑C₁) =
--   ⇒-⊑-⊑ c c⊑C .proj₁ , ⇒-⊑-⊑ d c⊑C₁ .proj₂
-- ⇒-⊑-⊑ {Δ} {Σ} {A} {B} (★⇒★ !) (!-⊑ (⇒⊑⇒ x y)) = ⇒⊑⇒ x y , ★⊑⇒ x y
-- ⇒-⊑-⊑ {Δ} {Σ} {A} {★} (★⇒★ !) (!-⊑ (⊑∀{B = B′} ★⇒★⊑B′)) =
--   let FVB = ★⇒★-⊑-FV-⊆ ★⇒★⊑B′ in
--   let ⤋FVB = ⊆-⤋ FVB in
--   (⊑∀ ★⇒★⊑B′) , (★-⊑ (`∀ _) ⤋FVB)
-- ⇒-⊑-⊑ {Δ} {Σ} {A} {B} {C} (`ℕ !) (!-⊑ ℕ⊑C) = ℕ⊑C , (★-⊑ C (ℕ-⊑-FV ℕ⊑C))
-- ⇒-⊑-⊑ {Δ} {Σ} {A} {B} {C} ((` X) !) (!-⊑ X⊑C) = X⊑C , {!!}
--   {-

--     X  ⊑   C
--     !
--     ★  ⊑  C

--    -}
-- ⇒-⊑-⊑ {Δ} {Σ} {A} {B} {C} c (?-⊑ x) = {!!}
-- -}

-- infix 3 _∣_∣_⊩_⊑_⦂_
-- data _∣_∣_⊩_⊑_⦂_ : ∀{Δ}(Σ Σ′ : BindCtx Δ){A B : Type Δ}{Γ Γ′ : Ctx Δ}
--   → PrecCtx Σ′ Γ Γ′ → (Δ ∣ Σ ∣ Γ ⊢ A) → (Δ ∣ Σ′ ∣ Γ′ ⊢ B)
--   → Δ ∣ Σ′ ⊢ A ⊑ B → Set  where
  
--   ⊑-var : ∀{Δ}{Σ Σ′ : BindCtx Δ}{A B}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--      → (x : ⊢ Φ ∋ A ⊑ B)
--        ---------------------------------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ (` proj-left x) ⊑ (` proj-right x) ⦂ get-⊑ x

--   ⊑-nat : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}{k : ℕ}
--      → Σ ∣ Σ′ ∣ Φ ⊩ (# k) ⊑ (# k) ⦂ ℕ⊑ℕ

--   ⊑-lam : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--       {A B C D : Type Δ}{N : Δ ∣ Σ ∣ (Γ ▷ A) ⊢ B} {N′ : Δ ∣ Σ′ ∣ (Γ′ ▷ C) ⊢ D}
--       {c : Δ ∣ Σ′ ⊢ A ⊑ C}{d : Δ ∣ Σ′ ⊢ B ⊑ D}
--      → Σ ∣ Σ′ ∣ (Φ , c) ⊩ N ⊑ N′ ⦂ d
--        ---------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ ƛ N ⊑ ƛ N′ ⦂ ⇒⊑⇒ c d
  
--   ⊑-app : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--        {A B C D : Type Δ}
--        {L : Δ ∣ Σ ∣ Γ ⊢ A ⇒ B}    {M : Δ ∣ Σ ∣ Γ ⊢ A}
--        {L′ : Δ ∣ Σ′ ∣ Γ′ ⊢ C ⇒ D} {M′ : Δ ∣ Σ′ ∣ Γ′ ⊢ C}
--        {c : Δ ∣ Σ′ ⊢ A ⊑ C}
--        {d : Δ ∣ Σ′ ⊢ B ⊑ D}
--      → Σ ∣ Σ′ ∣ Φ ⊩ L ⊑ L′ ⦂ (⇒⊑⇒ c d)
--      → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ c
--        --------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ L · M ⊑ L′ · M′ ⦂ d
  
--   ⊑-Λ : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--       {A B : Type (Δ ,typ)}{N : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A}
--       {N′ : (Δ ,typ) ∣ ⤊ Σ′ ∣ ⟰ Γ′ ⊢ B}
--       {c : (Δ ,typ) ∣ ⤊ Σ′ ⊢ A ⊑ B}
--      → ⤊ Σ ∣ ⤊ Σ′ ∣ ⟰ᵖ Φ ⊩ N ⊑ N′ ⦂ c
--        --------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ Λ N ⊑ Λ N′ ⦂ ∀⊑∀ c
      
--   ⊑-◯ : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--         {A B : Type (Δ ,typ)}{M : Δ ∣ Σ ∣ Γ ⊢ `∀ A}
--         {M′ : Δ ∣ Σ′  ∣ Γ′ ⊢ `∀ B}{X}
--         {p : (Δ ,typ) ∣ ⤊ Σ′ ⊢ A ⊑ B}
--      → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ ∀⊑∀ p
--        ----------------------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ (M ◯ X) ⊑ (M′ ◯ X) ⦂ subᵗ-prec p

--   ⊑-blame : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--         {A : Type Δ}{M : Δ ∣ Σ ∣ Γ ⊢ A}{M : Δ ∣ Σ ∣ Γ ⊢ A}
--        --------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ blame ⦂ Refl⊑ A

--   ⊑-⟨⟩ : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--         {A B A′ B′ : Type Δ}
--         {M : Δ ∣ Σ ∣ Γ ⊢ A} {c : Δ ∣ Σ ⊢ A ⇒ B}
--         {M′ : Δ ∣ Σ′  ∣ Γ′ ⊢ A′} {c′ : Δ ∣ Σ′ ⊢ A′ ⇒ B′}
--         {A⊑A′ : Δ ∣ Σ′ ⊢ A ⊑ A′}
--         {B⊑B′ : Δ ∣ Σ′ ⊢ B ⊑ B′}
--      → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ A⊑A′
--      → Δ ∣ Σ ∣ Σ′ ⊩ c ⊑ c′
--        ----------------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B⊑B′

--   ⊑-ν : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--         {A B A′ B′ : Type Δ}
--         {M : Δ ,typ ∣ (Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ ∣ ⟰ Γ ⊢ ⇑ᵗ B}
--         {M′ : Δ ,typ ∣ (Zᵗ , ⇑ᵗ A′) ∷ ⤊ Σ′ ∣ ⟰ Γ′ ⊢ ⇑ᵗ B′}
--         {A⊑A′ : (Δ ,typ) ∣ (Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ′ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′}
--         {B⊑B′ : (Δ ,typ) ∣ (Zᵗ , ⇑ᵗ A′) ∷ ⤊ Σ′ ⊢ ⇑ᵗ B ⊑ ⇑ᵗ B′}
--         {B⊑B′₂ : Δ ∣ Σ′ ⊢ B ⊑ B′}
--      → (Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ ∣ (Zᵗ , ⇑ᵗ A′) ∷ ⤊ Σ′ ∣ extend-⊑ Φ A′ ⊩ M ⊑ M′ ⦂ B⊑B′
--        ----------------------------------------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ ν A · M  ⊑ ν A′ · M′ ⦂ B⊑B′₂

-- {-
--   ⊑-⟨⟩-L : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Σ′ Γ Γ′}
--         {A B C : Type Δ}
--         {M : Δ ∣ Σ ∣ Γ ⊢ A}
--         {c : Δ ∣ Σ ⊢ A ⇒ B}
--         {p : Δ ∣ Σ′ ⊢ A ⊑ C}
--         {M′ : Δ ∣ Σ′  ∣ Γ′ ⊢ C}
--      → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ p
--      → Δ ∣ Σ ⊩ c ⊑ C
--        ----------------------------------------------
--      → Σ ∣ Σ′ ∣ Φ ⊩ M ⟨ c ⟩ ⊑ M′ ⦂ {!!}
  
-- -}

-- ⏵⇒-⊑-⏵⇒ : ∀{Δ}{Σ : BindCtx Δ} {A B C A′ B′ C′ : Type Δ}
--   → (Δ ∣ Σ ⊢ C ⊑ C′)
--   → (f : Δ ⊢ C ⏵ (A ⇒ B))
--   → (f′ : Δ ⊢ C′ ⏵ (A′ ⇒ B′))
--   → Δ ∣ [] ∣ [] ⊩ (⏵-⇒ f) ⊑ (⏵-⇒ f′)
-- ⏵⇒-⊑-⏵⇒ cc ⏵-⇒-⇒ ⏵-⇒-⇒ = id-⊑ cc
-- ⏵⇒-⊑-⏵⇒ (★⊑⇒ ★⊑A′ ★⊑B′) ⏵-★-⇒ ⏵-⇒-⇒ = ?-⊑-id (⇒⊑⇒ ★⊑A′ ★⊑B′)
-- ⏵⇒-⊑-⏵⇒ cc ⏵-★-⇒ ⏵-★-⇒ = ?-⊑

-- ⊑-⏵-⏵-⊑ : ∀{Δ}{Σ : BindCtx Δ} {A B C A′ B′ C′ : Type Δ}
--   → (Δ ∣ Σ ⊢ C ⊑ C′)
--   → (Δ ⊢ C ⏵ (A ⇒ B))
--   → (Δ ⊢ C′ ⏵ (A′ ⇒ B′))
--   → Δ ∣ Σ ⊢ A ⊑ A′
-- ⊑-⏵-⏵-⊑ (⇒⊑⇒ cc dd) ⏵-⇒-⇒ ⏵-⇒-⇒ = cc
-- ⊑-⏵-⏵-⊑ (★⊑⇒ cc dd) ⏵-★-⇒ ⏵-⇒-⇒ = cc
-- ⊑-⏵-⏵-⊑ ★⊑★ ⏵-★-⇒ ⏵-★-⇒ = ★⊑★

-- -- id★-⊑-≲⇒ : ∀ {Δ}{Σ Σ′ : BindCtx Δ} {B : Type Δ}
-- --   → (Δ ∣ Σ′ ⊢ ★ ⊑ B)
-- --   → (ab : Δ ∣ Σ′ ⊢ ★ ≲ B)
-- --   → Δ ∣ Σ ∣ Σ′ ⊩ id{A = ★} ⊑ ≲-⇒ Σ′ ab
  
-- -- id★-⊑-≲⇒ {B = `ℕ} ⊑B ★≲ℕ = id-⊑-? ⊑B
-- -- id★-⊑-≲⇒ {B = ★} ⊑B ★≲★ = id-⊑ ⊑B
-- -- id★-⊑-≲⇒ {B = ` x} ⊑B (★≲X x₁) = id-⊑-? ⊑B
-- -- id★-⊑-≲⇒ {Σ = Σ}{B = B ⇒ B₁} (★⊑⇒ ⊑B ⊑B₁) (★≲⇒ ≲B ≲B₁) = 
-- --   ⊑-⨟ (id-⊑-?{Σ = Σ} (★⊑⇒ ★⊑★ ★⊑★))
-- --       (id★-⊑-↦{A = B}{B = B} (id★-⊑-≲⇒ ⊑B ≲B)
-- --        (id★-⊑-≲⇒ ⊑B₁ ≲B₁))
-- -- id★-⊑-≲⇒ {B = `∀ B} (⊑∀ ⊑B) (≲∀ ≲B) = id★-⊑-𝒢 (id★-⊑-≲⇒ ⊑B ≲B)

-- -- id-⊑-≲⇒ : ∀ {Δ}{Σ : BindCtx Δ} {C A′ B′ : Type Δ}
-- --   → (Δ ∣ Σ ⊢ C ⊑ A′)
-- --   → (Δ ∣ Σ ⊢ C ⊑ B′)
-- --   → (ab : Δ ∣ Σ ⊢ A′ ≲ B′)
-- --   → Δ ∣ [] ∣ [] ⊩ id{A = C} ⊑ ≲-⇒ ab []
-- -- id-⊑-≲⇒ ca cb ℕ≲ℕ = id-⊑ ca
-- -- id-⊑-≲⇒ ca cb X≲X = id-⊑ ca
-- -- id-⊑-≲⇒ ca cb ★≲★ = id-⊑ ca
-- -- id-⊑-≲⇒ ★⊑★ cb (★≲X x) = id-⊑-? cb
-- -- id-⊑-≲⇒ (★⊑X x₁) cb (X≲★ x) = id-⊑-! (★⊑X x₁)
-- -- id-⊑-≲⇒ ★⊑★ cb ★≲ℕ = id-⊑-? cb
-- -- id-⊑-≲⇒ ★⊑ℕ cb ℕ≲★ = id-⊑-! ★⊑ℕ
-- -- id-⊑-≲⇒ (★⊑⇒ ca ca₁) ★⊑★ (⇒≲★ ab ab₁) =
-- --   ⊑-⨟ (id★-⊑-↦ (id-⊑-≲⇒ ca ★⊑★ ab)
-- --                 (id-⊑-≲⇒ ca₁ ★⊑★ ab₁))
-- --       (id-⊑-! (★⊑⇒ ★⊑★ ★⊑★))
-- -- id-⊑-≲⇒ ★⊑★ (★⊑⇒ cb cb₁) (★≲⇒ ab ab₁) =
-- --   ⊑-⨟ (id-⊑-? (★⊑⇒ ★⊑★ ★⊑★))
-- --       (id★-⊑-↦ (id★-⊑-≲⇒ cb ab) (id★-⊑-≲⇒ cb₁ ab₁))
-- -- id-⊑-≲⇒ (★⊑⇒ ca ca₁) (★⊑⇒ cb cb₁) (⇒≲⇒ ab ab₁) =
-- --   id★-⊑-↦ (id-⊑-≲⇒ ca cb ab) (id-⊑-≲⇒ ca₁ cb₁ ab₁)
-- -- id-⊑-≲⇒ (⇒⊑⇒ ca ca₁) (⇒⊑⇒ cb cb₁) (⇒≲⇒ ab ab₁) =
-- --   id-⊑-↦ (id-⊑-≲⇒ ca cb ab) (id-⊑-≲⇒ ca₁ cb₁ ab₁)
-- -- id-⊑-≲⇒ ca cb (∀≲∀ ab) = {!!}
-- -- id-⊑-≲⇒ ca cb (≲∀ ab) = {!!}
-- -- id-⊑-≲⇒ ca cb (∀≲ ab) = {!!}

-- postulate 
--   ≲⇒-⊑-≲⇒ : ∀ {Δ} {B C B′ C′ : Type Δ}
--     → (Δ ∣ [] ⊢ B ⊑ B′)
--     → (Δ ∣ [] ⊢ C ⊑ C′)
--     → (bc : Δ ∣ [] ⊢ B ≲ C)
--     → (bc′ : Δ ∣ [] ⊢ B′ ≲ C′)
--     → Δ ∣ [] ∣ [] ⊩ ≲-⇒ [] bc ⊑ ≲-⇒ [] bc′
  
-- -- ≲⇒-⊑-≲⇒ ℕ⊑ℕ ℕ⊑ℕ ℕ≲ℕ ℕ≲ℕ = id-⊑ ℕ⊑ℕ
-- -- ≲⇒-⊑-≲⇒ ℕ⊑ℕ ★⊑★ ℕ≲★ ℕ≲★ = !-⊑
-- -- ≲⇒-⊑-≲⇒ ℕ⊑ℕ ★⊑ℕ ℕ≲★ ℕ≲ℕ = !-⊑-id ℕ⊑ℕ
-- -- ≲⇒-⊑-≲⇒ ℕ⊑ℕ (∀⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ ℕ⊑ℕ (⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ X⊑X X⊑X X≲X X≲X = id-⊑ X⊑X
-- -- ≲⇒-⊑-≲⇒ X⊑X ★⊑★ (X≲★ ∋X) (X≲★ ∋X′) = !-⊑   -- Remember ∋X ?
-- -- ≲⇒-⊑-≲⇒ X⊑X (★⊑X x) (X≲★ x₁) X≲X = !-⊑-id X⊑X
-- -- ≲⇒-⊑-≲⇒ X⊑X (∀⊑∀ cc) (≲∀ bc) (≲∀ bc′) = {!!}
-- -- ≲⇒-⊑-≲⇒ X⊑X (⊑∀ cc) X≲X (≲∀ bc′) = {!!}
-- -- ≲⇒-⊑-≲⇒ X⊑X (⊑∀ cc) (X≲★ x) (≲∀ bc′) = {!!}
-- -- ≲⇒-⊑-≲⇒ X⊑X (⊑∀ cc) (≲∀ bc) bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ ★⊑★ ℕ⊑ℕ ★≲ℕ ★≲ℕ = ?-⊑
-- -- ≲⇒-⊑-≲⇒ ★⊑★ X⊑X (★≲X x) (★≲X x₁) = ?-⊑
-- -- ≲⇒-⊑-≲⇒ ★⊑★ ★⊑★ ★≲★ ★≲★ = id-⊑ ★⊑★
-- -- ≲⇒-⊑-≲⇒ ★⊑★ (★⊑X ∋X) ★≲★ (★≲X x₁) = id-⊑-? (★⊑X x₁)
-- -- ≲⇒-⊑-≲⇒ ★⊑★ ★⊑ℕ ★≲★ ★≲ℕ = id-⊑-? ★⊑ℕ
-- -- ≲⇒-⊑-≲⇒ ★⊑★ (★⊑⇒ cc cc₁) ★≲★ (★≲⇒ bc′ bc′₁) =
-- --   ⊑-⨟ (id-⊑-? (★⊑⇒ ★⊑★ ★⊑★)) (id★-⊑-↦ {!!} {!!})
-- -- ≲⇒-⊑-≲⇒ ★⊑★ (⇒⊑⇒ cc cc₁) (★≲⇒ bc bc₁) (★≲⇒ bc′ bc′₁) =
-- --   ⨟-⊑-⨟ ?-⊑ (↦-⊑ (≲⇒-⊑-≲⇒ ★⊑★ cc bc bc′) (≲⇒-⊑-≲⇒ ★⊑★ cc₁ bc₁ bc′₁))
-- -- ≲⇒-⊑-≲⇒ ★⊑★ (∀⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ ★⊑★ (⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ (★⊑X x) X⊑X (★≲X x₁) X≲X = ?-⊑-id X⊑X
-- -- ≲⇒-⊑-≲⇒ (★⊑X x) ★⊑★ ★≲★ (X≲★ x₁) = id-⊑-! (★⊑X x)
-- -- ≲⇒-⊑-≲⇒ (★⊑X x) (★⊑X x₁) ★≲★ X≲X = id-⊑ (★⊑X x)
-- -- ≲⇒-⊑-≲⇒ (★⊑X x) (∀⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ (★⊑X x) (⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ ★⊑ℕ ℕ⊑ℕ ★≲ℕ ℕ≲ℕ = ?-⊑-id ℕ⊑ℕ
-- -- ≲⇒-⊑-≲⇒ ★⊑ℕ ★⊑★ ★≲★ ℕ≲★ = id-⊑-! ★⊑ℕ
-- -- ≲⇒-⊑-≲⇒ ★⊑ℕ ★⊑ℕ ★≲★ ℕ≲ℕ = id-⊑ ★⊑ℕ
-- -- ≲⇒-⊑-≲⇒ ★⊑ℕ (∀⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ ★⊑ℕ (⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ (★⊑⇒ bb bb₁) ★⊑★ ★≲★ (⇒≲★ bc′ bc′₁) =
-- --   ⊑-⨟ (id★-⊑-↦ {!!} {!!}) (id-⊑-! (★⊑⇒ ★⊑★ ★⊑★))
-- -- ≲⇒-⊑-≲⇒ (★⊑⇒ bb bb₁) (★⊑⇒ cc cc₁) ★≲★ (⇒≲⇒ bc′ bc′₁) =
-- --   id★-⊑-↦ {!!} {!!}
-- -- ≲⇒-⊑-≲⇒ (★⊑⇒ bb bb₁) (⇒⊑⇒ cc cc₁) (★≲⇒ bc bc₁) (⇒≲⇒ bc′ bc′₁) =
-- --   ⨟-⊑ (?-⊑-↦ (★⊑⇒ bb bb₁) (⇒⊑⇒ {!!} {!!}))
-- --       (↦-⊑ (≲⇒-⊑-≲⇒ bb cc bc bc′) (≲⇒-⊑-≲⇒ bb₁ cc₁ bc₁ bc′₁))
-- -- ≲⇒-⊑-≲⇒ (★⊑⇒ bb bb₁) (∀⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ (★⊑⇒ bb bb₁) (⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ (⇒⊑⇒ bb bb₁) ★⊑★ (⇒≲★ bc bc₁) (⇒≲★ bc′ bc′₁) =
-- --   ⨟-⊑-⨟ (↦-⊑ (≲⇒-⊑-≲⇒ bb ★⊑★ bc bc′) (≲⇒-⊑-≲⇒ bb₁ ★⊑★ bc₁ bc′₁)) !-⊑
-- -- ≲⇒-⊑-≲⇒ (⇒⊑⇒ bb bb₁) (★⊑⇒ cc cc₁) (⇒≲★ bc bc₁) (⇒≲⇒ bc′ bc′₁) =
-- --   ⨟-⊑ (↦-⊑ (≲⇒-⊑-≲⇒ bb cc bc bc′) (≲⇒-⊑-≲⇒ bb₁ cc₁ bc₁ bc′₁))
-- --       (!-⊑-↦ (⇒⊑⇒ {!!} {!!}) (★⊑⇒ cc cc₁))
-- -- ≲⇒-⊑-≲⇒ (⇒⊑⇒ bb bb₁) (⇒⊑⇒ cc cc₁) (⇒≲⇒ bc bc₁) (⇒≲⇒ bc′ bc′₁) =
-- --   ↦-⊑ (≲⇒-⊑-≲⇒ bb cc bc bc′) (≲⇒-⊑-≲⇒ bb₁ cc₁ bc₁ bc′₁)
-- -- ≲⇒-⊑-≲⇒ (⇒⊑⇒ bb bb₁) (∀⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ (⇒⊑⇒ bb bb₁) (⊑∀ cc) bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ (∀⊑∀ bb) cc bc bc′ = {!!}
-- -- ≲⇒-⊑-≲⇒ (⊑∀ bb) cc bc bc′ = {!!}

-- postulate
--   ⊑-⇑ : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx [] Γ Γ′}
--       {A A′ : Type Δ} {A⊑A′ : Δ ∣ [] ⊢ A ⊑ A′}
--       {M : Δ ∣ [] ∣ Γ ⊢ A} {M′ : Δ ∣ [] ∣ Γ′ ⊢ A′}
--       → [] ∣ [] ∣ Φ ⊩ M ⊑ M′ ⦂ A⊑A′
--       → ⤊ [] ∣ ⤊ [] ∣ ⟰ᵖ Φ ⊩ ⇑ M ⊑ ⇑ M′ ⦂ ⊑-⇑ᵗ A A′ A⊑A′

-- _∣_⊢_⊑ˢ_ : ∀ (Δ : TyCtx) (Σ : BindCtx Δ) (σ σ′ : Δ →ᵗ Δ) → Set
-- Δ ∣ Σ ⊢ σ ⊑ˢ σ′ = ∀ X → Δ ∣ Σ ⊢ σ X ⊑ σ′ X

-- postulate
--   reveal-⊑ : ∀{Δ}{σ σ′ : (Δ ,typ) →ᵗ (Δ ,typ)}
--        {B B′ : Type (Δ ,typ)}{C C′ : Type Δ}{s1}{s2}{s3}{s4}
--      → (Δ ,typ) ∣ (Zᵗ , ⇑ᵗ C′) ∷ [] ⊢ σ ⊑ˢ σ′
--      → (Δ ,typ) ∣ (Zᵗ , ⇑ᵗ C) ∷ [] ∣ (Zᵗ , ⇑ᵗ C′) ∷ []
--        ⊩ reveal{σ = σ} B s1 s2 ⊑ reveal{σ = σ′} B′ s3 s4

-- compile-pres-precision : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx [] Γ Γ′}
--   {A A′ : Type Δ} {A⊑A′ : Δ ∣ [] ⊢ A ⊑ A′}
--   {M : Δ ∣ Γ ⊢ᵍ A} {M′ : Δ ∣ Γ′ ⊢ᵍ A′}
--   → Δ ∣ Φ ⊢ᵍ M ⊑ M′ ⦂ A⊑A′
--   → [] ∣ [] ∣ Φ ⊩ compile M ⊑ compile M′ ⦂ A⊑A′
-- compile-pres-precision (⊑-var ∋⊑) = ⊑-var ∋⊑
-- compile-pres-precision ⊑-nat = ⊑-nat
-- compile-pres-precision (⊑-lam M⊑M′) = ⊑-lam (compile-pres-precision M⊑M′)
-- compile-pres-precision (⊑-app{a = a}{b}{d}{f}{bc}{f′}{bc′} L⊑L′ M⊑M′) =
--     let IH1 = compile-pres-precision L⊑L′ in
--     let IH2 = compile-pres-precision M⊑M′ in
--     let cc = ⊑-⏵-⏵-⊑ a f f′ in
--     ⊑-app{c = cc} (⊑-⟨⟩ IH1 (⏵⇒-⊑-⏵⇒ a f f′)) (⊑-⟨⟩ IH2 (≲⇒-⊑-≲⇒ b cc bc bc′))
-- compile-pres-precision (⊑-Λ N⊑N′) =
--     let IH = compile-pres-precision N⊑N′ in
--     ⊑-Λ IH
-- compile-pres-precision{Δ}{Γ}{Γ′}{Φ} (⊑-◯{M = M}{M′}{a = a} M⊑M′) =
--     let IH  : [] ∣ [] ∣ Φ ⊩ compile M ⊑ compile M′ ⦂ a
--         IH = compile-pres-precision M⊑M′ in
--     ⊑-ν (⊑-⟨⟩ {!!} (reveal-⊑ λ { Zᵗ → {!!} ; (Sᵗ X) → {!!}}))
