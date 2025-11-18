{-# OPTIONS --rewriting #-}
module PolyBlame.Compile where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Data.Sum using (_⊎_)
open import Function using (_∘_)
open import Agda.Builtin.Bool
open import Relation.Nullary using (Dec; yes; no)

open import PolyBlame.Types
open import PolyBlame.Variables
open import PolyBlame.Gradual
open import PolyBlame.Coercions
open import PolyBlame.Terms

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

⏵-⇒ : ∀{Δ}{A C D : Type Δ}
  → Δ ⊢ A ⏵ (C ⇒ D)
  → Δ ∣ [] ⊢ A ⇒ (C ⇒ D)
⏵-⇒ {A = ★} ⏵-★-⇒ = ★⇒★ `?
⏵-⇒ {A = A ⇒ B} ⏵-⇒-⇒ = id

⏵-∀ : ∀{Δ}{A : Type Δ}{B : Type (Δ ,typ)}
  → Δ ⊢ A ⏵ (`∀ B)
  → Δ ∣ [] ⊢ A ⇒ (`∀ B)
⏵-∀ {A} ⏵-∀-∀ = id
⏵-∀ {A} (⏵-A-∀ x) = 𝒢 id

∼-⇐ : ∀{Δ}{Ψ : SubCtx Δ}{A B : Type Δ}
  → Δ ∣ Ψ ⊢ A ∼ B
  → (Σ : BindCtx Δ)
  → Δ ∣ Σ ⊢ B ⇒ A

∼-⇒ : ∀{Δ}{Ψ : SubCtx Δ}{A B : Type Δ}
  → Δ ∣ Ψ ⊢ A ∼ B
  → (Σ : BindCtx Δ)
  → Δ ∣ Σ ⊢ A ⇒ B
∼-⇒ ℕ∼ℕ Σ = id
∼-⇒ X∼X Σ = id
∼-⇒ ★∼★ Σ = id
∼-⇒ (★∼X{X = X} ∋X) Σ
    with lookup-★ Σ X
... | yes l = l ↓
... | no nl = (` X) `?
∼-⇒ (X∼★{X = X} ∋X) Σ
    with lookup-★ Σ X
... | yes l = l ↑
... | no nl = (` X) !
∼-⇒ ★∼ℕ Σ = `ℕ `?
∼-⇒ ℕ∼★ Σ = `ℕ !
∼-⇒ (⇒∼★ A∼★ B∼★) Σ = ((∼-⇐ A∼★ Σ) ↦ (∼-⇒ B∼★ Σ)) ⨟ (★⇒★ !)
∼-⇒ (★∼⇒ ★∼A ★∼B) Σ = (★⇒★ `?) ⨟ ((∼-⇐ ★∼A Σ) ↦ (∼-⇒ ★∼B Σ))
∼-⇒ (⇒∼⇒ A∼C B∼D) Σ = (∼-⇐ A∼C Σ) ↦ (∼-⇒ B∼D Σ)
∼-⇒ (∀∼∀ A∼B) Σ = `∀ ∼-⇒ A∼B (⤊ Σ)
∼-⇒ (∼∀ A∼B) Σ = 𝒢 (∼-⇒ A∼B (⤊ Σ))
∼-⇒ (∀∼ A∼B) Σ = ℐ (∼-⇒ A∼B ((Zᵗ , ★) ∷ ⤊ Σ))

∼-⇐ ℕ∼ℕ Σ = id
∼-⇐ X∼X Σ = id
∼-⇐ ★∼★ Σ = id
∼-⇐ (★∼X{X = X} ∋X) Σ
    with lookup-★ Σ X
... | yes l = l ↑
... | no nl = (` X) !
∼-⇐ (X∼★{X = X} ∋X) Σ
    with lookup-★ Σ X
... | yes l = l ↓
... | no nl = (` X) `?
∼-⇐ ★∼ℕ Σ = `ℕ !
∼-⇐ ℕ∼★ Σ = `ℕ `?
∼-⇐ (⇒∼★ A∼★ B∼★) Σ = (★⇒★ `?) ⨟ (∼-⇒ A∼★ Σ ↦ ∼-⇐ B∼★ Σ)
∼-⇐ (★∼⇒ ★∼A ★∼B) Σ = (∼-⇒ ★∼A Σ ↦ ∼-⇐ ★∼B Σ) ⨟ (★⇒★ !)
∼-⇐ (⇒∼⇒ A∼C B∼D) Σ = ∼-⇒ A∼C Σ ↦ ∼-⇐ B∼D Σ
∼-⇐ (∀∼∀ A∼B) Σ = `∀ ∼-⇐ A∼B (⤊ Σ)
∼-⇐ (∼∀ A∼B) Σ = ℐ (∼-⇐ A∼B ((Zᵗ , ★) ∷ ⤊ Σ))
∼-⇐ (∀∼ A∼B) Σ = 𝒢 (∼-⇐ A∼B (⤊ Σ))


conceal : ∀{Δ}
    (B : Type (Δ ,typ))
    (C : Type Δ)
  → Δ ,typ ∣ (Zᵗ , ⇑ᵗ C) ∷ [] ⊢ ⇑ᵗ (B [ C ]ˢ) ⇒ B

reveal : ∀{Δ}
    (B : Type (Δ ,typ))
    (C : Type Δ)
  → Δ ,typ ∣ (Zᵗ , ⇑ᵗ C) ∷ [] ⊢ B ⇒ ⇑ᵗ (B [ C ]ˢ)
reveal `ℕ C = id
reveal ★ C = id
reveal (` Zᵗ) C = Zᵇ ↑
reveal (` Sᵗ X) C = id
reveal (B₁ ⇒ B₂) C = conceal B₁ C ↦ reveal B₂ C
reveal (`∀ B) C =
  let c = reveal B (⇑ᵗ C) in
  `∀ {!!} 

conceal B C = {!!}


compile : ∀{Δ : TyCtx}{Γ : Ctx Δ}{A : Type Δ} → Δ ∣ Γ ⊢ᵍ A → Δ ∣ [] ∣ Γ ⊢ A
compile (` x) = ` x
compile (# k) = # k
compile (ƛ N) = ƛ compile N
compile ((L · M) A₁⏵C→A B∼C) =
  ((compile L) ⟨ ⏵-⇒ A₁⏵C→A ⟩) · ( (compile M) ⟨ ∼-⇒ B∼C [] ⟩)
compile (Λ M) = Λ compile M
compile{Δ}{Γ}{D} (_◯_{A = A}{B} M A⏵ C) =
  let M′ = (⇑ᵇ (⇑ (compile M ⟨ ⏵-∀ A⏵ ⟩))) in
  ν C · ((M′ ◯ Zᵗ) ⟨ reveal B C ⟩)


