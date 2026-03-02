{-# OPTIONS --rewriting #-}
module PolyBlame.Compile where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym; subst)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Data.Sum using (_⊎_)
open import Function using (_∘_)
open import Agda.Builtin.Bool
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import PolyBlame.Types
open import PolyBlame.TypeSubst
open import PolyBlame.Variables
open import PolyBlame.TypePrecision
open import PolyBlame.ConsistentSubtyping
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

≲-⇒ : ∀{Δ}{A B : Type Δ}
  → (Σ : BindCtx Δ)
  → Δ ∣ Σ ⊢ A ≲ B
  → Δ ∣ Σ ⊢ A ⇒ B
≲-⇒ Σ ℕ≲ℕ = id
≲-⇒ Σ X≲X = id
≲-⇒ Σ ★≲★ = id
≲-⇒ Σ (★≲X{X = X} ∋X)
    with lookup-★ Σ X
... | yes l = l -
... | no nl = (` X) `?
≲-⇒ Σ (X≲★{X = X} ∋X)
    with lookup-★ Σ X
... | yes l = l +
... | no nl = (` X) !
≲-⇒ Σ ★≲ℕ = `ℕ `?
≲-⇒ Σ ℕ≲★ = `ℕ !
≲-⇒ Σ (⇒≲★ A≲★ B≲★) = ((≲-⇒ Σ A≲★) ↦ (≲-⇒ Σ B≲★)) ⨟ (★⇒★ !)
≲-⇒ Σ (★≲⇒ ★≲A ★≲B) = (★⇒★ `?) ⨟ ((≲-⇒ Σ ★≲A) ↦ (≲-⇒ Σ ★≲B))
≲-⇒ Σ (⇒≲⇒ A≲C B≲D) = (≲-⇒ Σ A≲C) ↦ (≲-⇒ Σ B≲D)
≲-⇒ Σ (∀≲∀ A≲B) = `∀ ≲-⇒ (⤊ Σ) A≲B
≲-⇒ Σ (≲∀ A≲B) = 𝒢 (≲-⇒ (⤊ Σ) A≲B)
≲-⇒ Σ (∀≲ A≲B) = ℐ (≲-⇒ ((Zᵗ , ★) ∷ ⤊ Σ) A≲B)

data SubOne : ∀ {Δ Δ′} (C : Type Δ′) → (Δ →ᵗ Δ′) → Set where
  se-init : ∀ {Δ′}{C : Type Δ′} → SubOne C (C •ˢ ids)
  se-ext : ∀{Δ Δ′}{σ : Δ →ᵗ Δ′}{C : Type Δ′}
     → SubOne C σ
     → SubOne (⇑ᵗ C) (extsᵗ σ)

⤊-∋ : ∀{Δ}{Σ : BindCtx Δ}{X : TyVar (Δ ,typ)}{A : Type (Δ ,typ)}
  → ⤊ Σ ∋ X := A
  → Σ[ A′ ∈ Type Δ ] Σ[ Y ∈ TyVar Δ ] Σ ∋ Y := A′ × A ≡ ⇑ᵗ A′ × X ≡ Sᵗ Y
⤊-∋ {Δ} {(Y , B) ∷ Σ}{X} (Zᵇ refl refl) = B , Y , (Zᵇ refl refl) , refl , refl
⤊-∋ {Δ} {(Y , B) ∷ Σ} (Sᵇ ∋X)
    with ⤊-∋ ∋X
... | C , W , ∋X′ , refl , refl = C , W , Sᵇ ∋X′ , refl , refl

exts-fun : ∀{Δ}{Σ : BindCtx Δ}{σ : Δ →ᵗ Δ}
    → ((X : TyVar Δ) (A : Type Δ) → Σ ∋ X := A → σ X ≡ A)
    → ((X : TyVar (Δ ,typ)) (A : Type (Δ ,typ)) → ⤊ Σ ∋ X := A → extsᵗ σ X ≡ A)
exts-fun {Δ} {Σ} {σ} f X A ∋X
    with ⤊-∋ ∋X
... | B , Y , X′ , refl , refl
    with f Y B X′
... | refl = refl

exts-nolook : ∀ {Δ}{Σ : BindCtx Δ}{σ : Δ →ᵗ Δ}
  → ((X : TyVar Δ) → ¬ (Σ[ A ∈ Type Δ ] Σ ∋ X := A) → σ X ≡ (` X))
  → ((X : TyVar (Δ ,typ)) → ¬ (Σ[ A ∈ Type (Δ ,typ) ] (⤊ Σ) ∋ X := A)
         → extsᵗ σ X ≡ (` X))
exts-nolook {Δ} {[]} {σ} nl Zᵗ nl2 = refl
exts-nolook {Δ} {[]} {σ} nl (Sᵗ X) nl2 =
  let eq = (nl X (λ ())) in
  subst (λ W → ⇑ᵗ W ≡ (` Sᵗ X)) (sym eq) refl
exts-nolook {Δ} {(Y , B) ∷ Σ} {σ} nl Zᵗ nl2 = refl
exts-nolook {Δ} {(Y , B) ∷ Σ} {σ} nl (Sᵗ X) nl2 =
  let eq = nl X λ { (A , ∋X) → nl2 ((⇑ᵗ A) , (ren-bind ∋X))} in
  subst (λ W → ⇑ᵗ W ≡ (` Sᵗ X)) (sym eq) refl

reveal : ∀{Δ}{Σ}{σ : Δ →ᵗ Δ}
    (B : Type Δ)
  → (∀ X A → Σ ∋ X := A → σ X ≡ A)
  → (∀ X → ¬ (Σ[ A ∈ Type Δ ] Σ ∋ X := A) → σ X ≡ ` X)
  → Δ ∣ Σ ⊢ B ⇒ subᵗ σ B

conceal : ∀{Δ}{Σ}{σ : Δ →ᵗ Δ}
    (B : Type Δ)
  → (∀ X A → Σ ∋ X := A → σ X ≡ A)
  → (∀ X → ¬ (Σ[ A ∈ Type Δ ] Σ ∋ X := A) → σ X ≡ ` X)
  → Δ ∣ Σ ⊢ subᵗ σ B ⇒ B

id-eq : ∀{Δ}{Σ}{A B : Type Δ} → A ≡ B → Δ ∣ Σ ⊢ A ⇒ B
id-eq refl = id

reveal `ℕ f nf = id
reveal ★ f nf = id
reveal {Δ}{Σ}{σ} (` X) f nf
    with lookup-bind Σ X
... | no nl = id-eq (sym (nf X nl))
reveal {Δ}{Σ}{σ} (` X) f nf
    | yes (A , ∋X)
    with f X A ∋X
... | refl = ∋X +
reveal (A ⇒ B) f nf = conceal A f nf ↦ reveal B f nf
reveal{σ = σ} (`∀ B) f nf = `∀ reveal{σ = extsᵗ σ} B (exts-fun f) (exts-nolook nf)

conceal `ℕ f nf = id
conceal ★ f nf = id
conceal{Δ}{Σ}{σ} (` X) f nf
    with lookup-bind Σ X
... | no nl = id-eq (nf X nl)
conceal {Δ}{Σ}{σ} (` X) f nf
    | yes (A , ∋X)
    with f X A ∋X
... | refl = ∋X -
conceal (A ⇒ B) f nf = reveal A f nf ↦ conceal B f nf
conceal{σ = σ} (`∀ B) f nf =
  `∀ conceal{σ = extsᵗ σ} B (exts-fun f) (exts-nolook nf)

compile : ∀{Δ : TyCtx}{Γ : Ctx Δ}{A : Type Δ} → Δ ∣ Γ ⊢ᵍ A → Δ ∣ [] ∣ Γ ⊢ A
compile (` x) = ` x
compile (# k) = # k
compile (ƛ N) = ƛ compile N
compile ((L · M) A₁⏵C→A B∼C) =
  ((compile L) ⟨ ⏵-⇒ A₁⏵C→A ⟩) · ( (compile M) ⟨ ≲-⇒ [] B∼C ⟩)
compile (Λ M) = Λ compile M
compile{Δ}{Γ}{D} (_◯_{A = A}{B} M C A⏵) =
  let M′ = (⇑ᵇ (⇑ (compile M ⟨ ⏵-∀ A⏵ ⟩))) in
  ν C · ((M′ ◯ Zᵗ) ⟨ reveal{σ = (C •ˢ ids) ⨟ᵀ r2s Sᵗ} B L NL ⟩)
  where
  L : (X : TyVar (Δ ,typ)) (A : Type (Δ ,typ))
      → ((Zᵗ , ⇑ᵗ C) ∷ []) ∋ X := A
      → subᵗ (r2s Sᵗ) ((C •ˢ ids) X) ≡ A
  L X A (Zᵇ refl refl) = refl

  NL : (X : TyVar (Δ ,typ))
      → ¬ Σ-syntax (Type (Δ ,typ)) (_∋_:=_ ((Zᵗ , ⇑ᵗ C) ∷ []) X)
      → subᵗ (r2s Sᵗ) ((C •ˢ ids) X) ≡ (` X)
  NL Zᵗ nl = ⊥-elim (nl ((⇑ᵗ C) , (Zᵇ refl refl)))
  NL (Sᵗ X) nl = refl


