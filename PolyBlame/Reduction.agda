{-# OPTIONS --rewriting #-}
module PolyBlame.Reduction where

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
open import Relation.Nullary using (Dec; yes; no)

open import PolyBlame.Types
open import PolyBlame.Coercions
open import PolyBlame.Terms

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

{- Value -}

data Value : ∀ {Δ}{Σ}{Γ}{A} → Δ ∣ Σ ∣ Γ ⊢ A → Set where
  ƛ_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
     → (N : Δ ∣ Σ ∣ (Γ ▷ A) ⊢ B)
       -------------------------
     → Value (ƛ N)

  #_ : ∀{Δ Σ Γ}{k}
     → ℕ
       --------------------
     → Value{Δ}{Σ}{Γ} (# k)
  
  Λ_ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
     → (N : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A)
       -------------------------------
     → Value{Δ}{Σ}{Γ} (Λ N)

  _⟨G!⟩ : ∀{Δ Σ Γ}{G : Grnd Δ}{V : Δ ∣ Σ ∣ Γ ⊢ ⌈ G ⌉}
     → Value V
       -----------------
     → Value (V ⟨ G ! ⟩)

  _⟨X↓⟩ : ∀{Δ Σ Γ A}{V : Δ ∣ Σ ∣ Γ ⊢ A}{X}{∋X : Σ ∋ X := A}
     → Value V
       -----------------
     → Value (V ⟨ ∋X ↓ ⟩)

  -- problem parsing ambiguity
  V-⟨↦⟩ : ∀{Δ Σ Γ A B C D}{V : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
            {c : Δ ∣ Σ ⊢ C ⇒ A}{d : Δ ∣ Σ ⊢ B ⇒ D}
     → Value V
       -------------------
     → Value (V ⟨ c ↦ d ⟩)

  _⟨∀_⟩ : ∀{Δ Σ Γ A B}{V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
           {c : Δ ,typ ∣ ⤊ Σ ⊢ A ⇒ B}
     → Value V
       ------------------
     → Value (V ⟨ `∀ c ⟩)

  _⟨𝒢_⟩ : ∀{Δ Σ Γ A B}{V : Δ ∣ Σ ∣ Γ ⊢ A}
           {c : Δ ,typ ∣ ⤊ Σ ⊢ ⇑ᵗ A ⇒ B}
     → Value V
       -----------------
     → Value (V ⟨ 𝒢 c ⟩)

{- Pure Reduction -}

infix 2 _—→_
data _—→_ : ∀ {Δ Σ Γ A} → (Δ ∣ Σ ∣ Γ ⊢ A) → (Δ ∣ Σ ∣ Γ ⊢ A) → Set where

  -- (λx.N) V              —→  N[V/x]
  β : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
          {N : Δ ∣ Σ ∣ Γ ▷ B ⊢ A}
          {V : Δ ∣ Σ ∣ Γ ⊢ B}
    → Value V
    → (ƛ N) · V —→ N [ V ]

  -- (ΛX.V)[Y]             —→  V[Y/X]
  β-Λ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}
          {V : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A}
          {Y : TyVar Δ}
    →  (Λ V) ◯ Y —→ V [ Y ]ᵀ

  -- V⟨∀X.c⟩[Y]            —→  V[Y]⟨c[Y/X]⟩
  β-⟨∀⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type (Δ ,typ)}
            {V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
            {c : Δ ,typ ∣ ⤊ Σ ⊢ A ⇒ B}
            {Y : TyVar Δ}
    → V ⟨ `∀ c ⟩ ◯ Y —→ (V ◯ Y) ⟨ c [ Y ]ᶜ ⟩

  -- V⟨𝒢 X.c⟩[Y]           —→ V⟨c[Y/X]⟩
  β-⟨𝒢⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}{B : Type (Δ ,typ)}
            {V : Δ ∣ Σ ∣ Γ ⊢ A}
            {c : Δ ,typ ∣ ⤊ Σ ⊢ (⇑ᵗ A) ⇒ B}
            {Y : TyVar Δ}
    → V ⟨ 𝒢 c ⟩ ◯ Y —→ V ⟨ c [ Y ]ᶜ ⟩

  -- V⟨ℐ X.c⟩             —→  νX=★. V[X]⟨c⟩
  β-⟨ℐ⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type (Δ ,typ)}{B : Type Δ}
            {V : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
            {c : Δ ,typ ∣ (Zᵗ , ★) ∷ ⤊ Σ ⊢ A ⇒ (⇑ᵗ B)}
    → (V ⟨ ℐ{B = B} c ⟩) —→ (ν ★ · ((⇑ᵇ (⇑ V) ◯ Zᵗ) ⟨ c ⟩))
    
  -- V⟨id⟩                  —→  V
  ⟨id⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}{B : Type Δ}
           {V : Δ ∣ Σ ∣ Γ ⊢ A}
    → (V ⟨ id ⟩) —→ V

  -- V⟨X↓⟩⟨X↑⟩                  —→  V
  ⟨X↓⟩⟨X↑⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}{B : Type Δ}
           {V : Δ ∣ Σ ∣ Γ ⊢ A}{X}{∋X : Σ ∋ X := A}{∋X′ : Σ ∋ X := A}
    → (V ⟨ ∋X ↓ ⟩ ⟨ ∋X′ ↑ ⟩) —→ V

  -- V⟨G!⟩⟨G?⟩              —→  V
  ⟨G!⟩⟨G?⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{G}
           {V : Δ ∣ Σ ∣ Γ ⊢ ⌈ G ⌉}
    → V ⟨ G ! ⟩ ⟨ G `? ⟩ —→ V

  -- V⟨G!⟩⟨H?l⟩             —→  blame l    (G ≠ H)
  ⟨G!⟩⟨H?⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{G}{H}
           {V : Δ ∣ Σ ∣ Γ ⊢ ⌈ G ⌉}
    → G ≢ H
    → V ⟨ G ! ⟩ ⟨ H `? ⟩ —→ blame

  -- V⟨c → d⟩ W             —→  (V W⟨c⟩)⟨d⟩
  β-⟨c→d⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{B}{C}{D}
           {V : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}{W : Δ ∣ Σ ∣ Γ ⊢ C}
           {c : Δ ∣ Σ ⊢ C ⇒ A}{d : Δ ∣ Σ ⊢ B ⇒ D}
    → (V ⟨ c ↦ d ⟩) · W —→ (V · W ⟨ c ⟩) ⟨ d ⟩ 

  -- V⟨c ; d⟩              —→  V⟨c⟩⟨d⟩
  β-⟨c⨟d⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{B}{C}
           {V : Δ ∣ Σ ∣ Γ ⊢ A}
           {c : Δ ∣ Σ ⊢ A ⇒ B}{d : Δ ∣ Σ ⊢ B ⇒ C}
    → V ⟨ c ⨟ d ⟩ —→ V ⟨ c ⟩ ⟨ d ⟩ 

{- Helpers for Context Weaking -}

⤊ᵇ : ∀{Δ}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ}{Γ}{A}
  → Σ ↝ Σ′
  → Δ ∣ Σ ∣ Γ ⊢ A
  → Δ ∣ Σ′ ∣ Γ ⊢ A
⤊ᵇ ↝-refl M = M
⤊ᵇ ↝-extend M = ⇑ᵇ M
⤊ᵇ (↝-trans a b) M = ⤊ᵇ b (⤊ᵇ a M)

rbm : ∀ {Δ₁ Δ₂ Δ₃ : TyCtx}{Σ₁ : BindCtx Δ₁}{Σ₂ : BindCtx Δ₂}
        (ρ₁ : TyVar Δ₁ → TyVar Δ₂)
        (ρ₂ : TyVar Δ₂ → TyVar Δ₃)
  → map (renᵇ ρ₁) Σ₁ ↝ Σ₂
  → map (renᵇ (ρ₁ ⨟ᵗ ρ₂)) Σ₁ ↝ map (renᵇ ρ₂) Σ₂
rbm ρ₁ ρ₂ s = (let s' = ren-bind-map ρ₂ s in s')

{- Reduction -}

infix 2 _∥_∥_⊢_∋_—→_∣_∣_∣_⊢_
data _∥_∥_⊢_∋_—→_∣_∣_∣_⊢_ : ∀ (Δ₁ : TyCtx) → (Σ₁ : BindCtx Δ₁)
  → (Γ : Ctx Δ₁) → (A : Type Δ₁) → (Δ₁ ∣ Σ₁ ∣ Γ ⊢ A) 
  → (Δ₂ : TyCtx)
  → (ρ : Δ₁ ⇒ᵗ Δ₂)
  → (Σ₂ : BindCtx Δ₂)
  → (s : (map (renᵇ ρ) Σ₁) ↝ Σ₂)
  → (Δ₂ ∣ Σ₂ ∣ ren-ctx ρ Γ ⊢ renᵗ ρ A)
  → Set where
  
  pure : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{M N : Δ ∣ Σ ∣ Γ ⊢ A}
    → M —→ N
    → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ N

  β-ν : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B : Type Δ}
      {N : (Δ ,typ) ∣ (Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ ∣ ⟰ Γ ⊢ (⇑ᵗ B)}
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (ν A · N) —→
         (Δ ,typ) ∣ Sᵗ ∣ ((Zᵗ , ⇑ᵗ A) ∷ ⤊ Σ) ∣ ↝-extend ⊢ N

  ξ-·₁ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵗ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
      {s : map (renᵇ ρ) Σ ↝ Σ′}
      {Γ : Ctx Δ}{A B}
      {L : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {L′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ renᵗ ρ (A ⇒ B)}
      {M : Δ ∣ Σ ∣ Γ ⊢ A}
    → Δ ∥ Σ ∥ Γ ⊢ (A ⇒ B) ∋ L —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ L′
      ------------------------------------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (L · M) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ (L′ · ⤊ᵇ s (rename-ty ρ M))

  ξ-·₂ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵗ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
      {s : map (renᵇ ρ) Σ ↝ Σ′}
      {Γ : Ctx Δ}{A B}
      {V : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {M : Δ ∣ Σ ∣ Γ ⊢ A} {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ renᵗ ρ A}
    → Value V
    → Δ ∥ Σ ∥ Γ  ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
      ----------------------------------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (V · M) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ ⤊ᵇ s (rename-ty ρ V) · M′

  blame-·₁ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B}{M : Δ ∣ Σ ∣ Γ ⊢ A}
      ----------------------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (blame · M) —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ blame

  blame-·₂ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A B}
      {V : Δ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
    → Value V
      ----------------------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ B ∋ (V · blame) —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ blame
    
  ξ-◯ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵗ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
     {s : map (renᵇ ρ) Σ ↝ Σ′}
     {Γ : Ctx Δ}{A}
     {M : Δ ∣ Σ ∣ Γ ⊢ (`∀ A)}
     {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ renᵗ ρ (`∀ A)}
     {X : TyVar Δ}
   → Δ ∥ Σ ∥ Γ ⊢ (`∀ A) ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
     --------------------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ A [ X ]ᵗ ∋ (M ◯ X) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ (M′ ◯ ρ X)

  blame-◯ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{X : TyVar Δ}
     ---------------------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ A [ X ]ᵗ ∋ (_◯_{A = A} blame X) —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ blame

  ξ-⟨⟩ : ∀ {Δ Δ′}{ρ : Δ ⇒ᵗ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
     {s : map (renᵇ ρ) Σ ↝ Σ′}
     {Γ : Ctx Δ}{A}{B}
     {M : Δ ∣ Σ ∣ Γ ⊢ A} {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ renᵗ ρ A}
     {c : Δ ∣ Σ ⊢ A ⇒ B}
   → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
     -----------------------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ B ∋ (M ⟨ c ⟩) —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ (M′ ⟨ ⇧ᵇ s (rename-crcn ρ c) ⟩)

  blame-⟨⟩ : ∀ {Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A}{B}{c : Δ ∣ Σ ⊢ A ⇒ B}
     -------------------------------------------------------------
   → Δ ∥ Σ ∥ Γ ⊢ B ∋ (blame ⟨ c ⟩) —→ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ blame

{- Reflexive and transitive closure -}

infix  2 _∥_∥_⊢_∋_—↠_∣_∣_∣_⊢_
infix  3 _∎

data _∥_∥_⊢_∋_—↠_∣_∣_∣_⊢_ : ∀ (Δ₁ : TyCtx) → (Σ₁ : BindCtx Δ₁)
  → (Γ : Ctx Δ₁) → (A : Type Δ₁) → (Δ₁ ∣ Σ₁ ∣ Γ ⊢ A) 
  → (Δ₂ : TyCtx)
  → (ρ : Δ₁ ⇒ᵗ Δ₂)
  → (Σ₂ : BindCtx Δ₂)
  → (s : (map (renᵇ ρ) Σ₁) ↝ Σ₂)
  → (Δ₂ ∣ Σ₂ ∣ ren-ctx ρ Γ ⊢ renᵗ ρ A)
  → Set where

  _∎ : ∀{Δ}{Σ : BindCtx Δ}{Γ : Ctx Δ}{A : Type Δ}
    → (M : Δ ∣ Σ ∣ Γ ⊢ A)
      ---------------------------------------------
    → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —↠ Δ ∣ idᵗ ∣ Σ ∣ ↝-refl ⊢ M

  step—→ : ∀{Δ₁ Δ₂ Δ₃}{Σ₁ Σ₂ Σ₃}{Γ}{A}{ρ₁}{s₁}{ρ₂}{s₂}
      (L : Δ₁ ∣ Σ₁ ∣ Γ ⊢ A)
      {M : Δ₂ ∣ Σ₂ ∣ ren-ctx ρ₁ Γ ⊢ renᵗ ρ₁ A}
      {N : Δ₃ ∣ Σ₃ ∣ ren-ctx ρ₂ (ren-ctx ρ₁ Γ) ⊢ renᵗ ρ₂ (renᵗ ρ₁ A)}
    → Δ₁ ∥ Σ₁ ∥ Γ ⊢ A ∋ L —→ Δ₂ ∣ ρ₁ ∣ Σ₂ ∣ s₁ ⊢ M
    → Δ₂ ∥ Σ₂ ∥ ren-ctx ρ₁ Γ ⊢ renᵗ ρ₁ A ∋ M —↠ Δ₃ ∣ ρ₂ ∣ Σ₃ ∣ s₂ ⊢ N
      -----------------------------------------------------------------------
    → Δ₁ ∥ Σ₁ ∥ Γ ⊢ A ∋ L
      —↠ Δ₃ ∣ (ρ₁ ⨟ᵗ ρ₂) ∣ Σ₃ ∣ ↝-trans (rbm ρ₁ ρ₂ s₁) s₂ ⊢ N


{- Progress -}

data Progress {Δ}{Σ}{A} (M : Δ ∣ Σ ∣ ∅ ⊢ A) : Set where
  step : ∀ {Δ′}{ρ}{Σ′}{s} {N : Δ′ ∣ Σ′ ∣ ∅ ⊢ renᵗ ρ A}
    → Δ ∥ Σ ∥ ∅ ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ N
    → Progress M
    
  done :
      Value M
      -----------
    → Progress M

  blame :
      M ≡ blame
    → Progress M

progress-seal : ∀{Δ Σ}{Y}{A}
  → unique Σ
  → (M : Δ ∣ Σ ∣ ∅ ⊢ (` Y))
  → (∋Y : Σ ∋ Y := A)
  → (c : Δ ∣ Σ ⊢ (` Y) ⇒ A)
  → Value M
  → Progress (M ⟨ ∋Y ↑ ⟩)
progress-seal {A = A} u (V ⟨ ∋X ↓ ⟩) ∋Y c (vM ⟨X↓⟩)
    with lookup-unique ∋X ∋Y u
... | refl = step (pure (⟨X↓⟩⟨X↑⟩{B = A}))

progress : ∀ {Δ Σ A} → (M : Δ ∣ Σ ∣ ∅ ⊢ A) → unique Σ → Progress M
progress (# k) u = done (# k)
progress (ƛ N) u = done (ƛ N)
progress (L · M) u with progress L u
... | step L→L′ = step (ξ-·₁ L→L′)
... | done (V-⟨↦⟩ v) = step (pure β-⟨c→d⟩)
... | blame refl = step blame-·₁
... | done (ƛ N) with progress M u
... | step M→M′ = step (ξ-·₂ (ƛ N) M→M′)
... | done w = step (pure (β w))
... | blame refl = step (blame-·₂ (ƛ N))
progress (Λ N) u = done (Λ N)
progress (M ◯ X) u with progress M u
... | step M→M′ = step (ξ-◯ M→M′)
... | done (Λ N) = step (pure β-Λ)
... | done (_⟨∀_⟩ v) = step (pure β-⟨∀⟩)
... | done (_⟨𝒢_⟩ v) = step (pure β-⟨𝒢⟩)
... | blame refl = step blame-◯
progress (_⟨_⟩{A = A } M c) u with progress M u
... | step M→M′ = step (ξ-⟨⟩ M→M′)
... | blame refl = step blame-⟨⟩
... | done v
    with c
... | id = step (pure (⟨id⟩{B = A}))
... | c ↦ d = done (V-⟨↦⟩ v)
... | c ⨟ d = step (pure β-⟨c⨟d⟩)
... | `∀ c = done (_⟨∀_⟩ v)
... | 𝒢 c = done (_⟨𝒢_⟩ v)
... | ℐ c = step (pure β-⟨ℐ⟩)
... | X ↓ = done (v ⟨X↓⟩)
... | X ↑ = progress-seal u M X c v
... | G ! = done (v ⟨G!⟩)
... | H `?
    with v
... | _⟨G!⟩ {G = G} v′
    with G ≡ᵍ H
... | yes refl = step (pure ⟨G!⟩⟨G?⟩)
... | no neq = step (pure (⟨G!⟩⟨H?⟩ neq))
progress blame u = blame refl
progress (ν A · N) u = step β-ν

{--- Preservation of unique binding entries ---}

unique-preservation : ∀ {Δ Δ′}{ρ : Δ ⇒ᵗ Δ′}{Σ : BindCtx Δ}{Σ′ : BindCtx Δ′}
     {s : map (renᵇ ρ) Σ ↝ Σ′} {Γ : Ctx Δ}{A}
     {M : Δ ∣ Σ ∣ Γ ⊢ A}
     {M′ : Δ′ ∣ Σ′ ∣ ren-ctx ρ Γ ⊢ renᵗ ρ A}
  → unique Σ
  → Δ ∥ Σ ∥ Γ ⊢ A ∋ M —→ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ M′
  → unique Σ′ 
unique-preservation u (pure x) = u
unique-preservation {Σ = Σ} u (β-ν{A = A}) = unique-extend{A = A} Σ u
unique-preservation u (ξ-·₁ M→M′) = unique-preservation u M→M′
unique-preservation u (ξ-·₂ x M→M′) = unique-preservation u M→M′
unique-preservation u blame-·₁ = u
unique-preservation u (blame-·₂ x) = u
unique-preservation u (ξ-◯ M→M′) = unique-preservation u M→M′
unique-preservation u blame-◯ = u
unique-preservation u (ξ-⟨⟩ M→M′) = unique-preservation u M→M′
unique-preservation u blame-⟨⟩ = u

{--- Type Safety ---}

type-safety : ∀{Δ Δ′}{ρ}{Σ}{Σ′}{s}{A}{M}{N}
  → unique Σ
  → Δ ∥ Σ ∥ ∅ ⊢ A ∋ M —↠ Δ′ ∣ ρ ∣ Σ′ ∣ s ⊢ N
  → Progress N
type-safety u (M ∎) = progress M u
type-safety u (step—→ _ M→M′ M′→N) =
   type-safety (unique-preservation u M→M′) M′→N
