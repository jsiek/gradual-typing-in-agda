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
open import PolyBlame.Variables
open import PolyBlame.Terms
open import PolyBlame.Coercions
open import PolyBlame.Gradual
open import PolyBlame.Compile

postulate
  subᵗ-prec : ∀{Δ}{A B : Type (Δ ,typ)}{X}
    → (Δ ,typ) ∣ mt Δ , false ⊢ A ⊑ B
    → Δ ∣ mt Δ ⊢ A [ X ]ᵗ ⊑ (B [ X ]ᵗ)

{- Coercion less precise than a type -}
infix 3 _∣_⊩_⊑_
data _∣_⊩_⊑_ : ∀(Δ : TyCtx)(Σ : BindCtx Δ){A B : Type Δ}
  → (Δ ∣ Σ ⊢ A ⇒ B) → (Type Δ)
  →  Set  where

  id-⊑ : ∀{Δ}{Σ}{A : Type Δ}
      ------------------------
     → Δ ∣ Σ ⊩  id{A = A}  ⊑ A

  ↦-⊑ : ∀{Δ}{Σ}{A B C D E F : Type Δ}
       {c : Δ ∣ Σ ⊢ C ⇒ A }
       {d : Δ ∣ Σ ⊢ B ⇒ D }
     → Δ ∣ Σ ⊩ c ⊑ E
     → Δ ∣ Σ ⊩ d ⊑ F
       --------------------------
     → Δ ∣ Σ ⊩ (c ↦ d) ⊑ (E ⇒ F)

  ⨟-⊑ : ∀{Δ}{Σ}{A B C D : Type Δ}
       {c : Δ ∣ Σ ⊢ A ⇒ B }
       {d : Δ ∣ Σ ⊢ B ⇒ C }
     → Δ ∣ Σ ⊩ c ⊑ D
     → Δ ∣ Σ ⊩ d ⊑ D
       --------------------------
     → Δ ∣ Σ ⊩ (c ⨟ d) ⊑ D

  !-⊑ : ∀{Δ}{Σ}{B : Type Δ}{G : Grnd Δ}
     → Δ ∣ mt Δ ⊢ ⌈ G ⌉ ⊑ B
      ---------------------
     → Δ ∣ Σ ⊩ (G !) ⊑ B

  ?-⊑ : ∀{Δ}{Σ}{B : Type Δ}{G : Grnd Δ}
     → Δ ∣ mt Δ ⊢ ⌈ G ⌉ ⊑ B
      ---------------------
     → Δ ∣ Σ ⊩ (G `?) ⊑ B


★-⊑-FV-⊆ : ∀{Δ}{Ψ : SubCtx Δ}{A : Type Δ}
  → Δ ∣ Ψ ⊢ ★ ⊑ A
  → FV A ⊆ Ψ
★-⊑-FV-⊆ {Δ} {Ψ} {A} ★⊑★ = mt-⊆
★-⊑-FV-⊆ {Δ} {Ψ} {A} (★⊑X ∋X) = ∋-single-⊆ ∋X
★-⊑-FV-⊆ {Δ} {Ψ} {A} ★⊑ℕ = mt-⊆
★-⊑-FV-⊆ {Δ} {Ψ} {A ⇒ B} (★⊑⇒ ★⊑A ★⊑B) =
  let IH1 = ★-⊑-FV-⊆ ★⊑A in
  let IH2 = ★-⊑-FV-⊆ ★⊑B in
  ⊆-∪ IH1 IH2
★-⊑-FV-⊆ {Δ} {Ψ} {A} (⊑∀ ★⊑A) = ⊆-⤋ (★-⊑-FV-⊆ ★⊑A)

★⇒★-⊑-FV-⊆ : ∀{Δ}{Ψ : SubCtx Δ}{A : Type Δ}
  → Δ ∣ Ψ ⊢ (★ ⇒ ★) ⊑ A
  → FV A ⊆ Ψ
★⇒★-⊑-FV-⊆ {Δ} {Ψ} {A ⇒ B} (⇒⊑⇒ ★⊑A ★⊑B) =
  ⊆-∪ (★-⊑-FV-⊆ ★⊑A) (★-⊑-FV-⊆ ★⊑B)
★⇒★-⊑-FV-⊆ {Δ} {Ψ} {`∀ A} (⊑∀ ★⇒★⊑A) =
  ⊆-⤋ (★⇒★-⊑-FV-⊆ ★⇒★⊑A)

★⇒★-⊑ : ∀{Δ}{Ψ : SubCtx Δ}{A : Type Δ}
  → Δ ∣ Ψ ⊢ (★ ⇒ ★) ⊑ A
  → Σ[ A₁ ∈ Type Δ ] Σ[ A₂ ∈ Type Δ ]
    Δ ∣ Ψ ⊢ ★ ⊑ A₁  ×  Δ ∣ Ψ ⊢ ★ ⊑ A₂
★⇒★-⊑ {Δ} {Ψ} {A} (⇒⊑⇒ ★⊑C ★⊑D) = _ , _ , ★⊑C , ★⊑D
★⇒★-⊑ {Δ} {Ψ} {A} (⊑∀ ★⇒★⊑A) = ★ , ★ , ★⊑★ , ★⊑★

ℕ-⊑-FV : ∀{Δ}{Ψ : SubCtx Δ}{A : Type Δ}
  → Δ ∣ Ψ ⊢ `ℕ ⊑ A
  → FV A ⊆ mt Δ
ℕ-⊑-FV {Δ} {Ψ} {`ℕ} ℕ⊑A = mt-⊆
ℕ-⊑-FV {Δ} {Ψ} {`∀ A} (⊑∀ ℕ⊑A) = ⊆-⤋ (ℕ-⊑-FV ℕ⊑A)

{-
⇒-⊑-⊑ : ∀{Δ}{Σ : BindCtx Δ}{A B C : Type Δ}
    (c : Δ ∣ Σ ⊢ A ⇒ B)
  → Δ ∣ Σ ⊩ c ⊑ C
  → Δ ∣ mt Δ ⊢ A ⊑ C  ×  Δ ∣ mt Δ ⊢ B ⊑ C
⇒-⊑-⊑ {Δ} {Σ} {A} {B} c id-⊑ = Refl⊑ A , Refl⊑ A
⇒-⊑-⊑ {Δ} {Σ} {A₁ ⇒ A₂} {B₁ ⇒ B₂} {C₁ ⇒ C₂} (c ↦ d) (↦-⊑ c⊑C₁ d⊑C₂) =
    (⇒⊑⇒ (⇒-⊑-⊑ c c⊑C₁ .proj₂) (⇒-⊑-⊑ d d⊑C₂ .proj₁))
  , (⇒⊑⇒ (⇒-⊑-⊑ c c⊑C₁ .proj₁) (⇒-⊑-⊑ d d⊑C₂ .proj₂))
⇒-⊑-⊑ {Δ} {Σ} {A} {B} (c ⨟ d) (⨟-⊑ c⊑C c⊑C₁) =
  ⇒-⊑-⊑ c c⊑C .proj₁ , ⇒-⊑-⊑ d c⊑C₁ .proj₂
⇒-⊑-⊑ {Δ} {Σ} {A} {B} (★⇒★ !) (!-⊑ (⇒⊑⇒ x y)) = ⇒⊑⇒ x y , ★⊑⇒ x y
⇒-⊑-⊑ {Δ} {Σ} {A} {★} (★⇒★ !) (!-⊑ (⊑∀{B = B′} ★⇒★⊑B′)) =
  let FVB = ★⇒★-⊑-FV-⊆ ★⇒★⊑B′ in
  let ⤋FVB = ⊆-⤋ FVB in
  (⊑∀ ★⇒★⊑B′) , (★-⊑ (`∀ _) ⤋FVB)
⇒-⊑-⊑ {Δ} {Σ} {A} {B} {C} (`ℕ !) (!-⊑ ℕ⊑C) = ℕ⊑C , (★-⊑ C (ℕ-⊑-FV ℕ⊑C))
⇒-⊑-⊑ {Δ} {Σ} {A} {B} {C} ((` X) !) (!-⊑ X⊑C) = X⊑C , {!!}
  {-

    X  ⊑   C
    !
    ★  ⊑  C

   -}
⇒-⊑-⊑ {Δ} {Σ} {A} {B} {C} c (?-⊑ x) = {!!}
-}

infix 3 _∣_∣_⊩_⊑_⦂_
data _∣_∣_⊩_⊑_⦂_ : ∀{Δ}(Σ Σ′ : BindCtx Δ){A B : Type Δ}{Γ Γ′ : Ctx Δ}
  → PrecCtx Γ Γ′ → (Δ ∣ Σ ∣ Γ ⊢ A) → (Δ ∣ Σ′ ∣ Γ′ ⊢ B)
  → Δ ∣ mt Δ ⊢ A ⊑ B → Set  where
  
  ⊑-var : ∀{Δ}{Σ Σ′ : BindCtx Δ}{A B}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
     → (x : ⊢ Φ ∋ A ⊑ B)
       ---------------------------------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ (` proj-left x) ⊑ (` proj-right x) ⦂ get-⊑ x

  ⊑-nat : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}{k : ℕ}
     → Σ ∣ Σ′ ∣ Φ ⊩ (# k) ⊑ (# k) ⦂ ℕ⊑ℕ

  ⊑-lam : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
      {A B C D : Type Δ}{N : Δ ∣ Σ ∣ (Γ ▷ A) ⊢ B} {N′ : Δ ∣ Σ′ ∣ (Γ′ ▷ C) ⊢ D}
      {c : Δ ∣ mt Δ ⊢ A ⊑ C}{d : Δ ∣ mt Δ ⊢ B ⊑ D}
     → Σ ∣ Σ′ ∣ (Φ , c) ⊩ N ⊑ N′ ⦂ d
       ---------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ ƛ N ⊑ ƛ N′ ⦂ ⇒⊑⇒ c d
  
  ⊑-app : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
       {A B C D : Type Δ}
       {L : Δ ∣ Σ ∣ Γ ⊢ A ⇒ B}    {M : Δ ∣ Σ ∣ Γ ⊢ A}
       {L′ : Δ ∣ Σ′ ∣ Γ′ ⊢ C ⇒ D} {M′ : Δ ∣ Σ′ ∣ Γ′ ⊢ C}
       {c : Δ ∣ mt Δ ⊢ A ⊑ C}
       {d : Δ ∣ mt Δ ⊢ B ⊑ D}
     → Σ ∣ Σ′ ∣ Φ ⊩ L ⊑ L′ ⦂ (⇒⊑⇒ c d)
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ c
       --------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ L · M ⊑ L′ · M′ ⦂ d
  
  ⊑-Λ : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
      {A B : Type (Δ ,typ)}{N : (Δ ,typ) ∣ ⤊ Σ ∣ ⟰ Γ ⊢ A}
      {N′ : (Δ ,typ) ∣ ⤊ Σ′ ∣ ⟰ Γ′ ⊢ B}
      {c : (Δ ,typ) ∣ mt (Δ ,typ) ⊢ A ⊑ B}
     → ⤊ Σ ∣ ⤊ Σ′ ∣ ⟰ᵖ Φ ⊩ N ⊑ N′ ⦂ c
       --------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ Λ N ⊑ Λ N′ ⦂ ∀⊑∀ c
      
  ⊑-◯ : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
        {A B : Type (Δ ,typ)}{M : Δ ∣ Σ ∣ Γ ⊢ `∀ A}
        {M′ : Δ ∣ Σ′  ∣ Γ′ ⊢ `∀ B}{X}
        {p : (Δ ,typ) ∣ mt (Δ ,typ) ⊢ A ⊑ B}
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ ∀⊑∀ p
       ----------------------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ (M ◯ X) ⊑ (M′ ◯ X) ⦂ subᵗ-prec p

  ⊑-blame : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
        {A : Type Δ}{M : Δ ∣ Σ ∣ Γ ⊢ A}{M : Δ ∣ Σ ∣ Γ ⊢ A}
       --------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ blame ⦂ Refl⊑ A

  ⊑-⟨⟩ : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
        {A B A′ B′ : Type Δ}
        {M : Δ ∣ Σ ∣ Γ ⊢ A} {c : Δ ∣ Σ ⊢ A ⇒ B}
        {M′ : Δ ∣ Σ′  ∣ Γ′ ⊢ A′} {c′ : Δ ∣ Σ′ ⊢ A′ ⇒ B′}
        {A⊑A′ : Δ ∣ mt Δ ⊢ A ⊑ A′}
        {B⊑B′ : Δ ∣ mt Δ ⊢ B ⊑ B′}
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ A⊑A′
     → Δ ∣ Σ ∣ Σ′ ⊩ c ⊑ c′
       ----------------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B⊑B′
     
{-
  ⊑-⟨⟩-L : ∀{Δ}{Σ Σ′ : BindCtx Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
        {A B C : Type Δ}
        {M : Δ ∣ Σ ∣ Γ ⊢ A}
        {c : Δ ∣ Σ ⊢ A ⇒ B}
        {p : Δ ∣ mt Δ ⊢ A ⊑ C}
        {M′ : Δ ∣ Σ′  ∣ Γ′ ⊢ C}
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⊑ M′ ⦂ p
     → Δ ∣ Σ ⊩ c ⊑ C
       ----------------------------------------------
     → Σ ∣ Σ′ ∣ Φ ⊩ M ⟨ c ⟩ ⊑ M′ ⦂ {!!}
  
-}

⏵⇒-⊑-⏵⇒ : ∀{Δ} {A B C A′ B′ C′ : Type Δ}
  → (Δ ∣ mt Δ ⊢ C ⊑ C′)
  → (f : Δ ⊢ C ⏵ (A ⇒ B))
  → (f′ : Δ ⊢ C′ ⏵ (A′ ⇒ B′))
  → Δ ∣ [] ∣ [] ⊩ (⏵-⇒ f) ⊑ (⏵-⇒ f′)
⏵⇒-⊑-⏵⇒ cc ⏵-⇒-⇒ ⏵-⇒-⇒ = id-⊑ cc
⏵⇒-⊑-⏵⇒ (★⊑⇒ ★⊑A′ ★⊑B′) ⏵-★-⇒ ⏵-⇒-⇒ = ?-⊑-id (⇒⊑⇒ ★⊑A′ ★⊑B′)
⏵⇒-⊑-⏵⇒ cc ⏵-★-⇒ ⏵-★-⇒ = ?-⊑

⊑-⏵-⏵-⊑ : ∀{Δ} {A B C A′ B′ C′ : Type Δ}
  → (Δ ∣ mt Δ ⊢ C ⊑ C′)
  → (Δ ⊢ C ⏵ (A ⇒ B))
  → (Δ ⊢ C′ ⏵ (A′ ⇒ B′))
  → Δ ∣ mt Δ ⊢ A ⊑ A′
⊑-⏵-⏵-⊑ (⇒⊑⇒ cc dd) ⏵-⇒-⇒ ⏵-⇒-⇒ = cc
⊑-⏵-⏵-⊑ (★⊑⇒ cc dd) ⏵-★-⇒ ⏵-⇒-⇒ = cc
⊑-⏵-⏵-⊑ ★⊑★ ⏵-★-⇒ ⏵-★-⇒ = ★⊑★

∼⇐-⊑-∼⇐ : ∀ {Δ} {B C B′ C′ : Type Δ}
  → (Δ ∣ mt Δ ⊢ B ⊑ B′)
  → (Δ ∣ mt Δ ⊢ C ⊑ C′)
  → (bc : Δ ∣ mt Δ ⊢ B ∼ C)
  → (bc′ : Δ ∣ mt Δ ⊢ B′ ∼ C′)
  → Δ ∣ [] ∣ [] ⊩ ∼-⇐ bc [] ⊑ ∼-⇐ bc′ []
  
∼⇒-⊑-∼⇒ : ∀ {Δ} {B C B′ C′ : Type Δ}
  → (Δ ∣ mt Δ ⊢ B ⊑ B′)
  → (Δ ∣ mt Δ ⊢ C ⊑ C′)
  → (bc : Δ ∣ mt Δ ⊢ B ∼ C)
  → (bc′ : Δ ∣ mt Δ ⊢ B′ ∼ C′)
  → Δ ∣ [] ∣ [] ⊩ ∼-⇒ bc [] ⊑ ∼-⇒ bc′ []
∼⇒-⊑-∼⇒ ℕ⊑ℕ ℕ⊑ℕ ℕ∼ℕ ℕ∼ℕ = id-⊑ ℕ⊑ℕ
∼⇒-⊑-∼⇒ ℕ⊑ℕ ★⊑★ ℕ∼★ ℕ∼★ = !-⊑
∼⇒-⊑-∼⇒ ℕ⊑ℕ ★⊑ℕ ℕ∼★ ℕ∼ℕ = !-⊑-id ℕ⊑ℕ
∼⇒-⊑-∼⇒ ℕ⊑ℕ (∀⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ ℕ⊑ℕ (⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ X⊑X X⊑X X∼X X∼X = id-⊑ X⊑X
∼⇒-⊑-∼⇒ X⊑X ★⊑★ (X∼★ ∋X) (X∼★ ∋X′) = !-⊑   -- Remember ∋X ?
∼⇒-⊑-∼⇒ X⊑X (★⊑X x) (X∼★ x₁) X∼X = !-⊑-id X⊑X
∼⇒-⊑-∼⇒ X⊑X (∀⊑∀ cc) (∼∀ bc) (∼∀ bc′) = {!!}
∼⇒-⊑-∼⇒ X⊑X (⊑∀ cc) X∼X (∼∀ bc′) = {!!}
∼⇒-⊑-∼⇒ X⊑X (⊑∀ cc) (X∼★ x) (∼∀ bc′) = {!!}
∼⇒-⊑-∼⇒ X⊑X (⊑∀ cc) (∼∀ bc) bc′ = {!!}
∼⇒-⊑-∼⇒ ★⊑★ ℕ⊑ℕ ★∼ℕ ★∼ℕ = ?-⊑
∼⇒-⊑-∼⇒ ★⊑★ X⊑X (★∼X x) (★∼X x₁) = ?-⊑
∼⇒-⊑-∼⇒ ★⊑★ ★⊑★ ★∼★ ★∼★ = id-⊑ ★⊑★
∼⇒-⊑-∼⇒ ★⊑★ (★⊑X ∋X) ★∼★ (★∼X x₁) = id-⊑-? (★⊑X x₁)
∼⇒-⊑-∼⇒ ★⊑★ ★⊑ℕ ★∼★ ★∼ℕ = id-⊑-? ★⊑ℕ
∼⇒-⊑-∼⇒ ★⊑★ (★⊑⇒ cc cc₁) ★∼★ (★∼⇒ bc′ bc′₁) =
  ⊑-⨟ (id-⊑-? (★⊑⇒ ★⊑★ ★⊑★)) (id★-⊑-↦ {!!} {!!})
∼⇒-⊑-∼⇒ ★⊑★ (⇒⊑⇒ cc cc₁) (★∼⇒ bc bc₁) (★∼⇒ bc′ bc′₁) =
  ⨟-⊑-⨟ ?-⊑ (↦-⊑ (∼⇐-⊑-∼⇐ ★⊑★ cc bc bc′) (∼⇒-⊑-∼⇒ ★⊑★ cc₁ bc₁ bc′₁))
∼⇒-⊑-∼⇒ ★⊑★ (∀⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ ★⊑★ (⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ (★⊑X x) X⊑X (★∼X x₁) X∼X = ?-⊑-id X⊑X
∼⇒-⊑-∼⇒ (★⊑X x) ★⊑★ ★∼★ (X∼★ x₁) = id-⊑-! (★⊑X x)
∼⇒-⊑-∼⇒ (★⊑X x) (★⊑X x₁) ★∼★ X∼X = id-⊑ (★⊑X x)
∼⇒-⊑-∼⇒ (★⊑X x) (∀⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ (★⊑X x) (⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ ★⊑ℕ ℕ⊑ℕ ★∼ℕ ℕ∼ℕ = ?-⊑-id ℕ⊑ℕ
∼⇒-⊑-∼⇒ ★⊑ℕ ★⊑★ ★∼★ ℕ∼★ = id-⊑-! ★⊑ℕ
∼⇒-⊑-∼⇒ ★⊑ℕ ★⊑ℕ ★∼★ ℕ∼ℕ = id-⊑ ★⊑ℕ
∼⇒-⊑-∼⇒ ★⊑ℕ (∀⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ ★⊑ℕ (⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ (★⊑⇒ bb bb₁) ★⊑★ ★∼★ (⇒∼★ bc′ bc′₁) =
  ⊑-⨟ (id★-⊑-↦ {!!} {!!}) (id-⊑-! (★⊑⇒ ★⊑★ ★⊑★))
∼⇒-⊑-∼⇒ (★⊑⇒ bb bb₁) (★⊑⇒ cc cc₁) ★∼★ (⇒∼⇒ bc′ bc′₁) =
  id★-⊑-↦ {!!} {!!}
∼⇒-⊑-∼⇒ (★⊑⇒ bb bb₁) (⇒⊑⇒ cc cc₁) (★∼⇒ bc bc₁) (⇒∼⇒ bc′ bc′₁) =
  ⨟-⊑ (?-⊑-↦ (★⊑⇒ bb bb₁) (⇒⊑⇒ {!!} {!!}))
      (↦-⊑ (∼⇐-⊑-∼⇐ bb cc bc bc′) (∼⇒-⊑-∼⇒ bb₁ cc₁ bc₁ bc′₁))
∼⇒-⊑-∼⇒ (★⊑⇒ bb bb₁) (∀⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ (★⊑⇒ bb bb₁) (⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ (⇒⊑⇒ bb bb₁) ★⊑★ (⇒∼★ bc bc₁) (⇒∼★ bc′ bc′₁) =
  ⨟-⊑-⨟ (↦-⊑ (∼⇐-⊑-∼⇐ bb ★⊑★ bc bc′) (∼⇒-⊑-∼⇒ bb₁ ★⊑★ bc₁ bc′₁)) !-⊑
∼⇒-⊑-∼⇒ (⇒⊑⇒ bb bb₁) (★⊑⇒ cc cc₁) (⇒∼★ bc bc₁) (⇒∼⇒ bc′ bc′₁) =
  ⨟-⊑ (↦-⊑ (∼⇐-⊑-∼⇐ bb cc bc bc′) (∼⇒-⊑-∼⇒ bb₁ cc₁ bc₁ bc′₁))
      (!-⊑-↦ (⇒⊑⇒ {!!} {!!}) (★⊑⇒ cc cc₁))
∼⇒-⊑-∼⇒ (⇒⊑⇒ bb bb₁) (⇒⊑⇒ cc cc₁) (⇒∼⇒ bc bc₁) (⇒∼⇒ bc′ bc′₁) =
  ↦-⊑ (∼⇐-⊑-∼⇐ bb cc bc bc′) (∼⇒-⊑-∼⇒ bb₁ cc₁ bc₁ bc′₁)
∼⇒-⊑-∼⇒ (⇒⊑⇒ bb bb₁) (∀⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ (⇒⊑⇒ bb bb₁) (⊑∀ cc) bc bc′ = {!!}
∼⇒-⊑-∼⇒ (∀⊑∀ bb) cc bc bc′ = {!!}
∼⇒-⊑-∼⇒ (⊑∀ bb) cc bc bc′ = {!!}

∼⇐-⊑-∼⇐ bb cc bc bc′ = {!!}

compile-pres-precision : ∀{Δ}{Γ Γ′ : Ctx Δ}{Φ : PrecCtx Γ Γ′}
  {A A′ : Type Δ} {A⊑A′ : Δ ∣ mt Δ ⊢ A ⊑ A′}
  {M : Δ ∣ Γ ⊢ᵍ A} {M′ : Δ ∣ Γ′ ⊢ᵍ A′}
  → Δ ∣ Φ ⊢ᵍ M ⊑ M′ ⦂ A⊑A′
  → [] ∣ [] ∣ Φ ⊩ compile M ⊑ compile M′ ⦂ A⊑A′
compile-pres-precision (⊑-var ∋⊑) = ⊑-var ∋⊑
compile-pres-precision ⊑-nat = ⊑-nat
compile-pres-precision (⊑-lam M⊑M′) = ⊑-lam (compile-pres-precision M⊑M′)
compile-pres-precision (⊑-app{a = a}{b}{d}{f}{bc}{f′}{bc′} L⊑L′ M⊑M′) =
    let IH1 = compile-pres-precision L⊑L′ in
    let IH2 = compile-pres-precision M⊑M′ in
    let cc = ⊑-⏵-⏵-⊑ a f f′ in
    ⊑-app (⊑-⟨⟩ IH1 (⏵⇒-⊑-⏵⇒ a f f′)) (⊑-⟨⟩ IH2 (∼⇒-⊑-∼⇒ b cc bc bc′))
compile-pres-precision (⊑-Λ N⊑N′) = {!!}
compile-pres-precision (⊑-◯ M⊑M′) = {!!}
