{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var

open import InjProj.CastCalculus

module InjProj.Precision where

{----------------------- Type Precision ------------------------}

infixr 6 _⊑_
data _⊑_ : Type → Type → Set where

  unk⊑unk : ★ ⊑ ★
  
  unk⊑ : ∀{G}{B} → gnd⇒ty G ⊑ B → ★ ⊑ B
  
  base⊑ : ∀{ι} → $ₜ ι ⊑ $ₜ ι

  fun⊑ : ∀{A B C D}
     → A ⊑ C
     → B ⊑ D
     → A ⇒ B ⊑ C ⇒ D

Refl⊑ : ∀{A} → A ⊑ A
Refl⊑ {★} = unk⊑unk
Refl⊑ {$ₜ ι} = base⊑
Refl⊑ {A ⇒ B} = fun⊑ Refl⊑ Refl⊑

Trans⊑ : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
Trans⊑ unk⊑unk unk⊑unk = unk⊑unk
Trans⊑ unk⊑unk (unk⊑ b) = unk⊑ b
Trans⊑ (unk⊑ a) unk⊑unk = unk⊑unk
Trans⊑ (unk⊑ a) (unk⊑ b) = unk⊑ b
Trans⊑ (unk⊑ a) base⊑ = unk⊑ a
Trans⊑ (unk⊑ a) (fun⊑ b b₁) = unk⊑ (Trans⊑ a (fun⊑ b b₁))
Trans⊑ base⊑ b = b
Trans⊑ (fun⊑ a a₁) (fun⊑ b b₁) = fun⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)

AntiSym⊑ : ∀ {A B} → A ⊑ B → B ⊑ A → A ≡ B
AntiSym⊑ unk⊑unk unk⊑unk = refl
AntiSym⊑ unk⊑unk (unk⊑ b) = refl
AntiSym⊑ (unk⊑ a) unk⊑unk = refl
AntiSym⊑ (unk⊑ a) (unk⊑ b) = refl
AntiSym⊑ base⊑ base⊑ = refl
AntiSym⊑ {A ⇒ B}{A' ⇒ B'} (fun⊑ a a₁) (fun⊑ b b₁) =
  cong₂ (_⇒_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)

dyn-prec-unique : ∀{A}
  → (c : ★ ⊑ A)
  → (d : ★ ⊑ A)
  → c ≡ d
dyn-prec-unique {★} unk⊑unk unk⊑unk = refl
dyn-prec-unique {★} unk⊑unk (unk⊑ {$ᵍ ι} ())
dyn-prec-unique {★} unk⊑unk (unk⊑ {★⇒★} ())
dyn-prec-unique {★} (unk⊑ {$ᵍ ι} ()) d
dyn-prec-unique {★} (unk⊑ {★⇒★} ()) d
dyn-prec-unique {$ₜ ι} (unk⊑ {$ᵍ .ι} base⊑) (unk⊑ {$ᵍ .ι} base⊑) = refl
dyn-prec-unique {A ⇒ A₁} (unk⊑ {★⇒★} (fun⊑ c c₁)) (unk⊑ {★⇒★} (fun⊑ d d₁))
    with dyn-prec-unique c d | dyn-prec-unique c₁ d₁
... | refl | refl = refl

gnd-prec-unique : ∀{G A}
   → (c : gnd⇒ty G ⊑ A)
   → (d : gnd⇒ty G ⊑ A)
   → c ≡ d
gnd-prec-unique {$ᵍ ι} {.($ₜ ι)} base⊑ base⊑ = refl
gnd-prec-unique {★⇒★} {.(_ ⇒ _)} (fun⊑ c c₁) (fun⊑ d d₁)
    with dyn-prec-unique c d | dyn-prec-unique c₁ d₁
... | refl | refl = refl

unk⊑gnd-inv : ∀{G}
   → (c : ★ ⊑ gnd⇒ty G)
   → ∃[ d ] c ≡ unk⊑{G}{gnd⇒ty G} d
unk⊑gnd-inv {$ᵍ ι} (unk⊑ {$ᵍ .ι} base⊑) = base⊑ , refl
unk⊑gnd-inv {★⇒★} (unk⊑ {★⇒★} (fun⊑ c d)) = fun⊑ c d , refl

{----------------------- Term Precision ------------------------}

infix 3 _⊩_⊑_⦂_

Prec : Set
Prec = (∃[ A ] ∃[ B ] A ⊑ B)

data _⊩_⊑_⦂_ : List Prec → Term → Term → ∀{A B : Type} → A ⊑ B → Set 

data _⊩_⊑_⦂_ where

  ⊑-var : ∀ {Γ x A⊑B}
     → Γ ∋ x ⦂ A⊑B
       -------------------------------------
     → Γ ⊩ (` x) ⊑ (` x) ⦂ proj₂ (proj₂ A⊑B)

  ⊑-lit : ∀ {Γ c}
       -----------------------------------
     → Γ ⊩ ($ c) ⊑ ($ c) ⦂ base⊑{typeof c}

  ⊑-app : ∀{Γ L M L′ M′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → Γ ⊩ L ⊑ L′ ⦂ fun⊑ c d
     → Γ ⊩ M ⊑ M′ ⦂ c
       -----------------------
     → Γ ⊩ L · M ⊑ L′ · M′ ⦂ d

  ⊑-lam : ∀{Γ N N′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → (A , C , c) ∷ Γ ⊩ N ⊑ N′ ⦂ d
       ----------------------------
     → Γ ⊩ ƛ N ⊑ ƛ N′ ⦂ fun⊑ c d

  ⊑-inj-L : ∀{Γ M M′}{G B}{c : (gnd⇒ty G) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ c
       --------------------------------
     → Γ ⊩ M ⟨ G !⟩ ⊑ M′ ⦂ unk⊑{G}{B} c

  ⊑-inj-R : ∀{Γ M M′}{G}{c : ★ ⊑ (gnd⇒ty G)}
     → Γ ⊩ M ⊑ M′ ⦂ c
       ---------------------------
     → Γ ⊩ M ⊑ M′ ⟨ G !⟩ ⦂ unk⊑unk

  ⊑-proj-L : ∀{Γ M M′ H B}{c : (gnd⇒ty H) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑ c
       ---------------------
     → Γ ⊩ M ⟨ H ?⟩ ⊑ M′ ⦂ c

  ⊑-proj-R : ∀{Γ M M′ H}{c : ★ ⊑ (gnd⇒ty H)}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑unk
       ---------------------
     → Γ ⊩ M ⊑ M′ ⟨ H ?⟩  ⦂ c

  ⊑-blame : ∀{Γ M A}
     → map proj₁ Γ ⊢ M ⦂ A
       ------------------------
     → Γ ⊩ M ⊑ blame ⦂ Refl⊑{A}

