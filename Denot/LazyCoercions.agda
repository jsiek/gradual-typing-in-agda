open import Data.Nat
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

module Denot.LazyCoercions where

  open import Types
  open import Variables
  open import Labels
  open import CastStructureABT
  open import LazyCoercionsABT
  open import Denot.Value




  infix 4 _↝⟨_⟩↝_
  infix 4 _↝⟨_⟩₊↝_

  data _↝⟨_⟩↝_ : ∀ {A B} → (v : Val) → (c : Cast (A ⇒ B)) → (v' : Val) → Set
  data _↝⟨_⟩₊↝_ : ∀ {A B} → (V : List Val) → (c : Cast (A ⇒ B)) → (V' : List Val) → Set where
    [] : ∀ {A B}{c : Cast (A ⇒ B)} → [] ↝⟨ c ⟩₊↝ []
    _∷_ : ∀ {A B}{c : Cast (A ⇒ B)}{v v' V V'} 
        → v ↝⟨ c ⟩↝ v' → V ↝⟨ c ⟩₊↝ V' → (v ∷ V) ↝⟨ c ⟩₊↝ (v' ∷ V')
  data _↝⟨_⟩↝_ where 
    ⟦id⟧ : ∀{v}{A}{a} → v ↝⟨ id {A}{a} ⟩↝ v
    ⟦inj⟧ : ∀{v}{A}{a} → v ↝⟨ (_!! A {a}) ⟩↝ v
    ⟦proj⟧-ok : ∀{v}{τ : Type}{ℓ}{a}
      → ⟦ v ∶ τ ⟧ → v ↝⟨ _??_ τ ℓ {a} ⟩↝ v
    ⟦proj⟧-fail : ∀{v}{τ : Type}{ℓ : Label}{a}
      → ¬ ⟦ v ∶ τ ⟧
      → v ↝⟨ _??_ τ ℓ {a} ⟩↝ blame ℓ   {- originally "blame! (cvt-label ℓ)", need to check -}
    ⟦cfun⟧ : ∀{V w V′ w′}{A B A′ B′}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}
      → V′ ↝⟨ c ⟩₊↝ V   →   w ↝⟨ d ⟩↝ w′
      → (V ↦ w) ↝⟨ c ↣ d ⟩↝ (V′ ↦ w′)
    ⟦cprod⟧-fst : ∀{u v}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → u ↝⟨ c ⟩↝ v
      → fst u ↝⟨ c `× d ⟩↝ fst v
    ⟦cprod⟧-snd : ∀{u v}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → u ↝⟨ d ⟩↝ v
      → snd u ↝⟨ c `× d ⟩↝ snd v
    ⟦csum⟧-inl : ∀{V V'}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → V ↝⟨ c ⟩₊↝ V'
      → inl V ↝⟨ c `+ d ⟩↝ inl V'
    ⟦csum⟧-inr : ∀{V V'}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → V ↝⟨ d ⟩₊↝ V'
      → inr V ↝⟨ c `+ d ⟩↝ inr V'
    ⟦cfail⟧ : ∀{v}{ℓ}{A}{B} 
      → v ↝⟨ ⊥ A ⟨ ℓ ⟩ B ⟩↝ blame ℓ



  open import Denot.CastStructure

-- This won't typecheck; LazyCoercions and GroundCoercions are written
-- using CastStructureOrig instead of CasStructureABT 
  instance 
    dcs : DenotCastStruct
    dcs = record 
            { cast = cs
            ; _↝⟨_⟩↝_ = _↝⟨_⟩↝_ }