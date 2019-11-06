open import Types

open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)

module CastStructure where

import ParamCastCalculus
import ParamCastReduction

record CastStruct : Set₁ where
  field
    Cast : Type → Set  
    Inert : ∀{A} → Cast A → Set
    Active : ∀{A} → Cast A → Set
    ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  open ParamCastCalculus Cast
  open ParamCastReduction Cast Inert Active ActiveOrInert 
  field
    applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
                 → ∀ {a : Active c} → Γ ⊢ B
    funSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
    pairSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' `× B'))) → (i : Inert c)
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
    dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁)
    cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
    fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         → Cast (A₁ ⇒ A')
    sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         →  Cast (A₂ ⇒ B')
    caseCast : ∀{Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B')))
                 → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
    baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c

module CastCalc (C : CastStruct) where
  open CastStruct C
  open ParamCastCalculus Cast public
  open ParamCastReduction Cast Inert Active ActiveOrInert public
  open Reduction applyCast funSrc dom cod fstCast sndCast
         caseCast baseNotInert public
