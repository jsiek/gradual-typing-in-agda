open import Types hiding (_⊔_)
open import Variables
open import PreCastStructure

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _≤_; _⊔_; _+_; _*_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)
open import Pow2

module CastStructure where

import ParamCastCalculus
import ParamCastCalculusOrig
import ParamCastAux
import EfficientParamCastAux

  {-

  We need a few operations to define reduction in a generic way.
  In particular, we need parameters that say how to reduce casts and
  how to eliminate values wrapped in casts.
  * The applyCast parameter, applies an Active cast to a value.
  * The funCast parameter applies a function wrapped in an inert cast
    to an argument.
  * The fstCast and sndCast parameters take the first or second part
    of a pair wrapped in an inert cast.
  * The caseCast performs a case-elimination on a value of sum type (inl or inr)
    that is wrapped in an inert cast.
  * The baseNotInert parameter ensures that every cast to a base type
    is not inert.

  We define a nested module named Reduction with these parameters
  because they all depend on parameters of the outer module, and it
  seems that Agda does not allow parameters to depend on other
  parameters of the same module.

  -}

record CastStruct : Set₁ where
  field
    precast : PreCastStruct
  open PreCastStruct precast public
  open ParamCastCalculus Cast Inert
  open ParamCastAux precast
  field
    applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
                    → ∀ {a : Active c} → Γ ⊢ B


record EfficientCastStruct : Set₁ where
  field
    precast : PreCastStruct
  open PreCastStruct precast public
  open ParamCastCalculusOrig Cast
  open EfficientParamCastAux precast
  field
    applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → SimpleValue M → (c : Cast (A ⇒ B))
                 → ∀ {a : Active c} → Γ ⊢ B
    compose : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C)) → Cast (A ⇒ C)
    height : ∀{A B} → (c : Cast (A ⇒ B)) → ℕ
    compose-height : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
                   → height (compose c d) ≤ (height c) ⊔ (height d)
    applyCastOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}{a}
          → n ∣ false ⊢ M ok → (v : SimpleValue M)
          → Σ[ m ∈ ℕ ] m ∣ false ⊢ applyCast M v c {a} ok × m ≤ 2 + n

  c-height : ∀{Γ A} (M : Γ ⊢ A) → ℕ
  c-height (` x) = 0
  c-height (ƛ M) = c-height M
  c-height (L · M) = c-height L ⊔ c-height M
  c-height ($ x) = 0
  c-height (if L M N) = c-height L ⊔ c-height M ⊔ c-height N
  c-height (cons M N) = c-height M ⊔ c-height N
  c-height (fst M) = c-height M
  c-height (snd M) = c-height M
  c-height (inl M) = c-height M
  c-height (inr M) = c-height M
  c-height (case L M N) = c-height L ⊔ c-height M ⊔ c-height N
  c-height (M ⟨ c ⟩) = c-height M ⊔ height c
  c-height (blame ℓ) = 0


record EfficientCastStructHeight : Set₁ where
  field
    effcast : EfficientCastStruct
  open EfficientCastStruct effcast public
  open ParamCastCalculus Cast
  open EfficientParamCastAux precast

  field
    applyCast-height : ∀{Γ}{A B}{V}{v : SimpleValue {Γ} V}{c : Cast (A ⇒ B)}
        {a : Active c}
      → c-height (applyCast V v c {a}) ≤ c-height V ⊔ height c
    dom-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}.{x : Cross c}
       → height (dom c x) ≤ height c
    cod-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}.{x : Cross c}
       → height (cod c x) ≤ height c
    fst-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}.{x : Cross c}
       → height (fstC c x) ≤ height c
    snd-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}.{x : Cross c}
       → height (sndC c x) ≤ height c
    inlC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}.{x : Cross c}
       → height (inlC c x) ≤ height c
    inrC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}.{x : Cross c}
       → height (inrC c x) ≤ height c
    size : ∀{A B} → (c : Cast (A ⇒ B)) → ℕ
    size-height : Σ[ c1 ∈ ℕ ] Σ[ c2 ∈ ℕ ] 1 ≤ c2 ×
        ∀{A B}(c : Cast (A ⇒ B)) → c1 + size c ≤ c2 * pow2 (height c) 

