{-

  P(ω) or Engeler style graph model
  
-}

module DenotValue where

open import Data.Empty using (⊥-elim; ⊥)
open import Data.List using (List ; _∷_ ; []; _++_; length)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Labels
open import PrimitiveTypes using (Base)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import SetsAsPredicates
open import Types hiding (_⊑_; _⊔_)

data Val : Set where
  const : {B : Base} → rep-base B → Val  {- A primitive constant of type B. -}
  _↦_ : List Val → Val → Val             {- one entry in a function's graph -}
  ν : Val                                {- empty function -}
  fst : Val → Val                        {- first component of a pair -}
  snd : Val → Val                        {- second component of a pair -}
  inl : List Val → Val                   {- right injection of a sum -}
  inr : List Val → Val                   {- left injection of a sum -}
  blame : Label → Val

{- Abstraction  ---------------------------------------------------------------}

data Λ : (𝒫 Val → 𝒫 Val) → 𝒫 Val where
  Λ-const : ∀{f B k} → Λ f (const {B} k)
  Λ-↦ : ∀{f V w }
     → w ∈ f (mem V)
     → V ≢ []  {- call by value -}
     → Λ f (V ↦ w)
  Λ-ν : ∀{f} → Λ f ν

{- Application -----------------------------------------------------------------}

infix 6 _•_
data _•_ : 𝒫 Val → 𝒫 Val → 𝒫 Val where
   •-app : ∀ D₁ D₂ {V w}
      → (V ↦ w) ∈ D₁
      → mem V ⊆ D₂
      → w ∈ (D₁ • D₂) 
   •-blame-rator : ∀ D₁ D₂ {ℓ}
      → blame ℓ ∈ D₁
      → blame ℓ ∈ (D₁ • D₂) 
   •-blame-rand : ∀ D₁ D₂ {ℓ}
      → blame ℓ ∈ D₂
      → blame ℓ ∈ (D₁ • D₂) 

{- Pairs -}

data pair : 𝒫 Val → 𝒫 Val → 𝒫 Val where
   pair-fst : ∀ D E {u v}
      → u ∈ D → v ∈ E
      → fst u ∈ pair D E
   pair-snd : ∀ D E {u v}
      → u ∈ D → v ∈ E
      → snd v ∈ pair D E
   pair-blame-fst : ∀ D E {ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ pair D E
   pair-blame-snd : ∀ D E {ℓ}
      → blame ℓ ∈ E
      → blame ℓ ∈ pair D E

data car : 𝒫 Val → 𝒫 Val where
   car-fst : ∀ D {u}
      → fst u ∈ D
      → u ∈ car D
   car-blame : ∀ D {ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ car D

data cdr : 𝒫 Val → 𝒫 Val where
   cdr-snd : ∀ D {u}
      → snd u ∈ D
      → u ∈ cdr D
   cdr-blame : ∀ D {ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ cdr D

{- Sums -}

data inleft : 𝒫 Val → 𝒫 Val where
  inleft-inl : ∀{V D} → mem V ⊆ D → inl V ∈ inleft D
  inleft-blame : ∀{ℓ D} → blame ℓ ∈ D → blame ℓ ∈ inleft D

data inright : 𝒫 Val → 𝒫 Val where
  inright-inr : ∀{V D} → mem V ⊆ D → inr V ∈ inright D
  inright-blame : ∀{ℓ D} → blame ℓ ∈ D → blame ℓ ∈ inright D

data cond : 𝒫 Val → (𝒫 Val → 𝒫 Val) → (𝒫 Val → 𝒫 Val) → 𝒫 Val where
  cond-inl : ∀{D F₁ F₂ V w}
    → inl V ∈ D  → w ∈ F₁ (mem V) → w ∈ cond D F₁ F₂
  cond-inr : ∀{D F₁ F₂ V w}
    → inr V ∈ D  → w ∈ F₂ (mem V) → w ∈ cond D F₁ F₂
  cond-blame : ∀{D F₁ F₂ ℓ}
    → blame ℓ ∈ D  →  blame ℓ ∈ cond D F₁ F₂

