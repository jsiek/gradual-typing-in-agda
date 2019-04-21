module GroundMachine where

  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  open import Labels
  open import Types
  open import EfficientGroundCoercions

  import AbstractMachine
  module AbsMach = AbstractMachine Cast Inert Active ActiveOrInert
  open AbsMach

  cast : ∀{A B} → Value A → (c : Cast (A ⇒ B)) → Active c → Value B ⊎ Label
  cast V c a = ?
  
  funSrc' : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → SimpleValue A
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc' c i V = funSrc c i

  module Mach = AbsMach.Machine cast funSrc' dom cod ? ? ? ? ? ?
                  compose baseNotInert

