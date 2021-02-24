open import Types
open import Labels
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; Σ; Σ-syntax)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

module PreCastStructure where

record PreCastStruct : Set₁ where
  field
    Cast : Type → Set
    Inert : ∀{A} → Cast A → Set
    Active : ∀{A} → Cast A → Set
    ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
    ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
    Cross : ∀{A} → Cast A → Set
    Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
    Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
    Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
    dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
    cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
    fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
    sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
    inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
    inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
    baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
    idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
    projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c


record PreCastStructWithSafety : Set₁ where
  field
    precast : PreCastStruct
  open PreCastStruct precast public
  field
    {- The fields below are for blame-subtyping. -}
    Safe : ∀ {A} → Cast A → Label → Set
    domSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (dom c x) ℓ
    codSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (cod c x) ℓ
    fstSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (fstC c x) ℓ
    sndSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (sndC c x) ℓ
    inlSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (inlC c x) ℓ
    inrSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (inrC c x) ℓ
