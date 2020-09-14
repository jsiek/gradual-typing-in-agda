open import Types
open import Labels
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; Σ; Σ-syntax)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

module PreCastStructure where

record PreCastStruct : Set₁ where
  field
    Cast : Type → Set  
    Inert : ∀{A} → Cast A → Set
    Active : ∀{A} → Cast A → Set
    ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
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
    {- The fields below are for blame-subtyping. -}
    labC : ∀ {A} → (c : Cast A) → Maybe Label
    Safe : ∀ {A} → Cast A → Set
    domSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} → Safe c → (x : Cross c)
            → Safe (dom c x)
    codSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} → Safe c → (x : Cross c)
            → Safe (cod c x)
    domLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))) → (x : Cross c)
           → labC c ≡ labC (dom c x)
    codLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))) → (x : Cross c)
           → labC c ≡ labC (cod c x)
    fstSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} → Safe c → (x : Cross c)
            → Safe (fstC c x)
    sndSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} → Safe c → (x : Cross c)
            → Safe (sndC c x)
    fstLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))) → (x : Cross c)
           → labC c ≡ labC (fstC c x)
    sndLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))) → (x : Cross c)
           → labC c ≡ labC (sndC c x)
    inlSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} → Safe c → (x : Cross c)
            → Safe (inlC c x)
    inrSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} → Safe c → (x : Cross c)
            → Safe (inrC c x)
    inlLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))) → (x : Cross c)
           → labC c ≡ labC (inlC c x)
    inrLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))) → (x : Cross c)
           → labC c ≡ labC (inrC c x)
