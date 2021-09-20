open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Product using (_×_; Σ; Σ-syntax)

open import Types
open import Labels
open import PreCastStructure


module PreCastStructureWithPrecisionABT where

  {- This record contains precision relations and corresponding lemmas. -}
  record PreCastStructWithPrecision : Set₁ where
    field
      precast : PreCastStruct
    open PreCastStruct precast public

    -- Precision between two inert casts
    infix 6 _₍_₎⊑_₍_₎
    -- Between an inert cast and a type
    infix 6 _₍_₎⊑_
    -- Between a type and an inert cast
    infix 6 _⊑_₍_₎
    field
      _₍_₎⊑_₍_₎ {- LPII -} : ∀ {A A′ B B′ : Type}
        → (c  : Cast (A  ⇒ B )) → Inert c
        → (c′ : Cast (A′ ⇒ B′)) → Inert c′ → Set
      _₍_₎⊑_    {- LPIT -} : ∀ {A B   : Type}
        → (c  : Cast (A  ⇒ B )) → Inert c
        → Type → Set
      _⊑_₍_₎    {- LPTI -} : ∀ {A′ B′ : Type}
        → Type
        → (c′ : Cast (A′ ⇒ B′)) → Inert c′ → Set

      {- ****** The definitions above need to satisfy the following lemmas: ****** -}
      {-   1. It implies Cast (A ⇒ B , Inert) ⊑ A′ if A ⊑ A′ and B ⊑ B′. -}
      ⊑→lpit : ∀ {A B A′} {c : Cast (A ⇒ B)}
        → (i : Inert c) → A ⊑ A′ → B ⊑ A′ → c ₍ i ₎⊑ A′
      {-   2. It implies A ⊑ A′ and B ⊑ B′ if
              Cast ( A ⇒ B , Inert ) ⊑ Cast ( A′ ⇒ B′ , Inert ) . -}
      lpii→⊑ : ∀ {A A′ B B′}
                  {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
                  {i : Inert c} {i′ : Inert c′}
        → c ₍ i ₎⊑ c′ ₍ i′ ₎ → (A ⊑ A′) × (B ⊑ B′)
      {-   3. It implies A ⊑ A′ and B ⊑ A′ if Cast ( A ⇒ B , Inert ) ⊑ A′ . -}
      lpit→⊑ : ∀ {A A′ B}
                  {c : Cast (A ⇒ B)} {i : Inert c}
        → c ₍ i ₎⊑ A′    → (A ⊑ A′) × (B ⊑ A′)
      {-   4. It implies A ⊑ A′ and A ⊑ B′ if A ⊑ Cast ( A′ ⇒ B′ , Inert ) . -}
      lpti→⊑ : ∀ {A A′ B′}
                  {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
        → A ⊑ c′ ₍ i′ ₎  → (A ⊑ A′) × (A ⊑ B′)
