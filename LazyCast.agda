module LazyCast where

  open import Data.Nat
  open import Data.Bool
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)
  import ParamCastReduction

  data Cast : Type → Set where
    cast : (A : Type) → (B : Type) → Label → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  data Inert : ∀ {A} → Cast A → Set where
    inert : ∀{A} → A ≢ ⋆ → (c : Cast (A ⇒ ⋆)) → Inert c

  data Active : ∀ {A} → Cast A → Set where
    activeIdUnk : (c : Cast (⋆ ⇒ ⋆)) → Active c
    activeOther : ∀ {A B} → (c : Cast (A ⇒ B)) → B ≢ ⋆ → Active c

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert (cast A B ℓ) with eq-unk A | eq-unk B
  ... | inj₁ eqa | inj₁ eqb rewrite eqa | eqb = inj₁ (activeIdUnk (cast ⋆ ⋆ ℓ)) 
  ... | inj₁ eqa | inj₂ neqb = inj₁ (activeOther (cast A B ℓ) neqb)
  ... | inj₂ neqa | inj₁ eqb rewrite eqb = inj₂ (inert neqa (cast A ⋆ ℓ))
  ... | inj₂ neqa | inj₂ neqb = inj₁ (activeOther (cast A B ℓ) neqb)

  injNotActive : ∀{A ℓ} → A ≢ ⋆ → ¬ Active (cast A ⋆ ℓ)
  injNotActive neq (activeIdUnk .(cast ⋆ ⋆ _)) = neq refl
  injNotActive neq (activeOther .(cast _ ⋆ _) x) = x refl

  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  applyCast⋆ : ∀ {Γ A} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ ⋆)) → ∀ {a : Active c} → Γ ⊢ ⋆
  applyCast⋆ {Γ} {A} M v (cast A ⋆ ℓ) {a} with eq-unk A
  ... | inj₁ eq rewrite eq = M
  ... | inj₂ neq = contradiction a (injNotActive neq)

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B)) → ∀ {a : Active c} → Γ ⊢ B
  applyCast {Γ} {A₁} {B₁} M v (cast A₁ B₁ ℓ) {a} with A₁ `⌣ B₁
  ... | inj₁ unk⌣R = applyCast⋆ M v (cast A₁ ⋆ ℓ) {a}
  ... | inj₁ nat⌣ = M
  ... | inj₁ bool⌣ = M
  ... | inj₁ (fun⌣{A}{A'}{B}{B'}) = ƛ B , (((rename (λ {A₂} → S_) M) · ((` Z) ⟨ cast B A ℓ ⟩)) ⟨ cast A' B' ℓ ⟩)
  ... | inj₁ (pair⌣{A}{A'}{B}{B'}) = cons (fst M ⟨ cast A B ℓ ⟩) (snd M ⟨ cast A' B' ℓ ⟩)
  ... | inj₁ (sum⌣{A}{A'}{B}{B'}) =
          let l = inl ((` Z) ⟨ cast A B ℓ ⟩) in
          let r = inr ((` Z) ⟨ cast A' B' ℓ ⟩) in
          case M (ƛ A , l) (ƛ A' , r)
  ... | inj₂ nsc = blame ℓ
  ... | (inj₁ unk⌣L) with PCR.canonical⋆ M v
  ...    | ⟨ A' , ⟨ M' , ⟨ c' , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq =
            M' ⟨ cast A' B₁ ℓ ⟩

  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M c {()} N

  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M c {()}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M c {()}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B'))) → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L c {()} M N
  
  baseNotInert : ∀ {A B} → (c : Cast (A ⇒ B)) → Base B → ¬ Inert c
  baseNotInert c () (inert x .c)

  module Red = PCR.Reduction applyCast funCast fstCast sndCast caseCast baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → cast A B ℓ)
