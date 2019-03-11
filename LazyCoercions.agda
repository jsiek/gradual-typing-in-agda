module LazyCoercions where

  open import Data.Nat
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

  infix 7 _↣_
  infix 5 _!!
  infix 5 _??_
  infix 5 ⊥_⟨_⟩_

  data Cast : Type → Set where
    id : ∀ {A : Type} {a : Atomic A} → Cast (A ⇒ A)
    _!! : (A : Type) → ∀ {i : A ≢ ⋆} → Cast (A ⇒ ⋆)
    _??_ : (B : Type) → Label → ∀ {j : B ≢ ⋆} → Cast (⋆ ⇒ B)
    _↣_ : ∀ {A B A' B'}
      → (c : Cast (B ⇒ A)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A ⇒ A') ⇒ (B ⇒ B'))
    _`×_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A `× A') ⇒ (B `× B'))
    _`+_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A `⊎ A') ⇒ (B `⊎ B'))
    ⊥_⟨_⟩_ : 
        (A : Type) → Label → (B : Type)
      → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  coerce : (A : Type) → (B : Type) → Label → Cast (A ⇒ B)
  coerce A B ℓ with (A `⌣ B)
  coerce A B ℓ | inj₁ nat⌣ = id {a = A-Nat}
  ... | inj₁ bool⌣ = id {a = A-Bool}
  ... | inj₁ (fun⌣{A₁}{A₂}{B₁}{B₂}) = (coerce B₁ A₁ (flip ℓ)) ↣ (coerce A₂ B₂ ℓ)
  ... | inj₁ (pair⌣{A₁}{A₂}{B₁}{B₂}) = (coerce A₁ B₁ ℓ) `× (coerce A₂ B₂ ℓ)
  ... | inj₁ (sum⌣{A₁}{A₂}{B₁}{B₂}) = (coerce A₁ B₁ ℓ) `+ (coerce A₂ B₂ ℓ)
  ... | inj₂ nsc = ⊥ A ⟨ ℓ ⟩ B
  coerce A B ℓ | inj₁ unk⌣L with eq-unk B
  ... | inj₁ eq rewrite eq = id {a = A-Unk}
  ... | inj₂ neq = (B ?? ℓ) {j = neq}
  coerce A B ℓ | inj₁ unk⌣R with eq-unk A
  ... | inj₁ eq rewrite eq = id {a = A-Unk}
  ... | inj₂ neq = (A !!) {i = neq}

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A i} → Inert ((A !!) {i})

  data Active : ∀ {A} → Cast A → Set where
    A-proj : ∀{ B ℓ j} → Active ((B ?? ℓ) {j})
    A-fun : ∀{A B A' B'}{c : Cast (A ⇒ B)} {d : Cast (A' ⇒ B')} → Active(c ↣ d)
    A-pair : ∀{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')} → Active(c `× d)
    A-sum : ∀{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')} → Active(c `+ d)
    A-id : ∀{A a} → Active (id {A}{a})
    A-fail : ∀{A B ℓ} → Active (⊥ A ⟨ ℓ ⟩ B)

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id = inj₁ A-id
  ActiveOrInert (A !!) = inj₂ I-inj
  ActiveOrInert (B ?? ℓ) = inj₁ A-proj
  ActiveOrInert (c ↣ c₁) = inj₁ A-fun
  ActiveOrInert (c `× c₁) = inj₁ A-pair
  ActiveOrInert (c `+ c₁) = inj₁ A-sum
  ActiveOrInert (⊥ A ⟨ ℓ ⟩ B) = inj₁ A-fail

  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
              → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id {a} = M
  applyCast M v (A !!) {()}
  applyCast M v (B ?? ℓ) {a} with PCR.canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | inj₁ cns = M' ⟨ coerce A' B ℓ ⟩
  ...    | inj₂ incns = blame ℓ
  applyCast{Γ} M v (c ↣ d) {a} =
     ƛ (((rename (λ {A} → S_) M) · ((` Z) ⟨ c ⟩)) ⟨ d ⟩)
  applyCast M v (c `× d) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast M v (c `+ d) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in
    let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ l) (ƛ r)
  applyCast M v (⊥ A ⟨ ℓ ⟩ B) = blame ℓ

  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B')))
            → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M c {()} N

  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B')))
            → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M c {()}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B')))
            → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M c {()}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B')))
            → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L c {()} M N
  
  baseNotInert : ∀ {A B} → (c : Cast (A ⇒ B)) → Base B → ¬ Inert c
  baseNotInert (_ !!) () I-inj

  module Red = PCR.Reduction applyCast funCast fstCast sndCast caseCast
                   baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → coerce A B ℓ)
