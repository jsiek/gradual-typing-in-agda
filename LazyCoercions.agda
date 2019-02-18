module LazyCoercions where

  open import Data.Nat
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

  data Cast : Type → Set where
    id : ∀ {A : Type} {a : Atomic A} → Cast (A ⇒ A)
    inj : (A : Type) → ∀ {i : A ≢ ⋆} → Cast (A ⇒ ⋆)
    proj : (B : Type) → Label → ∀ {j : B ≢ ⋆} → Cast (⋆ ⇒ B)
    cfun : ∀ {A B A' B'}
      → (c : Cast (B ⇒ A)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A ⇒ A') ⇒ (B ⇒ B'))
    cpair : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A `× A') ⇒ (B `× B'))
    csum : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A `⊎ A') ⇒ (B `⊎ B'))
    cfail : ∀ {A B}
      → Label
      → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  coerce : (A : Type) → (B : Type) → Label → Cast (A ⇒ B)
  coerce A B ℓ with (A `⌣ B)
  coerce A B ℓ | inj₁ nat⌣ = id {a = A-Nat}
  ... | inj₁ bool⌣ = id {a = A-Bool}
  ... | inj₁ (fun⌣{A₁}{A₂}{B₁}{B₂}) = cfun (coerce B₁ A₁ (flip ℓ)) (coerce A₂ B₂ ℓ)
  ... | inj₁ (pair⌣{A₁}{A₂}{B₁}{B₂}) = cpair (coerce A₁ B₁ ℓ) (coerce A₂ B₂ ℓ)
  ... | inj₁ (sum⌣{A₁}{A₂}{B₁}{B₂}) = csum (coerce A₁ B₁ ℓ) (coerce A₂ B₂ ℓ)
  ... | inj₂ nsc = cfail ℓ
  coerce A B ℓ | inj₁ unk⌣L with eq-unk B
  ... | inj₁ eq rewrite eq = id {a = A-Unk}
  ... | inj₂ neq = proj B ℓ {j = neq}
  coerce A B ℓ | inj₁ unk⌣R with eq-unk A
  ... | inj₁ eq rewrite eq = id {a = A-Unk}
  ... | inj₂ neq = inj A {i = neq}

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A i} → Inert (inj A {i})

  data Active : ∀ {A} → Cast A → Set where
    A-proj : ∀{ B ℓ j} → Active (proj B ℓ {j})
    A-fun : ∀{A B A' B' c d} → Active (cfun {A}{B}{A'}{B'} c d)
    A-pair : ∀{A B A' B' c d} → Active (cpair {A}{B}{A'}{B'} c d)
    A-sum : ∀{A B A' B' c d} → Active (csum {A}{B}{A'}{B'} c d)
    A-id : ∀{A a} → Active (id {A}{a})
    A-fail : ∀{A B ℓ} → Active (cfail {A}{B} ℓ)

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id = inj₁ A-id
  ActiveOrInert (inj A) = inj₂ I-inj
  ActiveOrInert (proj B x) = inj₁ A-proj
  ActiveOrInert (cfun c c₁) = inj₁ A-fun
  ActiveOrInert (cpair c c₁) = inj₁ A-pair
  ActiveOrInert (csum c c₁) = inj₁ A-sum
  ActiveOrInert (cfail ℓ) = inj₁ A-fail

  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B)) → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id {a} = M
  applyCast M v (inj A) {()}
  applyCast M v (proj B ℓ) {a} with PCR.canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | inj₁ cns = M' ⟨ coerce A' B ℓ ⟩
  ...    | inj₂ incns = blame ℓ
  applyCast{Γ} M v (cfun{A₁}{B₁}{A₂}{B₂} c d) {a} =
     ƛ B₁ , (((rename (λ {A} → S_) M) · ((` Z) ⟨ c ⟩)) ⟨ d ⟩)
  applyCast M v (cpair c d) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast M v (csum{A₁}{B₁}{A₂}{B₂} c d) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in
    let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ A₁ , l) (ƛ A₂ , r)
  applyCast M v (cfail ℓ) = blame ℓ

  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M c {()} N

  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M c {()}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M c {()}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B'))) → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L c {()} M N
  
  baseNotInert : ∀ {A B} → (c : Cast (A ⇒ B)) → Base B → ¬ Inert c
  baseNotInert (inj _) () I-inj

  module Red = PCR.Reduction applyCast funCast fstCast sndCast caseCast baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → coerce A B ℓ)
