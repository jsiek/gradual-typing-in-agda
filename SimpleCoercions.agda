module SimpleCoercions where

  open import Data.Nat
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

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

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  coerce : (A : Type) → (B : Type) → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)
  coerce .⋆ B {unk~L} ℓ with eq-unk B
  ... | yes eq rewrite eq = id {⋆} {A-Unk}
  ... | no neq = proj B ℓ {neq}
  coerce A .⋆ {unk~R} ℓ with eq-unk A
  ... | yes eq rewrite eq = id {⋆} {A-Unk}
  ... | no neq = inj A {neq}
  coerce (` ι) (` ι) {base~} ℓ = id {` ι} {A-Base}
  coerce (A ⇒ B) (A' ⇒ B') {fun~ c c₁} ℓ =
    cfun (coerce A' A {c} (flip ℓ) ) (coerce B B' {c₁} ℓ)
  coerce (A `× B) (A' `× B') {pair~ c c₁} ℓ =
    cpair (coerce A A' {c} ℓ ) (coerce B B' {c₁} ℓ)
  coerce (A `⊎ B) (A' `⊎ B') {sum~ c c₁} ℓ =
    csum (coerce A A' {c} ℓ ) (coerce B B' {c₁} ℓ)  

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A i} → Inert (inj A {i})

  data Active : ∀ {A} → Cast A → Set where
    A-proj : ∀{ B ℓ j} → Active (proj B ℓ {j})
    A-fun : ∀{A B A' B' c d} → Active (cfun {A}{B}{A'}{B'} c d)
    A-pair : ∀{A B A' B' c d} → Active (cpair {A}{B}{A'}{B'} c d)
    A-sum : ∀{A B A' B' c d} → Active (csum {A}{B}{A'}{B'} c d)
    A-id : ∀{A a} → Active (id {A}{a})

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id = inj₁ A-id
  ActiveOrInert (inj A) = inj₂ I-inj
  ActiveOrInert (proj B x) = inj₁ A-proj
  ActiveOrInert (cfun c c₁) = inj₁ A-fun
  ActiveOrInert (cpair c c₁) = inj₁ A-pair
  ActiveOrInert (csum c c₁) = inj₁ A-sum

  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR
  
  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id {a} = M
  applyCast M v (inj A) {()}
  applyCast M v (proj B ℓ) {a} with PCR.canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | yes cns = M' ⟨ coerce A' B {cns} ℓ ⟩
  ...    | no incns = blame ℓ
  applyCast{Γ} M v (cfun{A₁}{B₁}{A₂}{B₂} c d) {a} =
     ƛ (((rename (λ {A} → S_) M) · ((` Z) ⟨ c ⟩)) ⟨ d ⟩)
  applyCast M v (cpair c d) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast M v (csum{A₁}{B₁}{A₂}{B₂} c d) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in
    let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ l) (ƛ r)

  funSrc : ∀{A A' B'}
         → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc c ()

  pairSrc : ∀{A A' B'}
         → (c : Cast (A ⇒ (A' `× B'))) → (i : Inert c)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  pairSrc c ()

  sumSrc : ∀{A A' B'}
         → (c : Cast (A ⇒ (A' `⊎ B'))) → (i : Inert c)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  sumSrc c ()

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁)
  dom c ()

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  cod c ()

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         → Cast (A₁ ⇒ A')
  fstC c ()

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  sndC c ()

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Inert c
         → Cast (A₁ ⇒ A')
  inlC c ()

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  inrC c ()
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  module Red = PCR.Reduction applyCast funSrc pairSrc sumSrc
                 dom cod fstC sndC inlC inrC
                 baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → coerce A B {c} ℓ)
