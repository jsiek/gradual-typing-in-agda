module LazyCast where

  open import Data.Nat
  open import Data.Bool
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
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
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c
    activeFun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c    
    activeErr : ∀ {A B} → (c : Cast (A ⇒ B)) → ¬ (A ⌣ B) → Active c

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert (cast ⋆ B ℓ) with eq-unk B
  ... | yes eq rewrite eq = inj₁ (activeId {a = A-Unk} (cast ⋆ ⋆ ℓ))
  ... | no neq = inj₁ (activeProj (cast ⋆ B ℓ) neq)
  ActiveOrInert (cast (` ι) B ℓ) with (` ι) `⌣ B
  ... | yes c with c
  ...    | base⌣ = inj₁ (activeId {a = A-Base} (cast (` ι) (` ι) ℓ))
  ...    | unk⌣R = inj₂ (inert (λ ()) (cast (` ι) ⋆ ℓ))
  ActiveOrInert (cast (` ι) B ℓ) | no nc = inj₁ (activeErr (cast (` ι) B ℓ) nc)
  ActiveOrInert (cast (A₁ ⇒ A₂) B ℓ) with (A₁ ⇒ A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ ⇒ A₂) B ℓ) nc)
  ... | yes c with c
  ...    | unk⌣R = inj₂ (inert (λ ()) (cast (A₁ ⇒ A₂) ⋆ ℓ))
  ...    | fun⌣{A' = A'}{B' = B'} =
            inj₁ (activeFun (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ))
  ActiveOrInert (cast (A₁ `× A₂) B ℓ) with (A₁ `× A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ `× A₂) B ℓ) nc)
  ... | yes c with c
  ...    | unk⌣R = inj₂ (inert (λ ()) (cast (A₁ `× A₂) ⋆ ℓ))
  ...    | pair⌣{A' = A'}{B' = B'} =
             inj₁ (activePair (cast (A₁ `× A₂) (A' `× B') ℓ))
  ActiveOrInert (cast (A₁ `⊎ A₂) B ℓ) with (A₁ `⊎ A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ `⊎ A₂) B ℓ) nc)
  ... | yes c with c
  ...    | unk⌣R = inj₂ (inert (λ ()) (cast (A₁ `⊎ A₂) ⋆ ℓ))
  ...    | sum⌣{A' = A'}{B' = B'} =
             inj₁ (activeSum (cast (A₁ `⊎ A₂) (A' `⊎ B') ℓ))
  
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
              → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v (cast A A ℓ) {activeId (cast A A ℓ)} = M
  applyCast M v (cast ⋆ B ℓ) {activeProj (cast ⋆ B ℓ) x}
        with PCR.canonical⋆ M v
  ... | ⟨ A , ⟨ M' , ⟨ c' , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq =
            M' ⟨ cast A B ℓ ⟩
  applyCast {Γ} M v (cast (A ⇒ B) (A' ⇒ B') ℓ) {activeFun _} =
     ƛ (((rename (λ {A₂} → S_) M) · ((` Z) ⟨ cast A' A ℓ ⟩)) ⟨ cast B B' ℓ ⟩)
  applyCast {Γ} M v (cast (A `× B) (A' `× B') ℓ) {activePair _} =
     cons (fst M ⟨ cast A A' ℓ ⟩) (snd M ⟨ cast B B' ℓ ⟩)
  applyCast {Γ} M v (cast (A `⊎ B) (A' `⊎ B') ℓ) {activeSum _} =
     let l = inl ((` Z) ⟨ cast A A' ℓ ⟩) in
     let r = inr ((` Z) ⟨ cast B B' ℓ ⟩) in
     case M (ƛ l) (ƛ r)
  applyCast {Γ} {A} {B} M v (cast A B ℓ) {activeErr .(cast A B ℓ) x} =
     blame ℓ

  funSrc : ∀{A A' B'}
         → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc c ()

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁)
  dom c ()

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  cod c ()

  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B')))
          → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M c {()}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B')))
          → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M c {()}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B')))
          → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L c {()} M N
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  module Red = PCR.Reduction applyCast funSrc dom cod fstCast sndCast caseCast
      baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → cast A B ℓ)

