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

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B C D} → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D))) → Cross c
    C-pair : ∀{A B C D} → (c : Cast ((A `× B) ⇒ (C `× D))) → Cross c
    C-sum : ∀{A B C D} → (c : Cast ((A `⊎ B) ⇒ (C `⊎ D))) → Cross c
    
  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ c ()

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× c ()

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ c ()

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
  dom (cast (A ⇒ B) (C ⇒ D) ℓ) x = cast C A ℓ

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (cast (A ⇒ B) (C ⇒ D) ℓ) x = cast B D ℓ

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (cast (A `× B) (C `× D) ℓ) x = cast A C ℓ

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (cast (A `× B) (C `× D) ℓ) x = cast B D ℓ

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (cast (A `⊎ B) (C `⊎ D) ℓ) x = cast A C ℓ

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (cast (A `⊎ B) (C `⊎ D) ℓ) x = cast B D ℓ
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  open import PreCastStructure
  
  pcs : PreCastStruct
  pcs = record
             { Cast = Cast
             ; Inert = Inert
             ; Active = Active
             ; ActiveOrInert = ActiveOrInert
             ; Cross = Cross
             ; Inert-Cross⇒ = Inert-Cross⇒
             ; Inert-Cross× = Inert-Cross×
             ; Inert-Cross⊎ = Inert-Cross⊎
             ; dom = dom
             ; cod = cod
             ; fstC = fstC
             ; sndC = sndC
             ; inlC = inlC
             ; inrC = inrC
             ; baseNotInert = baseNotInert
             }

  import ParamCastAux
  open ParamCastAux pcs

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
              → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v (cast A A ℓ) {activeId (cast A A ℓ)} = M
  applyCast M v (cast ⋆ B ℓ) {activeProj (cast ⋆ B ℓ) x}
        with canonical⋆ M v
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

  open import CastStructure

  cs : CastStruct
  cs = record
             { precast = pcs
             ; applyCast = applyCast
             }

  import ParamCastReduction
  open ParamCastReduction cs public

  import GTLC2CC
  open GTLC2CC Cast (λ A B ℓ {c} → (cast A B ℓ)) public

