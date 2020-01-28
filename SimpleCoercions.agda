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

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B A' B' c d} → Cross (cfun {A}{B}{A'}{B'} c d)    
    C-pair : ∀{A B A' B' c d} → Cross (cpair {A}{B}{A'}{B'} c d)
    C-sum : ∀{A B A' B' c d} → Cross (csum {A}{B}{A'}{B'} c d)
    
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
  dom (cfun c d) x = c

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (cfun c d) x = d

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (cpair c d) x = c

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (cpair c d) x = d

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (csum c d) x = c

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (csum c d) x = d
  
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
  applyCast M v id {a} = M
  applyCast M v (inj A) {()}
  applyCast M v (proj B ℓ) {a} with canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | yes cns = M' ⟨ coerce A' B {cns} ℓ ⟩
  ...    | no incns = blame ℓ
  applyCast M v (cfun c d) {a} = eta⇒ M (cfun c d) C-fun
  applyCast M v (cpair c d) {a} = eta× M (cpair c d) C-pair
  applyCast M v (csum c d) {a} = eta⊎ M (csum c d) C-sum
     
  open import CastStructure

  cs : CastStruct
  cs = record
             { precast = pcs
             ; applyCast = applyCast
             }

  import ParamCastReduction
  open ParamCastReduction cs public

  import GTLC2CC
  open GTLC2CC Cast (λ A B ℓ {c} → coerce A B {c} ℓ) public
