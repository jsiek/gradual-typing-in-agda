module GroundCoercions where

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
    inj : (A : Type) → {g : Ground A} → Cast (A ⇒ ⋆)
    proj : (B : Type) → Label → {g : Ground B} → Cast (⋆ ⇒ B)
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
    cseq : ∀{A B C}
      → Cast (A ⇒ B) → Cast (B ⇒ C)
        ---------------------------
      → Cast (A ⇒ C)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  coerce-to-gnd : (A : Type) → (B : Type) → {g : Ground B} → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)
  coerce-from-gnd : (A : Type) → (B : Type) → {g : Ground A} → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)
  
  coerce-to⋆ : (A : Type) → Label → Cast (A ⇒ ⋆)
  coerce-to⋆ A ℓ with eq-unk A
  ... | inj₁ eq rewrite eq = id {⋆} {A-Unk}
  ... | inj₂ neq with ground? A
  ...     | inj₁ g = inj A {g}
  ...     | inj₂ ng with ground A {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ = cseq (coerce-to-gnd A G {g} {c} ℓ) (inj G {g})

  coerce-from⋆ : (B : Type) → Label → Cast (⋆ ⇒ B)
  coerce-from⋆ B ℓ with eq-unk B
  ... | inj₁ eq rewrite eq = id {⋆} {A-Unk}
  ... | inj₂ neq with ground? B
  ...     | inj₁ g = proj B ℓ {g}
  ...     | inj₂ ng with ground B {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ = cseq (proj G ℓ {g}) (coerce-from-gnd G B {g} {Sym~ c} ℓ) 

  coerce-to-gnd .⋆ .Nat {G-Base B-Nat} {unk~L} ℓ = proj Nat ℓ {G-Base B-Nat}
  coerce-to-gnd .Nat .Nat {G-Base B-Nat} {nat~} ℓ = id {Nat} {A-Nat}
  coerce-to-gnd .⋆ .𝔹 {G-Base B-Bool} {unk~L} ℓ = proj 𝔹 ℓ {G-Base B-Bool}
  coerce-to-gnd .𝔹 .𝔹 {G-Base B-Bool} {bool~} ℓ = id {𝔹}{A-Bool}
  coerce-to-gnd .⋆ .(⋆ ⇒ ⋆) {G-Fun} {unk~L} ℓ = proj (⋆ ⇒ ⋆) ℓ {G-Fun}
  coerce-to-gnd (A₁ ⇒ A₂) .(⋆ ⇒ ⋆) {G-Fun} {fun~ c c₁} ℓ =
     cfun (coerce-from⋆ A₁ (flip ℓ)) (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd .⋆ .(⋆ `× ⋆) {G-Pair} {unk~L} ℓ = proj (⋆ `× ⋆) ℓ {G-Pair}
  coerce-to-gnd (A₁ `× A₂) .(⋆ `× ⋆) {G-Pair} {pair~ c c₁} ℓ =
     cpair (coerce-to⋆ A₁ ℓ) (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd .⋆ .(⋆ `⊎ ⋆) {G-Sum} {unk~L} ℓ = proj (⋆ `⊎ ⋆) ℓ {G-Sum}
  coerce-to-gnd (A₁ `⊎ A₂) .(⋆ `⊎ ⋆) {G-Sum} {sum~ c c₁} ℓ =
     csum (coerce-to⋆ A₁ ℓ) (coerce-to⋆ A₂ ℓ)
  
  coerce-from-gnd .Nat .⋆ {G-Base B-Nat} {unk~R} ℓ = inj Nat {G-Base B-Nat}
  coerce-from-gnd .Nat .Nat {G-Base B-Nat} {nat~} ℓ = id {Nat}{A-Nat}
  coerce-from-gnd .𝔹 .⋆ {G-Base B-Bool} {unk~R} ℓ = inj 𝔹 {G-Base B-Bool}
  coerce-from-gnd .𝔹 .𝔹 {G-Base B-Bool} {bool~} ℓ = id {𝔹}{A-Bool}
  coerce-from-gnd .(⋆ ⇒ ⋆) .⋆ {G-Fun} {unk~R} ℓ = inj (⋆ ⇒ ⋆) {G-Fun}
  coerce-from-gnd .(⋆ ⇒ ⋆) (B₁ ⇒ B₂) {G-Fun} {fun~ c c₁} ℓ =
     cfun (coerce-to⋆ B₁ (flip ℓ)) (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd .(⋆ `× ⋆) .⋆ {G-Pair} {unk~R} ℓ = inj (⋆ `× ⋆) {G-Pair}
  coerce-from-gnd .(⋆ `× ⋆) (B₁ `× B₂) {G-Pair} {pair~ c c₁} ℓ =
     cpair (coerce-from⋆ B₁ ℓ) (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd .(⋆ `⊎ ⋆) .⋆ {G-Sum} {unk~R} ℓ = inj (⋆ `⊎ ⋆) {G-Sum}
  coerce-from-gnd .(⋆ `⊎ ⋆) (B₁ `⊎ B₂) {G-Sum} {sum~ c c₁} ℓ =
     csum (coerce-from⋆ B₁ ℓ) (coerce-from⋆ B₂ ℓ)

  coerce : (A : Type) → (B : Type) → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)
  coerce .⋆ B {unk~L} ℓ = coerce-from⋆ B ℓ
  coerce A .⋆ {unk~R} ℓ = coerce-to⋆ A ℓ
  coerce Nat Nat {nat~} ℓ = id {Nat} {A-Nat}
  coerce 𝔹 𝔹 {bool~} ℓ = id {𝔹} {A-Bool}
  coerce (A ⇒ B) (A' ⇒ B') {fun~ c c₁} ℓ =
    cfun (coerce A' A {Sym~ c} (flip ℓ) ) (coerce B B' {c₁} ℓ)
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
    A-seq : ∀{A B C c d} → Active (cseq {A}{B}{C} c d)

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id = inj₁ A-id
  ActiveOrInert (inj A) = inj₂ I-inj
  ActiveOrInert (proj B x) = inj₁ A-proj
  ActiveOrInert (cfun c c₁) = inj₁ A-fun
  ActiveOrInert (cpair c c₁) = inj₁ A-pair
  ActiveOrInert (csum c c₁) = inj₁ A-sum
  ActiveOrInert (cseq c c₁) = inj₁ A-seq

  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR
  
  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B)) → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id {a} = M
  applyCast M v (inj A) {()}
  applyCast{Γ} M v (proj B ℓ {gb}) {a} with PCR.canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ I-inj {A'}{ga} , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with gnd-eq? A' B {ga} {gb}
  ...    | inj₂ neq = blame ℓ
  ...    | inj₁ eq = G  {- odd work-around -}
           where G : Γ ⊢ B
                 G rewrite eq = M'
  applyCast{Γ} M v (cfun{A₁}{B₁}{A₂}{B₂} c d) {a} =
     ƛ B₁ , (((rename (λ {A} → S_) M) · ((` Z) ⟨ c ⟩)) ⟨ d ⟩)
  applyCast M v (cpair c d) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast M v (csum{A₁}{B₁}{A₂}{B₂} c d) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in
    let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ A₁ , l) (ƛ A₂ , r)
  applyCast M x (cseq c d) = (M ⟨ c ⟩) ⟨ d ⟩

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
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → coerce A B {c} ℓ)
