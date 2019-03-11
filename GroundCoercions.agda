{-

  This module formalizes the λC calculus (Siek, Thiemann, Wadler 2015)
  and proves type safety via progress and preservation. The calculus
  uses Henglein's coercions to represent casts, but this calculus is
  not space efficient. This calculus is helpful in linking λB to λS
  (the space-efficient version) and it is useful for pedagogical
  purposes.

  This module is relatively small because it reuses the definitions
  and proofs from the Parameterized Cast Calculus. This module just
  has to provide the appropriate parameters.

-}

module GroundCoercions where

  open import Data.Nat
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

  {-
 
  The following data type defines the syntax and type system of the
  Coercion Calculus. We omit the failure coercion because it is not
  needed. (It is needed in λS.)

  -}

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

  {-

  For the compilation of the GTLC to this cast calculus, we need a
  function for compiling a cast between two types into a coercion.
  The coerce function, defined below, does this. Unfortunately, Agda
  would not accept the version of coerce given in Figure 4 of the
  paper of Siek, Thiemann, and Wadler (2015). To work around this
  issue, we added the auxilliary functions coerse-to-gnd and
  coerce-from-gnd. In initial version of these functions contained
  considerable repetition of code, which we reduced by abstracting the
  coerce-to⋆ and coerce-from⋆ functions.

  -}

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

  {-

  We instantiate the GTLC2CC module, creating a compiler from the GTLC
  to λC.

  -}

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → coerce A B {c} ℓ)

  {-

  To prepare for instantiating the ParamCastReduction module, we
  categorize the coercions as either inert or active.  The inert
  (value-forming) coercions are the injection and function coercions.

   -}

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A i} → Inert (inj A {i})
    I-fun : ∀{A B A' B' c d} → Inert (cfun {A}{B}{A'}{B'} c d)

  {-
  The rest of the coercions are active.
  -}

  data Active : ∀ {A} → Cast A → Set where
    A-proj : ∀{ B ℓ j} → Active (proj B ℓ {j})
    A-pair : ∀{A B A' B' c d} → Active (cpair {A}{B}{A'}{B'} c d)
    A-sum : ∀{A B A' B' c d} → Active (csum {A}{B}{A'}{B'} c d)
    A-id : ∀{A a} → Active (id {A}{a})
    A-seq : ∀{A B C c d} → Active (cseq {A}{B}{C} c d)

  {-

  We did not forget about any of the coercions in our categorization.

  -}

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id = inj₁ A-id
  ActiveOrInert (inj A) = inj₂ I-inj
  ActiveOrInert (proj B x) = inj₁ A-proj
  ActiveOrInert (cfun c c₁) = inj₂ I-fun
  ActiveOrInert (cpair c c₁) = inj₁ A-pair
  ActiveOrInert (csum c c₁) = inj₁ A-sum
  ActiveOrInert (cseq c c₁) = inj₁ A-seq

  {-

  We instantiate the outer module of ParamCastReduction, obtaining the
  definitions for values and frames.

  -}
  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  {- 

  To instaniate the inner module that defines reduction and progress,
  we need to define a few more functions. The first is applyCast,
  which applies an active cast to a value. We comment each case with
  the reduction rule from Siek, Thiemann, and Wadler (2015). The
  definition of applyCast was driven by pattern matching on the
  parameter {c : Cast (A ⇒ B)}. (Perhaps it would have been better
  to pattern match on {a : Active c}.)

  -}

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B)) → ∀ {a : Active c} → Γ ⊢ B
  {-
    V⟨id⟩    —→    V
   -}
  applyCast M v id {a} = M
  {-
    V⟨G!⟩⟨G?⟩    —→    V
    V⟨G!⟩⟨H?p⟩   —→   blame p  if G ≠ H
   -}
  applyCast{Γ} M v (proj B ℓ {gb}) {a} with PCR.canonical⋆ M v
  ... | ⟨ G , ⟨ V , ⟨ c , ⟨ I-inj {G}{ga} , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with gnd-eq? G B {ga} {gb}
  ...    | inj₂ neq = blame ℓ
  ...    | inj₁ eq = g  {- odd work-around -}
           where g : Γ ⊢ B
                 g rewrite eq = V
  {-
   V⟨c ; d⟩     —→    V⟨c⟩⟨d⟩
   -}
  applyCast M x (cseq c d) = (M ⟨ c ⟩) ⟨ d ⟩
  
  applyCast M v (cpair c d) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
    
  applyCast M v (csum{A₁}{B₁}{A₂}{B₂} c d) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in
    let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ l) (ƛ r)
    
  applyCast {Γ} M v (cfun {A₁} {B₁} {A₂} {B₂} c d) {()}
  applyCast M v (inj A) {()}

  {-
   The following functions handle every elimination form, saying what
   happens when the value is wrapped in an inert cast.  For function
   application, we distribute the cast to the argument and return
   value.
   -}

  {-
   V⟨c→d⟩ W    —→     (V  W⟨c⟩)⟨d⟩
  -}
  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B')))
          → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M (cfun c d) {I-fun} N = (M · (N ⟨ c ⟩)) ⟨ d ⟩


  {-

  The functions for pairs and sums are vacuous because we categorized
  these casts as inert, not active.

  -}
  
  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B')))
          → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M c {()}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B')))
          → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M c {()}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B')))
           → ∀ {i : Inert c}
           → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L c {()} M N
  
  {-
  Finally, we show that casts to base type are not inert.
  -}

  baseNotInert : ∀ {A B} → (c : Cast (A ⇒ B)) → Base B → ¬ Inert c
  baseNotInert c B-Nat ()
  baseNotInert c B-Bool ()

  {-
  We now instantiate the inner module of ParamCastReduction, thereby
  proving type safety for λC. 
  -}

  module Red = PCR.Reduction applyCast funCast fstCast sndCast caseCast
                     baseNotInert
  open Red

