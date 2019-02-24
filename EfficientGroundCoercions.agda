{-

  This module formalizes the λS calculus (Siek, Thiemann, Wadler 2015)
  and proves type safety via progress and preservation. The calculus
  uses Henglein's coercions to represent casts, and acheive space
  efficiency.

  This module is relatively small because it reuses the definitions
  and proofs from the Efficient Parameterized Cast Calculus. This
  module just has to provide the appropriate parameters, the most
  important of which is the compose function, written ⨟.

-}

module EfficientGroundCoercions where

  open import Agda.Primitive
  open import Data.Nat
  open import Data.Nat.Properties
  open ≤-Reasoning {- renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_) -}
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  
  data IntermediateCast : Type → Set
  data GroundCast : Type → Set
  data Cast : Type → Set

  {-

   The following Cast data type (together with the data types
   IntermediateCast and GroundCast) define a normal form for
   coercions, following the grammar in Figure 5 of Siek, Thiemann, and
   Wadler (2015).

  -}

  data Cast where
    id⋆ : Cast (⋆ ⇒ ⋆)
    proj : ∀{B}
       → (G : Type) → Label → IntermediateCast (G ⇒ B) → {g : Ground G}
       → Cast (⋆ ⇒ B)
    intmd : ∀{A B}
       → IntermediateCast (A ⇒ B)
       → Cast (A ⇒ B)

  data IntermediateCast where
    inj : ∀{A}
       → (G : Type)
       → GroundCast (A ⇒ G)
       → {g : Ground G}
       → IntermediateCast (A ⇒ ⋆)
    gnd : ∀{A B}
       → (g : GroundCast (A ⇒ B))
       → IntermediateCast (A ⇒ B)
    cfail : ∀{A B} (G : Type) → (H : Type) → Label → {a : A ≢ ⋆}
       → IntermediateCast (A ⇒ B)

  data GroundCast where
    cid : ∀ {A : Type} {a : Base A} → GroundCast (A ⇒ A)
    _↣_ : ∀ {A B A' B'}
      → (c : Cast (B ⇒ A)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → GroundCast ((A ⇒ A') ⇒ (B ⇒ B'))
    _×'_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → GroundCast ((A `× A') ⇒ (B `× B'))
    _+'_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → GroundCast ((A `⊎ A') ⇒ (B `⊎ B'))

  {-

   We instantiate the ParamCastCalculus module to obtain the syntax
   and type system of the cast calculus and the definition of
   substitution.

  -}

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  {-

   For the compilation of the GTLC to this cast calculus, we need a
   function for compiling a cast between two types into a coercion.
   Such a function is not directly given by Siek, Thiemann, and Wadler
   (2015), but they do provide a compilation from the coercions of λC
   to λS. Here we give a direction compilation from the casts of λB to
   the coercions of λS. The following definitions are more complex
   than one would hope for because of a workaround to satisfy Agda's
   termination checker.

  -}

  coerce-to-gnd : (A : Type) → (B : Type) → {g : Ground B}
     → ∀ {c : A ~ B}{a : A ≢ ⋆} → Label → GroundCast (A ⇒ B)
  coerce-from-gnd : (A : Type) → (B : Type) → {g : Ground A}
     → ∀ {c : A ~ B}{b : B ≢ ⋆} → Label → GroundCast (A ⇒ B)

  coerce-gnd-to⋆ : (A : Type) → {g : Ground A} → Label → Cast (A ⇒ ⋆)
  coerce-gnd-to⋆ .Nat {G-Base B-Nat} ℓ = intmd (inj Nat (cid{Nat}{B-Nat}) {G-Base B-Nat})
  coerce-gnd-to⋆ .𝔹 {G-Base B-Bool} ℓ = intmd (inj 𝔹 (cid{𝔹}{B-Bool}) {G-Base B-Bool})
  coerce-gnd-to⋆ .(⋆ ⇒ ⋆) {G-Fun} ℓ = intmd (inj (⋆ ⇒ ⋆) (id⋆ ↣ id⋆) {G-Fun})
  coerce-gnd-to⋆ .(⋆ `× ⋆) {G-Pair} ℓ = intmd (inj (⋆ `× ⋆) (id⋆ ×' id⋆) {G-Pair})
  coerce-gnd-to⋆ .(⋆ `⊎ ⋆) {G-Sum} ℓ = intmd (inj  (⋆ `⊎ ⋆) (id⋆ +' id⋆) {G-Sum})

  coerce-gnd-from⋆ : (B : Type) → {g : Ground B} → Label → Cast (⋆ ⇒ B)
  coerce-gnd-from⋆ .Nat {G-Base B-Nat} ℓ = proj Nat ℓ (gnd (cid{Nat}{B-Nat})) {G-Base B-Nat}
  coerce-gnd-from⋆ .𝔹 {G-Base B-Bool} ℓ = proj 𝔹 ℓ (gnd (cid{𝔹}{B-Bool})) {G-Base B-Bool}
  coerce-gnd-from⋆ .(⋆ ⇒ ⋆) {G-Fun} ℓ = proj (⋆ ⇒ ⋆) ℓ (gnd (id⋆ ↣ id⋆)) {G-Fun}
  coerce-gnd-from⋆ .(⋆ `× ⋆) {G-Pair} ℓ = proj (⋆ `× ⋆) ℓ (gnd (id⋆ ×' id⋆)) {G-Pair}
  coerce-gnd-from⋆ .(⋆ `⊎ ⋆) {G-Sum} ℓ = proj (⋆ `⊎ ⋆) ℓ (gnd (id⋆ +' id⋆)) {G-Sum}
  
  coerce-to⋆ : (A : Type) → Label → Cast (A ⇒ ⋆)
  coerce-to⋆ A ℓ with eq-unk A
  ... | inj₁ eq rewrite eq = id⋆ 
  ... | inj₂ neq with ground? A
  ...     | inj₁ g = coerce-gnd-to⋆ A {g} ℓ
  ...     | inj₂ ng with ground A {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ = intmd (inj G (coerce-to-gnd A G {g}{c}{neq} ℓ) {g})

  coerce-from⋆ : (B : Type) → Label → Cast (⋆ ⇒ B)
  coerce-from⋆ B ℓ with eq-unk B
  ... | inj₁ eq rewrite eq = id⋆
  ... | inj₂ neq with ground? B
  ...     | inj₁ g = coerce-gnd-from⋆ B {g} ℓ
  ...     | inj₂ ng with ground B {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ = proj G ℓ (gnd (coerce-from-gnd G B {g}{Sym~ c}{neq} ℓ)) {g} 

  coerce-to-gnd .⋆ .Nat {G-Base B-Nat} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd .Nat .Nat {G-Base B-Nat} {nat~} ℓ = cid{Nat}{B-Nat}
  coerce-to-gnd .⋆ .𝔹 {G-Base B-Bool} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd .𝔹 .𝔹 {G-Base B-Bool} {bool~} ℓ = cid{𝔹}{B-Bool}
  coerce-to-gnd .⋆ .(⋆ ⇒ ⋆) {G-Fun} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ ⇒ A₂) .(⋆ ⇒ ⋆) {G-Fun} {fun~ c c₁} ℓ =
     (coerce-from⋆ A₁ ℓ) ↣ (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd .⋆ .(⋆ `× ⋆) {G-Pair} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ `× A₂) .(⋆ `× ⋆) {G-Pair} {pair~ c c₁} ℓ =
     (coerce-to⋆ A₁ ℓ) ×' (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd .⋆ .(⋆ `⊎ ⋆) {G-Sum} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ `⊎ A₂) .(⋆ `⊎ ⋆) {G-Sum} {sum~ c c₁} ℓ =
     (coerce-to⋆ A₁ ℓ) +' (coerce-to⋆ A₂ ℓ)

  coerce-from-gnd .Nat .⋆ {G-Base B-Nat} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .Nat .Nat {G-Base B-Nat} {nat~} ℓ = cid{Nat}{B-Nat}
  coerce-from-gnd .𝔹 .⋆ {G-Base B-Bool} {unk~R}{neq} ℓ =  ⊥-elim (neq refl)
  coerce-from-gnd .𝔹 .𝔹 {G-Base B-Bool} {bool~} ℓ = cid{𝔹}{B-Bool}
  coerce-from-gnd .(⋆ ⇒ ⋆) .⋆ {G-Fun} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .(⋆ ⇒ ⋆) (B₁ ⇒ B₂) {G-Fun} {fun~ c c₁} ℓ =
     (coerce-to⋆ B₁ ℓ) ↣ (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd .(⋆ `× ⋆) .⋆ {G-Pair} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .(⋆ `× ⋆) (B₁ `× B₂) {G-Pair} {pair~ c c₁} ℓ =
     (coerce-from⋆ B₁ ℓ) ×' (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd .(⋆ `⊎ ⋆) .⋆ {G-Sum} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .(⋆ `⊎ ⋆) (B₁ `⊎ B₂) {G-Sum} {sum~ c c₁} ℓ =
     (coerce-from⋆ B₁ ℓ) +' (coerce-from⋆ B₂ ℓ)

  coerce : (A : Type) → (B : Type) → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)
  coerce .⋆ B {unk~L} ℓ = coerce-from⋆ B ℓ
  coerce A .⋆ {unk~R} ℓ = coerce-to⋆ A ℓ
  coerce Nat Nat {nat~} ℓ = intmd (gnd (cid {Nat} {B-Nat}))
  coerce 𝔹 𝔹 {bool~} ℓ = intmd (gnd (cid {𝔹} {B-Bool}))
  coerce (A ⇒ B) (A' ⇒ B') {fun~ c c₁} ℓ =
    intmd (gnd ((coerce A' A {Sym~ c} (flip ℓ)) ↣ (coerce B B' {c₁} ℓ)))
  coerce (A `× B) (A' `× B') {pair~ c c₁} ℓ =
    intmd (gnd ((coerce A A' {c} ℓ ) ×' (coerce B B' {c₁} ℓ)))
  coerce (A `⊎ B) (A' `⊎ B') {sum~ c c₁} ℓ =
    intmd (gnd ((coerce A A' {c} ℓ) +' (coerce B B' {c₁} ℓ)))

  {-

   We instantiate the GTLC2CC module, creating a compiler from the
   GTLC to λC.

  -}
  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → coerce A B {c} ℓ)


  {-

   To prepare for instantiating the ParamCastReduction module, we
   categorize the coercions as either inert or active.  We do this for
   each of the three kinds of coercions: for the ground, intermeidate,
   and top-level coercions. For the ground coercions, only the
   function coercion is inert.

   -}
  data InertGround : ∀ {A} → GroundCast A → Set where
    I-cfun : ∀{A B A' B'}{s : Cast (B ⇒ A)} {t : Cast (A' ⇒ B')}
          → InertGround (_↣_ {A}{B}{A'}{B'} s t)

  {-

   The other three ground coercions are active.

  -}
  data ActiveGround : ∀ {A} → GroundCast A → Set where
    A-cpair : ∀{A B A' B'}{s : Cast (A ⇒ B)} {t : Cast (A' ⇒ B')}
          → ActiveGround (_×'_{A}{B}{A'}{B'} s t)
    A-csum : ∀{A B A' B'}{s : Cast (A ⇒ B)} {t : Cast (A' ⇒ B')}
          → ActiveGround (_+'_{A}{B}{A'}{B'} s t)
    A-cid : ∀{B b}
          → ActiveGround (cid {B}{b})

  {-

   Of the intermediate coercions, injection is inert and
   so is an inert ground coercion.
   
  -}

  data InertIntmd : ∀ {A} → IntermediateCast A → Set where
    I-inj : ∀{A G i}{g : GroundCast (A ⇒ G)}
          → InertIntmd (inj {A} G g {i})
    I-gnd : ∀{A B}{g : GroundCast (A ⇒ B)}
          → InertGround g
          → InertIntmd (gnd {A}{B} g)

  {-
  
   A failure coercion is active.  An active ground coercion is also an
   active intermediate coercion.

   -}

  data ActiveIntmd : ∀ {A} → IntermediateCast A → Set where
    A-gnd : ∀{A B}{g : GroundCast (A ⇒ B)}
          → ActiveGround g
          → ActiveIntmd (gnd {A}{B} g)
    A-cfail : ∀{A B G H ℓ nd}
          → ActiveIntmd (cfail {A}{B} G H ℓ {nd})

  {-

   At the top level, an inert intermediate coercion 
   is also an inert top-level coercion.

  -}

  data Inert : ∀ {A} → Cast A → Set where
    I-intmd : ∀{A B}{i : IntermediateCast (A ⇒ B)}
          → InertIntmd i
          → Inert (intmd{A}{B} i)

  {-

  The rest of the top-level coercions are active.  That is, the
  identity and projection coercions and the active intermediate
  coercions.

  -}
  data Active : ∀ {A} → Cast A → Set where
    A-id⋆ : Active id⋆
    A-proj : ∀{B G ℓ g} {i : IntermediateCast (G ⇒ B)}
          → Active (proj{B} G ℓ i {g})
    A-intmd : ∀{A B}{i : IntermediateCast (A ⇒ B)}
          → ActiveIntmd i
          → Active (intmd{A}{B} i)

  {-

   Regarding this categorization, we did not leave behind any
   coercions.

  -}
  
  ActiveOrInertGnd : ∀{A} → (c : GroundCast A) → ActiveGround c ⊎ InertGround c
  ActiveOrInertGnd cid = inj₁ A-cid
  ActiveOrInertGnd (c ↣ d) = inj₂ I-cfun
  ActiveOrInertGnd (c ×' d) = inj₁ A-cpair
  ActiveOrInertGnd (c +' d) = inj₁ A-csum

  ActiveOrInertIntmd : ∀{A} → (c : IntermediateCast A) → ActiveIntmd c ⊎ InertIntmd c
  ActiveOrInertIntmd (inj G x) = inj₂ I-inj
  ActiveOrInertIntmd (gnd g) with ActiveOrInertGnd g
  ... | inj₁ a = inj₁ (A-gnd a)
  ... | inj₂ i = inj₂ (I-gnd i)
  ActiveOrInertIntmd (cfail G H x) = inj₁ A-cfail

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id⋆ = inj₁ A-id⋆
  ActiveOrInert (proj G x x₁) = inj₁ A-proj
  ActiveOrInert (intmd i) with ActiveOrInertIntmd i
  ... | inj₁ a = inj₁ (A-intmd a)
  ... | inj₂ j = inj₂ (I-intmd j)
  
  {-

  We instantiate the outer module of EfficientParamCasts, obtaining
  the definitions for values and frames.

  -}

  import EfficientParamCasts
  module EPCR = EfficientParamCasts Cast Inert Active ActiveOrInert
  open EPCR

  {-
   The following functions compute the size of the three kinds of coercions.
   These are used in the termination argument of the compose function.
   -}

  size-gnd : ∀{A} → GroundCast A → ℕ
  size-intmd : ∀{A} → IntermediateCast A → ℕ  
  size-cast : ∀{A} → Cast A → ℕ  

  size-gnd cid = 1
  size-gnd (c ↣ d) = 1 + size-cast c + size-cast d
  size-gnd (c ×' d) = 1 + size-cast c + size-cast d
  size-gnd (c +' d) =  1 + size-cast c + size-cast d

  size-intmd (inj G g) = 2 + size-gnd g
  size-intmd (gnd g) = 1 + size-gnd g
  size-intmd (cfail G H ℓ) = 1
  
  size-cast id⋆ = 1
  size-cast (proj G ℓ i) = 2 + size-intmd i
  size-cast (intmd i) = 1 + size-intmd i

  size-gnd-pos : ∀{A c} → size-gnd {A} c ≢ zero
  size-gnd-pos {.(_ ⇒ _)} {cid} = λ ()
  size-gnd-pos {.((_ ⇒ _) ⇒ (_ ⇒ _))} {c ↣ d} = λ ()
  size-gnd-pos {.(_ `× _ ⇒ _ `× _)} {c ×' d} = λ ()
  size-gnd-pos {.(_ `⊎ _ ⇒ _ `⊎ _)} {c +' d} = λ ()

  size-intmd-pos : ∀{A c} → size-intmd {A} c ≢ zero
  size-intmd-pos {.(_ ⇒ ⋆)} {inj G x} = λ ()
  size-intmd-pos {.(_ ⇒ _)} {gnd g} = λ ()
  size-intmd-pos {.(_ ⇒ _)} {cfail G H x} = λ ()

  size-cast-pos : ∀{A c} → size-cast {A} c ≢ zero
  size-cast-pos {.(⋆ ⇒ ⋆)} {id⋆} = λ ()
  size-cast-pos {.(⋆ ⇒ _)} {proj G x x₁} = λ ()
  size-cast-pos {.(_ ⇒ _)} {intmd x} = λ ()

  plus-zero1 : ∀{a}{b} → a + b ≡ zero → a ≡ zero
  plus-zero1 {zero} {b} p = refl
  plus-zero1 {suc a} {b} ()

  plus-gnd-pos : ∀{A}{B}{c}{d} → size-gnd{A} c + size-gnd{B} d ≤ zero → ⊥
  plus-gnd-pos {A}{B}{c}{d} p =
     let cd-z = n≤0⇒n≡0 p in
     let c-z = plus-zero1 {size-gnd c}{size-gnd d} cd-z in
     contradiction c-z (size-gnd-pos{A}{c})

  plus-cast-pos : ∀{A}{B}{c}{d} → size-cast{A} c + size-cast{B} d ≤ zero → ⊥
  plus-cast-pos {A}{B}{c}{d} p =
     let cd-z = n≤0⇒n≡0 p in
     let c-z = plus-zero1 {size-cast c}{size-cast d} cd-z in
     contradiction c-z (size-cast-pos{A}{c})

  plus1-suc : ∀{n} → n + 1 ≡ suc n
  plus1-suc {zero} = refl
  plus1-suc {suc n} = cong suc plus1-suc

  {- 
    Ugh, the following reasoning is tedious! Is there a better way? -Jeremy
  -}

  inequality-3 : ∀{sc sd sc1 sd1 n}
       → sc + sd + suc (sc1 + sd1) ≤ n
       → sc + sc1 ≤ n
  inequality-3{sc}{sd}{sc1}{sd1}{n} m =
    begin sc + sc1
               ≤⟨ m≤m+n (sc + sc1) (sd + (sd1 + 1)) ⟩
          (sc + sc1) + (sd + (sd1 + 1))
               ≤⟨ ≤-reflexive (+-assoc (sc) (sc1) (sd + (sd1 + 1))) ⟩
          sc + (sc1 + (sd + (sd1 + 1)))
               ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc})
                              (sym (+-assoc (sc1) (sd) (sd1 + 1)))) ⟩
          sc + ((sc1 + sd) + (sd1 + 1))
               ≤⟨ ≤-reflexive (cong₂ (_+_) ((refl{x = sc}))
                                         (cong₂ (_+_) (+-comm (sc1) (sd)) refl)) ⟩
          sc + ((sd + sc1) + (sd1 + 1))
               ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc})
                                (+-assoc (sd) (sc1) (sd1 + 1))) ⟩
          sc + (sd + (sc1 + (sd1 + 1)))
               ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc})
                            (cong₂ (_+_) (refl{x = sd})
                                 (sym (+-assoc (sc1) (sd1) 1)))) ⟩
          sc + (sd + ((sc1 + sd1) + 1))
               ≤⟨ ≤-reflexive (sym (+-assoc (sc) (sd) (sc1 + sd1 + 1))) ⟩
          (sc + sd) + ((sc1 + sd1) + 1)
               ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc + sd}) plus1-suc) ⟩
          (sc + sd) + suc (sc1 + sd1)
               ≤⟨ m ⟩
          n
    ∎  

  inequality-1 : ∀{sc sd sc1 sd1 n}
       → sc + sd + suc (sc1 + sd1) ≤ n
       → sc1 + sc ≤ n
  inequality-1{sc}{sd}{sc1}{sd1}{n} m =
    begin sc1 + sc
               ≤⟨ ≤-reflexive (+-comm sc1 sc) ⟩
          sc + sc1
               ≤⟨ inequality-3{sc} m ⟩
          n
    ∎  

  inequality-2 : ∀{sc sd sc1 sd1 n}
       → sc + sd + suc (sc1 + sd1) ≤ n 
       → sd + sd1 ≤ n
  inequality-2{sc}{sd}{sc1}{sd1}{n} m =
    begin
      sd + sd1
           ≤⟨ m≤m+n (sd + sd1) (sc + (sc1 + 1)) ⟩
      (sd + sd1) + (sc + (sc1 + 1))
           ≤⟨ ≤-reflexive (+-assoc sd sd1 (sc + (sc1 + 1))) ⟩
      sd + (sd1 + (sc + (sc1 + 1)))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd}) (sym (+-assoc sd1 sc (sc1 + 1)))) ⟩
      sd + ((sd1 + sc) + (sc1 + 1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd})
                             (cong₂ (_+_) (+-comm sd1 sc) (refl{x = sc1 + 1}))) ⟩
      sd + ((sc + sd1) + (sc1 + 1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd}) (+-assoc sc sd1 (sc1 + 1))) ⟩
      sd + (sc + (sd1 + (sc1 + 1)))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd})
                 (cong₂ (_+_) (refl{x = sc}) (sym (+-assoc sd1 sc1 1)))) ⟩
      sd + (sc + ((sd1 + sc1) + 1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd})
                 (cong₂ (_+_) (refl{x = sc}) plus1-suc)) ⟩
      sd + (sc + (suc (sd1 + sc1)))
           ≤⟨  ≤-reflexive (sym (+-assoc sd sc (suc (sd1 + sc1)))) ⟩
      (sd + sc) + (suc (sd1 + sc1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (+-comm sd sc) (refl{x = suc (sd1 + sc1)})) ⟩
      (sc + sd) + (suc (sd1 + sc1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc + sd}) (cong suc (+-comm sd1 sc1))) ⟩
      (sc + sd) + suc (sc1 + sd1)          
           ≤⟨ m ⟩
      n
    ∎  

  m+n≡0⇒n≡0 : ∀{m n : ℕ} → m + n ≡ zero → n ≡ zero
  m+n≡0⇒n≡0 {zero} {n} p = p
  m+n≡0⇒n≡0 {suc m} {n} ()

  {- 

    Next we define the composition operation from Figure 5 of Siek,
    Thiemann, and Wadler (2015). We break down the operation into
    a family of three functions in Agda, which enables us to capture
    more invariants about the type of the resulting coercion,
    which is necessary to pass the Agda type checker.
    First, observe that in equation #6, we compose two ground
    coercions (g ⨟ h) and the result must be a ground coercion.
    Second, in equation #5 we compose an intermediate coercion
    with a top-level coercion (i ⨟ t) and the result must
    be an intermeidate coercion. Thus, we shall define 
    composition with three functions in Agda,
    * (s ⨟ t) composition of top-level coercions
    * (i ⨟' t) composition of an intermediate coercion with a top-level coercion
    * (g `⨟ h) composition of two ground coercions

    Each of the equations from Figure 5 are placed in one of these
    three functions according to which kinds of coercions they refer
    to.

   -}

   {-
    
     The composition of ground coercions applies composition of
     top-level coercions, so we forward declare the later.

    -}

  _⨟_ : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
          → {n : ℕ} → {m : size-cast c + size-cast d ≤ n }
          → Cast (A ⇒ C)

  {- 
   
    The following is composition for ground coercions, which covers
    rules #1 and #2 from Figure 5 of Siek, Thiemann, and Wadler
    (2015).

   -}
  _`⨟_ : ∀{A B C} → (c : GroundCast (A ⇒ B)) → (d : GroundCast (B ⇒ C))
          → {n : ℕ} → {m : size-gnd c + size-gnd d ≤ n }
          → GroundCast (A ⇒ C)
  _`⨟_{A}{B}{C} c d {zero}{m} = ⊥-elim (plus-gnd-pos {A ⇒ B}{B ⇒ C}{c}{d} m)
  
  {- Rule #1 id ⨟ id = id -}
  (cid{A}{a} `⨟ cid) {suc n} = cid{A}{a}
  
  {- Rule #2   (s → t) ⨟ (s' → t') = (s'⨟s) → (t⨟t') -}
  ((s ↣ t) `⨟ (s' ↣ t')) {suc n} {s≤s m} = ((s' ⨟ s) {n}{m1}) ↣ ((t ⨟ t') {n}{m2})
     where m1 = inequality-1{size-cast s} m
           m2 = inequality-2{size-cast s} m
           
  {- Equivalent of #2 for pairs -}
  ((c ×' d) `⨟ (c₁ ×' d₁)) {suc n} {s≤s m} = ((c ⨟ c₁) {n}{m1}) ×' ((d ⨟ d₁) {n}{m2})
    where m1 = inequality-3{size-cast c} m
          m2 = inequality-2{size-cast c} m
          
  {- Equivalent of #2 for sums -}
  ((c +' d) `⨟ (c₁ +' d₁)) {suc n}{s≤s m} = ((c ⨟ c₁) {n}{m1}) +' ((d ⨟ d₁) {n}{m2})
    where m1 = inequality-3{size-cast c} m
          m2 = inequality-2{size-cast c} m
          
  {- Vacuous cases -}
  (cid {.(_ ⇒ _)} {()} `⨟ (c ↣ d)) {suc n}
  (cid {.(_ `× _)} {()} `⨟ (c ×' d)) {suc n}
  (cid {.(_ `⊎ _)} {()} `⨟ (c +' d)) {suc n}
  ((c ↣ d) `⨟ cid {.(_ ⇒ _)} {()}) {suc n}
  ((c ×' d) `⨟ cid {.(_ `× _)} {()}) {suc n}
  ((c +' d) `⨟ cid {.(_ `⊎ _)} {()}) {suc n}


  gnd-src-nd : ∀{A B} → (g : GroundCast (A ⇒ B)) → A ≢ ⋆
  gnd-src-nd {.Nat} {.Nat} (cid {.Nat} {B-Nat}) ()
  gnd-src-nd {.𝔹} {.𝔹} (cid {.𝔹} {B-Bool}) ()
  gnd-src-nd {.(_ ⇒ _)} {.(_ ⇒ _)} (c ↣ d) ()
  gnd-src-nd {.(_ `× _)} {.(_ `× _)} (c ×' d) ()
  gnd-src-nd {.(_ `⊎ _)} {.(_ `⊎ _)} (c +' d) ()

  gnd-tgt-nd : ∀{A B} → (g : GroundCast (A ⇒ B)) → B ≢ ⋆
  gnd-tgt-nd {.⋆} {.⋆} (cid {.⋆} {()}) refl
  gnd-tgt-nd (c ↣ d) ()
  gnd-tgt-nd (c ×' d) ()
  gnd-tgt-nd (c +' d) ()

  intmd-nd : ∀{A B} → (i : IntermediateCast (A ⇒ B)) → A ≢ ⋆
  intmd-nd{A}{B} (inj G g) A≡⋆ = contradiction A≡⋆ (gnd-src-nd g)
  intmd-nd{A}{B} (gnd g) A≡⋆ = contradiction A≡⋆ (gnd-src-nd g)
  intmd-nd{A}{B} (cfail G H p {A≢⋆}) A≡⋆ = contradiction A≡⋆ A≢⋆

  {-

   Composition of an intermediate coercion with a top-level coercion,
   which results in an intermediate coercion. This includes rule #4,
   #6, #7, #8, #9, and #10 from Figure 5 of Siek, Thiemann, and Wadler
   (2015).

   -}

  _⨟'_ : ∀{A B C} → (i : IntermediateCast (A ⇒ B))
          → (t : Cast (B ⇒ C))
          → {n : ℕ} → {m : size-intmd i + size-cast t ≤ n }
          → IntermediateCast (A ⇒ C)
  _⨟'_{A}{B}{C} i t {zero} {m} =
    contradiction (m+n≡0⇒n≡0 (n≤0⇒n≡0 m)) (size-cast-pos{B ⇒ C}{t})
    
  {- Rule #4   (g ; G!) ⨟ id⋆ = (g ; G!)  -}
  ((inj G g {Gg}) ⨟' id⋆) {suc n} {m} = inj G g {Gg}
  
  {- Rule #6   g ⨟ (h ; H!) = (g ⨟ h) ; H! -}
  ((gnd g) ⨟' (intmd (inj H h {Hg}))) {suc n} {s≤s m} =
    inj H ((g `⨟ h) {n} {m'}) {Hg}
    where m' = let g' = size-gnd g in let h' = size-gnd h in
              begin
                g' + h'
                   ≤⟨ m≤m+n (g' + h') 3 ⟩
                (g' + h') + 3
                   ≤⟨ ≤-reflexive (+-assoc g' h' 3) ⟩
                g' + (h' + 3)
                   ≤⟨ ≤-reflexive (cong₂ (_+_) refl (+-comm h' 3)) ⟩
                g' + (3 + h')
                   ≤⟨ m ⟩
                n
              ∎  
  {- Rule #7   (g ; G!) ⨟ (G?p ; i) = g ⨟ i
     Rule #8   (g ; G!) ⨟ (H?p ; i) = ⊥GpH    if G ≠ H  -}
  ((inj G g {Gg}) ⨟' (proj H p i {Hg})) {suc n} {s≤s m} with gnd-eq? G H {Gg}{Hg}
  ... | inj₂ neq = cfail G H p {gnd-src-nd g}
  ... | inj₁ eq rewrite eq = ((gnd g) ⨟' (intmd i)) {n} {m'}
       where m' = let g' = size-gnd g in let i' = size-intmd i in 
              begin
                suc (g' + suc i')
                    ≤⟨ m≤m+n (suc (g' + suc i')) 1 ⟩
                suc (g' + suc i') + 1
                    ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = suc (g' + suc i')}) (refl{x = 1})) ⟩
                ((1 + g') + suc i') + 1
                    ≤⟨ ≤-reflexive (cong₂ (_+_) ((cong₂ (_+_) (+-comm 1 g')
                                            (refl{x = suc i'}))) refl) ⟩
                ((g' + 1) + suc i') + 1
                    ≤⟨ ≤-reflexive (cong₂ (_+_) (+-assoc g' 1 (suc i')) refl)⟩
                (g' + (1 + suc i')) + 1
                    ≤⟨ ≤-reflexive plus1-suc ⟩
                suc (g' + (1 + suc i'))
                    ≤⟨ m ⟩
                n
              ∎  
  {- Dispatch to ⨟ for ground types -}
  ((gnd g) ⨟' (intmd (gnd h))) {suc n} {s≤s m} = gnd ((g `⨟ h) {n} {m'})
    where m' = let g' = size-gnd g in let h' = size-gnd h in
              begin
                g' + h'
                   ≤⟨ m≤m+n (g' + h') 2 ⟩
                g' + h' + 2
                   ≤⟨ ≤-reflexive (+-assoc g' h' 2) ⟩
                g' + (h' + 2)
                   ≤⟨ ≤-reflexive (cong₂ (_+_) refl (+-comm h' 2)) ⟩
                g' + (2 + h')
                   ≤⟨ m ⟩
                n
              ∎  
  {- Rule #9    ⊥GpH ⨟ s = ⊥GpH    -}
  ((cfail G H p {A≢⋆}) ⨟' s) {suc n} {m} = (cfail G H p {A≢⋆})
  
  {- Rule #10    g ⨟ ⊥GpH = ⊥GpH -}
  ((gnd g) ⨟' (intmd (cfail G H p {neq}))) {suc n} {m} = (cfail G H p {gnd-src-nd g})
    
  {- Vacuous cases -}
  _⨟'_ (inj G i₁) (intmd i₂) {suc n} {m} = contradiction refl (intmd-nd i₂)
  _⨟'_ (gnd g) id⋆ {suc n} {m} = contradiction refl (gnd-tgt-nd g)
  _⨟'_ (gnd g) (proj G p i) {suc n} {m} = contradiction refl (gnd-tgt-nd g)

  {-

   The definition of compose first does case analysis on the fuel
   parameter n. The case for zero is vacuous thanks to the metric m.

   We then perform case analysis on parameter s, so we have three
   cases. The first case is equation #3 in the paper and the second is
   equation #5. The third case dispatches to a helper function for
   composing an intermediate coercion with a top-level coercion.

   -}

  _⨟_{A}{B}{C} s t {zero}{m} = ⊥-elim (plus-cast-pos {A ⇒ B}{B ⇒ C}{s}{t} m)

  {- Rule #3 id⋆ ⨟ t = t -}
  (id⋆ ⨟ t) {suc n}  = t

  {- Rule #5 (G? ; i) ⨟ t = G? ; (i ⨟ t) -}
  (proj G p i {Gg} ⨟ t) {suc n} {s≤s m} = proj G p (_⨟'_ i t {n}{m'}) {Gg}
    where m' =
            begin
              size-intmd i + size-cast t
                 ≤⟨ ≤-step (≤-reflexive refl ) ⟩
              suc (size-intmd i + size-cast t)
                 ≤⟨ m ⟩
              n
            ∎  
  {- Dispatch to composition on intermediate coercion -}
  ((intmd i) ⨟ t) {suc n}{m} = intmd ((i ⨟' t) {n}{≤-pred m})

  {-

  We import the definition of Value and the canonical⋆ lemma from
  the ParamCastReduction module, as they do not require modification.
 
  -}

  import ParamCastReduction
  module PC = ParamCastReduction Cast Inert Active ActiveOrInert
  open PC using (Value; V-ƛ; V-const; V-pair; V-inl; V-inr; V-cast; canonical⋆)

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B)) → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id⋆ {a} = M
  applyCast M v (intmd (gnd cid)) {a} = M
  applyCast M v (intmd (cfail G H ℓ)) {a} = blame ℓ
  applyCast M v (proj G ℓ i {g}) {a} with PCR.canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ i' , meq ⟩ ⟩ ⟩ ⟩ rewrite meq =
     M' ⟨ (c ⨟ (proj G ℓ i {g})) {size-cast c + size-cast (proj G ℓ i {g})}{≤-reflexive refl} ⟩
  applyCast M v (intmd (gnd (c ×' d))) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast M v (intmd (gnd (_+'_ {A₁}{B₁}{A₂}{B₂} c d))) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in
    let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ A₁ , l) (ƛ A₂ , r)
  {- Vacuous cases -}
  applyCast M v (intmd (gnd (c ↣ d))) {A-intmd (A-gnd ())}
  applyCast M v (intmd (inj G x)) {A-intmd ()}

  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M (proj G x x₁) {()} N
  funCast M (intmd (gnd cid)) {I-intmd (I-gnd ())} N
  funCast M (intmd (cfail G H ℓ)) {I-intmd ()} N
  funCast M (intmd (gnd (c ↣ d))) {i} N =
    (M · (N ⟨ c ⟩)) ⟨ d ⟩

  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M (proj G x x₁) {()}
  fstCast M (intmd .(gnd _)) {I-intmd (I-gnd ())}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M (proj G x x₁) {()}
  sndCast M (intmd .(gnd _)) {I-intmd (I-gnd ())}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B')))
             → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L .(intmd (gnd _)) {I-intmd (I-gnd ())} M N
  
  baseNotInert : ∀ {A B} → (c : Cast (A ⇒ B)) → Base B → ¬ Inert c
  baseNotInert .(intmd (inj _ _)) () (I-intmd I-inj)
  baseNotInert .(intmd (gnd (_ ↣ _))) () (I-intmd (I-gnd I-cfun))

  compose : ∀{A B C} → Cast (A ⇒ B) → Cast (B ⇒ C) → Cast (A ⇒ C)
  compose c d = (c ⨟ d) {size-cast c + size-cast d} {≤-reflexive refl}

  module Red = EPCR.Reduction applyCast funCast fstCast sndCast caseCast baseNotInert compose
  open Red


