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
  open ≤-Reasoning
     {- renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_) -}
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
      renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  
  data iCast : Type → Set
  data gCast : Type → Set
  data Cast : Type → Set

  {-

   The following Cast data type (together with the data types
   iCast and gCast) define a normal form for
   coercions, following the grammar in Figure 5 of Siek, Thiemann, and
   Wadler (2015).

  -}

  infix 7 _↣_
  infix  10 `_
  infix 5 _⨟!
  infix 5 _??_⨟_
  infix 5 _`⨟_
  infix 5 _⨟'_
  infix 5 _⨟_

  data Cast where
    id★ : Cast (⋆ ⇒ ⋆)
    _??_⨟_ : ∀{B}
       → (G : Type) → Label → iCast (G ⇒ B) → {g : Ground G}
         ----------------------------------
       → Cast (⋆ ⇒ B)
    `_ : ∀{A B}
       → iCast (A ⇒ B)
       → Cast (A ⇒ B)

  data iCast where
    _⨟! : ∀{A} {G : Type}
       → gCast (A ⇒ G)
       → {g : Ground G}
         ------------------------
       → iCast (A ⇒ ⋆)
    `_ : ∀{A B}
       → (g : gCast (A ⇒ B))
       → iCast (A ⇒ B)
    cfail : ∀{A B} (G : Type) → (H : Type) → Label → {a : A ≢ ⋆}
       → iCast (A ⇒ B)

  data gCast where
    idι : ∀ {ι : Base} → gCast ((` ι) ⇒ (` ι))
    _↣_ : ∀ {A B A' B'}
      → (c : Cast (B ⇒ A)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → gCast ((A ⇒ A') ⇒ (B ⇒ B'))
    _×'_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → gCast ((A `× A') ⇒ (B `× B'))
    _+'_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → gCast ((A `⊎ A') ⇒ (B `⊎ B'))

  {-

   We instantiate the ParamCastCalculus module to obtain the syntax
   and type system of the cast calculus and the definition of
   substitution.

  -}

  import ParamCastCalculus
  open ParamCastCalculus Cast

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
     → ∀ {c : A ~ B}{a : A ≢ ⋆} → Label → gCast (A ⇒ B)
  coerce-from-gnd : (A : Type) → (B : Type) → {g : Ground A}
     → ∀ {c : A ~ B}{b : B ≢ ⋆} → Label → gCast (A ⇒ B)

  coerce-gnd-to⋆ : (A : Type) → {g : Ground A} → Label → Cast (A ⇒ ⋆)
  coerce-gnd-to⋆ (` ι) {G-Base} ℓ =
      ` (idι{ι} ⨟!) {G-Base}
  coerce-gnd-to⋆ (⋆ ⇒ ⋆) {G-Fun} ℓ = ` (id★ ↣ id★ ⨟!) {G-Fun}
  coerce-gnd-to⋆ (⋆ `× ⋆) {G-Pair} ℓ = ` (id★ ×' id★ ⨟!) {G-Pair}
  coerce-gnd-to⋆ (⋆ `⊎ ⋆) {G-Sum} ℓ = ` (id★ +' id★ ⨟!) {G-Sum}

  coerce-gnd-from⋆ : (B : Type) → {g : Ground B} → Label → Cast (⋆ ⇒ B)
  coerce-gnd-from⋆ (` ι) {G-Base} ℓ = (` ι ?? ℓ ⨟ ` idι{ι}) {G-Base}
  coerce-gnd-from⋆ (⋆ ⇒ ⋆) {G-Fun} ℓ = (⋆ ⇒ ⋆ ?? ℓ ⨟ ` (id★ ↣ id★)) {G-Fun}
  coerce-gnd-from⋆ (⋆ `× ⋆) {G-Pair} ℓ = (⋆ `× ⋆ ?? ℓ ⨟ ` id★ ×' id★) {G-Pair}
  coerce-gnd-from⋆ (⋆ `⊎ ⋆) {G-Sum} ℓ = (⋆ `⊎ ⋆ ?? ℓ ⨟ ` id★ +' id★) {G-Sum}
  
  coerce-to⋆ : (A : Type) → Label → Cast (A ⇒ ⋆)
  coerce-to⋆ A ℓ with eq-unk A
  ... | yes eq rewrite eq = id★ 
  ... | no neq with ground? A
  ...     | yes g = coerce-gnd-to⋆ A {g} ℓ
  ...     | no ng with ground A {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ =
     ` (coerce-to-gnd A G {g}{c}{neq} ℓ ⨟!) {g}

  coerce-from⋆ : (B : Type) → Label → Cast (⋆ ⇒ B)
  coerce-from⋆ B ℓ with eq-unk B
  ... | yes eq rewrite eq = id★
  ... | no neq with ground? B
  ...     | yes g = coerce-gnd-from⋆ B {g} ℓ
  ...     | no ng with ground B {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ =
               (G ?? ℓ ⨟ ` coerce-from-gnd G B {g}{Sym~ c}{neq} ℓ) {g} 

  coerce-to-gnd .⋆ (` ι) {G-Base} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (` ι) (` ι) {G-Base} {base~} ℓ = idι{ι}
  coerce-to-gnd .⋆ .(⋆ ⇒ ⋆) {G-Fun} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ ⇒ A₂) .(⋆ ⇒ ⋆) {G-Fun} {fun~ c c₁} ℓ =
     (coerce-from⋆ A₁ ℓ) ↣ (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd .⋆ .(⋆ `× ⋆) {G-Pair} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ `× A₂) .(⋆ `× ⋆) {G-Pair} {pair~ c c₁} ℓ =
     (coerce-to⋆ A₁ ℓ) ×' (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd .⋆ .(⋆ `⊎ ⋆) {G-Sum} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ `⊎ A₂) .(⋆ `⊎ ⋆) {G-Sum} {sum~ c c₁} ℓ =
     (coerce-to⋆ A₁ ℓ) +' (coerce-to⋆ A₂ ℓ)

  coerce-from-gnd (` ι) .⋆ {G-Base} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd (` ι) (` ι) {G-Base} {base~} ℓ = idι{ι}
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
  coerce (` ι) (` ι) {base~} ℓ = ` ` idι {ι}
  coerce (A ⇒ B) (A' ⇒ B') {fun~ c c₁} ℓ =
    ` ` (coerce A' A {c} (flip ℓ) ↣ coerce B B' {c₁} ℓ)
  coerce (A `× B) (A' `× B') {pair~ c c₁} ℓ =
    ` ` coerce A A' {c} ℓ ×' coerce B B' {c₁} ℓ
  coerce (A `⊎ B) (A' `⊎ B') {sum~ c c₁} ℓ =
    ` ` coerce A A' {c} ℓ +' coerce B B' {c₁} ℓ

  {-

   We instantiate the GTLC2CC module, creating a compiler from the
   GTLC to λC.

  -}
  import GTLC2CC
  open GTLC2CC Cast (λ A B ℓ {c} → coerce A B {c} ℓ) public


  {-

   To prepare for instantiating the ParamCastReduction module, we
   categorize the coercions as either inert or active.  We do this for
   each of the three kinds of coercions: for the ground, intermediate,
   and top-level coercions. For the ground coercions, only the
   function coercion is inert.

   -}
  data InertgCast : ∀ {A} → gCast A → Set where
    I-cfun : ∀{A B A' B'}{s : Cast (B ⇒ A)} {t : Cast (A' ⇒ B')}
          → InertgCast (s ↣ t)

  {-

   The other three ground coercions are active.

  -}
  data ActivegCast : ∀ {A} → gCast A → Set where
    A-cpair : ∀{A B A' B'}{s : Cast (A ⇒ B)} {t : Cast (A' ⇒ B')}
          → ActivegCast (s ×' t)
    A-csum : ∀{A B A' B'}{s : Cast (A ⇒ B)} {t : Cast (A' ⇒ B')}
          → ActivegCast (s +' t)
    A-idι : ∀{B}
          → ActivegCast (idι {B})

  {-

   Of the intermediate coercions, injection is inert and
   so is an inert ground coercion.
   
  -}

  data InertiCast : ∀ {A} → iCast A → Set where
    I-inj : ∀{A G i}{g : gCast (A ⇒ G)}
          → InertiCast ((g ⨟!) {i})
    I-gnd : ∀{A B}{g : gCast (A ⇒ B)}
          → InertgCast g
          → InertiCast (` g)

  {-
  
   A failure coercion is active.  An active ground coercion is also an
   active intermediate coercion.

   -}

  data ActiveiCast : ∀ {A} → iCast A → Set where
    A-gnd : ∀{A B}{g : gCast (A ⇒ B)}
          → ActivegCast g
          → ActiveiCast (` g)
    A-cfail : ∀{A B G H ℓ nd}
          → ActiveiCast (cfail {A}{B} G H ℓ {nd})

  {-

   At the top level, an inert intermediate coercion 
   is also an inert top-level coercion.

  -}

  data Inert : ∀ {A} → Cast A → Set where
    I-intmd : ∀{A B}{i : iCast (A ⇒ B)}
          → InertiCast i
          → Inert (` i)

  {-

  The rest of the top-level coercions are active.  That is, the
  identity and projection coercions and the active intermediate
  coercions.

  -}
  data Active : ∀ {A} → Cast A → Set where
    A-id★ : Active id★
    A-proj : ∀{B G ℓ g} {i : iCast (G ⇒ B)}
          → Active ((G ?? ℓ ⨟ i) {g})
    A-intmd : ∀{A B}{i : iCast (A ⇒ B)}
          → ActiveiCast i
          → Active (` i)

  {-

   Regarding this categorization, we did not leave behind any
   coercions.

  -}
  
  ActiveOrInertGnd : ∀{A} → (c : gCast A) → ActivegCast c ⊎ InertgCast c
  ActiveOrInertGnd idι = inj₁ A-idι
  ActiveOrInertGnd (c ↣ d) = inj₂ I-cfun
  ActiveOrInertGnd (c ×' d) = inj₁ A-cpair
  ActiveOrInertGnd (c +' d) = inj₁ A-csum

  ActiveOrInertiCast : ∀{A} → (c : iCast A) → ActiveiCast c ⊎ InertiCast c
  ActiveOrInertiCast (g ⨟!) = inj₂ I-inj
  ActiveOrInertiCast (` g) with ActiveOrInertGnd g
  ... | inj₁ a = inj₁ (A-gnd a)
  ... | inj₂ i = inj₂ (I-gnd i)
  ActiveOrInertiCast (cfail G H x) = inj₁ A-cfail

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id★ = inj₁ A-id★
  ActiveOrInert (G ?? x ⨟ x₁) = inj₁ A-proj
  ActiveOrInert (` i) with ActiveOrInertiCast i
  ... | inj₁ a = inj₁ (A-intmd a)
  ... | inj₂ j = inj₂ (I-intmd j)


  data Cross : ∀ {A} → Cast A → Set where
    C-cross : ∀{A B}{g : gCast (A ⇒ B)} → Cross (` ` g)


  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ .(` (` (_ ↣ _))) (I-intmd (I-gnd (I-cfun{A = A}{A' = A'}))) =
     ⟨ C-cross , ⟨ A , ⟨ A' , refl ⟩ ⟩ ⟩

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× .(` (` _)) (I-intmd (I-gnd ()))

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ .(` (` _)) (I-intmd (I-gnd ()))

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
  dom (` (` (c ↣ d))) x = c
  
  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (` (` (s ↣ t))) x = t

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (` (` (c ×' d))) x = c
  
  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (` (` (c ×' d))) x = d

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (` (` (c +' d))) x = c
  
  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (` (` (c +' d))) x = d

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert (` .(` _)) (I-intmd (I-gnd ()))
  
  {-

  We instantiate the outer module of EfficientParamCasts, obtaining
  the definitions for values and frames.

  -}

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

  import EfficientParamCastAux
  open EfficientParamCastAux pcs

  {-
   The following functions compute the size of the three kinds of coercions.
   These are used in the termination argument of the compose function.
   -}

  size-gnd : ∀{A} → gCast A → ℕ
  size-intmd : ∀{A} → iCast A → ℕ  
  size-cast : ∀{A} → Cast A → ℕ  

  size-gnd idι = 1
  size-gnd (c ↣ d) = 1 + size-cast c + size-cast d
  size-gnd (c ×' d) = 1 + size-cast c + size-cast d
  size-gnd (c +' d) =  1 + size-cast c + size-cast d

  size-intmd (g ⨟!) = 2 + size-gnd g
  size-intmd (` g) = 1 + size-gnd g
  size-intmd (cfail G H ℓ) = 1
  
  size-cast id★ = 1
  size-cast (G ?? ℓ ⨟ i) = 2 + size-intmd i
  size-cast (` i) = 1 + size-intmd i

  size-gnd-pos : ∀{A c} → size-gnd {A} c ≢ 0
  size-gnd-pos {.(_ ⇒ _)} {idι} = λ ()
  size-gnd-pos {.((_ ⇒ _) ⇒ (_ ⇒ _))} {c ↣ d} = λ ()
  size-gnd-pos {.(_ `× _ ⇒ _ `× _)} {c ×' d} = λ ()
  size-gnd-pos {.(_ `⊎ _ ⇒ _ `⊎ _)} {c +' d} = λ ()

  size-intmd-pos : ∀{A c} → size-intmd {A} c ≢ 0
  size-intmd-pos {.(_ ⇒ ⋆)} {g ⨟!} = λ ()
  size-intmd-pos {.(_ ⇒ _)} {` g} = λ ()
  size-intmd-pos {.(_ ⇒ _)} {cfail G H x} = λ ()

  size-cast-pos : ∀{A c} → size-cast {A} c ≢ 0
  size-cast-pos {.(⋆ ⇒ ⋆)} {id★} = λ ()
  size-cast-pos {.(⋆ ⇒ _)} {G ?? x ⨟ x₁} = λ ()
  size-cast-pos {.(_ ⇒ _)} {` x} = λ ()

  plus-01 : ∀{a}{b} → a + b ≡ 0 → a ≡ 0
  plus-01 {0} {b} p = refl
  plus-01 {suc a} {b} ()

  plus-gnd-pos : ∀{A}{B}{c}{d} → size-gnd{A} c + size-gnd{B} d ≤ 0 → Bot
  plus-gnd-pos {A}{B}{c}{d} p =
     let cd-z = n≤0⇒n≡0 p in
     let c-z = plus-01 {size-gnd c}{size-gnd d} cd-z in
     contradiction c-z (size-gnd-pos{A}{c})

  plus-cast-pos : ∀{A}{B}{c}{d} → size-cast{A} c + size-cast{B} d ≤ 0 → Bot
  plus-cast-pos {A}{B}{c}{d} p =
     let cd-z = n≤0⇒n≡0 p in
     let c-z = plus-01 {size-cast c}{size-cast d} cd-z in
     contradiction c-z (size-cast-pos{A}{c})

  plus1-suc : ∀{n} → n + 1 ≡ suc n
  plus1-suc {0} = refl
  plus1-suc {suc n} = cong suc plus1-suc

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
  _`⨟_ : ∀{A B C} → (c : gCast (A ⇒ B)) → (d : gCast (B ⇒ C))
          → {n : ℕ} → {m : size-gnd c + size-gnd d ≤ n }
          → gCast (A ⇒ C)
  _`⨟_{A}{B}{C} c d {0}{m} = ⊥-elim (plus-gnd-pos {A ⇒ B}{B ⇒ C}{c}{d} m)
  
  {- Rule #1 id ⨟ id = id -}
  (idι{A} `⨟ idι) {suc n} = idι{A}
  
  {- Rule #2   (s → t) ⨟ (s' → t') = (s' ⨟ s) → (t ⨟ t') -}
  (s ↣ t `⨟ s' ↣ t') {suc n} {s≤s m} =
       (s' ⨟ s) {n}{m1} ↣ (t ⨟ t') {n}{m2}
     where m1 = inequality-1{size-cast s} m
           m2 = inequality-2{size-cast s} m
           
  {- Equivalent of #2 for pairs -}
  (s ×' t `⨟ s' ×' t') {suc n} {s≤s m} =
      (s ⨟ s') {n}{m1} ×' (t ⨟ t') {n}{m2}
    where m1 = inequality-3{size-cast s} m
          m2 = inequality-2{size-cast s} m
          
  {- Equivalent of #2 for sums -}
  (s +' t `⨟ s' +' t') {suc n}{s≤s m} =
      (s ⨟ s') {n}{m1} +' (t ⨟ t') {n}{m2}
    where m1 = inequality-3{size-cast s} m
          m2 = inequality-2{size-cast s} m


  gnd-src-nd : ∀{A B} → (g : gCast (A ⇒ B)) → A ≢ ⋆
  gnd-src-nd {` ι} {` ι} (idι {ι} ) ()
  gnd-src-nd {.(_ ⇒ _)} {.(_ ⇒ _)} (c ↣ d) ()
  gnd-src-nd {.(_ `× _)} {.(_ `× _)} (c ×' d) ()
  gnd-src-nd {.(_ `⊎ _)} {.(_ `⊎ _)} (c +' d) ()

  gnd-tgt-nd : ∀{A B} → (g : gCast (A ⇒ B)) → B ≢ ⋆
  gnd-tgt-nd {` ι} {` ι} idι ()
  gnd-tgt-nd (c ↣ d) ()
  gnd-tgt-nd (c ×' d) ()
  gnd-tgt-nd (c +' d) ()

  intmd-nd : ∀{A B} → (i : iCast (A ⇒ B)) → A ≢ ⋆
  intmd-nd{A}{B} (g ⨟!) A≡⋆ = contradiction A≡⋆ (gnd-src-nd g)
  intmd-nd{A}{B} (` g) A≡⋆ = contradiction A≡⋆ (gnd-src-nd g)
  intmd-nd{A}{B} (cfail G H p {A≢⋆}) A≡⋆ = contradiction A≡⋆ A≢⋆

  {-

   Composition of an intermediate coercion with a top-level coercion
   results in an intermediate coercion. This includes rule #4, #6, #7,
   #8, #9, and #10 from Figure 5 of Siek, Thiemann, and Wadler (2015).

   -}

  _⨟'_ : ∀{A B C} → (i : iCast (A ⇒ B))
          → (t : Cast (B ⇒ C))
          → {n : ℕ} → {m : size-intmd i + size-cast t ≤ n }
          → iCast (A ⇒ C)
  _⨟'_{A}{B}{C} i t {0} {m} =
    contradiction (m+n≡0⇒n≡0 (size-intmd i) (n≤0⇒n≡0 m))
                  (size-cast-pos{B ⇒ C}{t})
    
  {- Rule #4   (g ; G!) ⨟ id★ = (g ; G!)  -}
  ((g ⨟!) {gg} ⨟' id★) {suc n} {m} = (g ⨟!) {gg}
  
  {- Rule #6   g ⨟ (h ; H!) = (g ⨟ h) ; H! -}
  (` g ⨟' ` (h ⨟!) {hg}) {suc n} {s≤s m} =
    ((g `⨟ h) {n} {m'} ⨟!) {hg}
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
     Rule #8   (g ; G!) ⨟ (H?p ; i) = BotGpH    if G ≠ H  -}
  (_⨟! {G = G} g {gg} ⨟' (H ?? p ⨟ i) {hg}) {suc n} {s≤s m}
        with gnd-eq? G H {gg}{hg}
  ... | no neq = cfail G H p {gnd-src-nd g}
  ... | yes eq rewrite eq = (` g ⨟' ` i) {n} {m'}
       where m' = let g' = size-gnd g in let i' = size-intmd i in 
              begin
                suc (g' + suc i')
                    ≤⟨ m≤m+n (suc (g' + suc i')) 1 ⟩
                suc (g' + suc i') + 1
                    ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = suc (g' + suc i')})
                                                (refl{x = 1})) ⟩
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
  (` g ⨟' ` ` h) {suc n} {s≤s m} = ` (g `⨟ h) {n} {m'}
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
  {- Rule #9    BotGpH ⨟ s = BotGpH    -}
  (cfail G H p {A≢⋆} ⨟' s) {suc n} {m} = cfail G H p {A≢⋆}
  
  {- Rule #10    g ⨟ BotGpH = BotGpH -}
  (` g ⨟' ` cfail G H p {neq}) {suc n} {m} = cfail G H p {gnd-src-nd g}
    
  {- Vacuous cases -}
  ((i₁ ⨟!) ⨟' ` i₂) {suc n} {m} = contradiction refl (intmd-nd i₂)
  (` g ⨟' id★) {suc n} {m} = contradiction refl (gnd-tgt-nd g)
  (` g ⨟' (G ?? p ⨟ i)) {suc n} {m} = contradiction refl (gnd-tgt-nd g)

  {-

   The definition of compose first does case analysis on the fuel
   parameter n. The case for 0 is vacuous thanks to the metric m.

   We then perform case analysis on parameter s, so we have three
   cases. The first case is equation #3 in the paper and the second is
   equation #5. The third case dispatches to a helper function for
   composing an intermediate coercion with a top-level coercion.

   -}

  _⨟_{A}{B}{C} s t {0}{m} = ⊥-elim (plus-cast-pos {A ⇒ B}{B ⇒ C}{s}{t} m)

  {- Rule #3 id★ ⨟ t = t -}
  (id★ ⨟ t) {suc n}  = t

  {- Rule #5 (G? ; i) ⨟ t = G? ; (i ⨟ t) -}
  ((G ?? p ⨟ i) {gg} ⨟ t) {suc n} {s≤s m} = (G ?? p ⨟ (i ⨟' t) {n}{m'}) {gg}
    where m' =
            begin
              size-intmd i + size-cast t
                 ≤⟨ ≤-step (≤-reflexive refl ) ⟩
              suc (size-intmd i + size-cast t)
                 ≤⟨ m ⟩
              n
            ∎  
  {- Dispatch to composition on intermediate coercion -}
  (` i ⨟ t) {suc n}{m} = ` (i ⨟' t) {n}{≤-pred m}

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id★ {a} = M
  applyCast M v (` (` idι)) {a} = M
  applyCast M v (` (cfail G H ℓ)) {a} = blame ℓ
  applyCast M v ((G ?? ℓ ⨟ i) {g}) {a} with canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ i' , ⟨ meq , _ ⟩ ⟩ ⟩ ⟩ ⟩ rewrite meq =
     M' ⟨ (c ⨟ (G ?? ℓ ⨟ i) {g}) {sz} {≤-reflexive refl} ⟩
     where sz = size-cast c + size-cast ((G ?? ℓ ⨟ i) {g})
  applyCast M v (` ` c ×' d) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast{A = A₁ `⊎ A₂} M v (` ` c +' d) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ l) (ƛ r)
  {- Vacuous cases -}
  applyCast M v (` ` (c ↣ d)) {A-intmd (A-gnd ())}
  applyCast M v (` (g ⨟!)) {A-intmd ()}

  funCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
          → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M v (` ` (c ↣ d)) {i} N = (M · N ⟨ c ⟩) ⟨ d ⟩
  {- Vacuous cases -}
  funCast M v (G ?? x ⨟ x₁) {()} N
  funCast M v (` (cfail G H ℓ)) {I-intmd ()} N

  funSrc : ∀{A A' B' Γ}
         → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → (M : Γ ⊢ A) → SimpleValue M
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc (G ?? x ⨟ x₁) () M v
  funSrc (` .(` (_ ↣ _)))
      (I-intmd (I-gnd (I-cfun{A = A₁}{B = B₁}{A' = A'}{B' = B'}))) M v =
        ⟨ A₁ , ⟨ A' , refl ⟩ ⟩

  pairSrc : ∀{A A' B' Γ}
         → (c : Cast (A ⇒ (A' `× B'))) → (i : Inert c)
            → (M : Γ ⊢ A) → SimpleValue M
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  pairSrc .(` (` _)) (I-intmd (I-gnd ())) M vM

  sumSrc : ∀{A A' B' Γ}
         → (c : Cast (A ⇒ (A' `⊎ B'))) → (i : Inert c)
            → (M : Γ ⊢ A) → SimpleValue M
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  sumSrc .(` (` _)) (I-intmd (I-gnd ())) M vM


  compose : ∀{A B C} → Cast (A ⇒ B) → Cast (B ⇒ C) → Cast (A ⇒ C)
  compose c d = (c ⨟ d) {size-cast c + size-cast d} {≤-reflexive refl}

  open import CastStructure

  ecs : EfficientCastStruct
  ecs = record
             { precast = pcs
             ; applyCast = applyCast
             ; compose = compose
             }
             
  import EfficientParamCasts
  open EfficientParamCasts ecs public
