{-

  This module formalizes the λS calculus (Siek, Thiemann, Wadler 2015)
  and proves type safety via progress and preservation. The calculus
  uses Henglein's coercions to represent casts, and acheive space
  efficiency.

  This module is relatively small because it reuses the definitions
  and proofs from the Efficient Parameterized Cast Calculus. This
  module just has to provide the appropriate parameters, the most
  important of which is the compose function, written ⨟.

  This module is authored by Jeremy Siek with improvements
  from Kuang-chen Lu.

-}

module EfficientGroundCoercions where

  open import Agda.Primitive using ()
  open import Data.Bool using (Bool; true; false)
  open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
  open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
  open import Data.Nat
  open import Data.Nat.Solver
  open import Data.Nat.Properties
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
      renaming (_,_ to ⟨_,_⟩)
  open import Labels
  open import Pow2
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Types hiding (_⊔_)
  open import Variables

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
  infix 5 _g⨟g_
  infix 5 _i⨟s_
  infix 5 _g⨟i_
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
    cfail : ∀{A B} (G : Type) → (H : Type) → Label → .{a : A ≢ ⋆}
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

  import ParamCastCalculusOrig
  open ParamCastCalculusOrig Cast

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

  mkcast = (λ A B ℓ {c} → coerce A B {c} ℓ)

  import GTLC2CCOrig
  open GTLC2CCOrig Cast mkcast public


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

   At the top level, an inert intermediate coercion 
   is also an inert top-level coercion.

  -}

  data Inert : ∀ {A} → Cast A → Set where
    I-intmd : ∀{A B}{i : iCast (A ⇒ B)}
          → InertiCast i
          → Inert (` i)

  InertgNotRel : ∀{A}{c : gCast A} (i1 : InertgCast c)(i2 : InertgCast c) → i1 ≡ i2
  InertgNotRel I-cfun I-cfun = refl

  InertiNotRel : ∀{A}{c : iCast A} (i1 : InertiCast c)(i2 : InertiCast c) → i1 ≡ i2
  InertiNotRel I-inj I-inj = refl
  InertiNotRel (I-gnd g1) (I-gnd g2)
      with InertgNotRel g1 g2
  ... | refl = refl
  
  InertNotRel : ∀{A}{c : Cast A} (i1 : Inert c)(i2 : Inert c) → i1 ≡ i2
  InertNotRel (I-intmd i1) (I-intmd i2)
      with InertiNotRel i1 i2
  ... | refl = refl

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
  
   A failure coercion is active.  An active ground coercion is also an
   active intermediate coercion.

   -}

  data ActiveiCast : ∀ {A} → iCast A → Set where
    A-gnd : ∀{A B}{g : gCast (A ⇒ B)}
          → ActivegCast g
          → ActiveiCast (` g)
    A-cfail : ∀{A B G H ℓ } .{nd}
          → ActiveiCast (cfail {A}{B} G H ℓ {nd})

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

  ActivegNotRel : ∀{A}{c : gCast A} (a1 : ActivegCast c) (a2 : ActivegCast c) → a1 ≡ a2
  ActivegNotRel A-cpair A-cpair = refl
  ActivegNotRel A-csum A-csum = refl
  ActivegNotRel A-idι A-idι = refl
  
  ActiveiNotRel : ∀{A}{c : iCast A} (a1 : ActiveiCast c) (a2 : ActiveiCast c) → a1 ≡ a2
  ActiveiNotRel (A-gnd g1) (A-gnd g2)
      with ActivegNotRel g1 g2
  ... | refl = refl
  ActiveiNotRel A-cfail A-cfail = refl
  
  ActiveNotRel : ∀{A}{c : Cast A} (a1 : Active c) (a2 : Active c) → a1 ≡ a2
  ActiveNotRel A-id★ A-id★ = refl
  ActiveNotRel A-proj A-proj = refl
  ActiveNotRel (A-intmd i1) (A-intmd i2)
      with ActiveiNotRel i1 i2
  ... | refl = refl

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
  ActiveOrInertiCast (cfail G H p {nd}) =
     inj₁ (A-cfail {nd = eq-unk-relevant nd})

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id★ = inj₁ A-id★
  ActiveOrInert (G ?? x ⨟ x₁) = inj₁ A-proj
  ActiveOrInert (` i) with ActiveOrInertiCast i
  ... | inj₁ a = inj₁ (A-intmd a)
  ... | inj₂ j = inj₂ (I-intmd j)

  ActiveNotInertGnd : ∀ {A} {c : gCast A} → ActivegCast c → InertgCast c → Bot
  ActiveNotInertGnd A-cpair ()
  ActiveNotInertGnd A-csum ()
  ActiveNotInertGnd A-idι ()

  ActiveNotInertiCast : ∀ {A} {c : iCast A} → ActiveiCast c → InertiCast c → Bot
  ActiveNotInertiCast (A-gnd a) (I-gnd i) = ActiveNotInertGnd a i

  ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
  ActiveNotInert (A-intmd a) (I-intmd i) = ActiveNotInertiCast a i


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

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         → Cast (A' ⇒ A₁)
  dom (` (` (c ↣ d))) x = c
  
  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  cod (` (` (s ↣ t))) x = t

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  fstC (` (` (c ×' d))) x = c
  
  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  sndC (` (` (c ×' d))) x = d

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  inlC (` (` (c +' d))) x = c
  
  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  inrC (` (` (c +' d))) x = d

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert (` .(` _)) (I-intmd (I-gnd ()))

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert A-Unk .(` (` _)) (I-intmd {i = ` ()} (I-gnd x))
  idNotInert A-Base .(` (` idι)) (I-intmd {i = ` idι} (I-gnd ()))

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j id★ = contradiction refl j
  projNotInert j (G ?? x ⨟ x₁) = ActiveNotInert A-proj
  projNotInert j (` x) (I-intmd (I-gnd ()))
  
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
             ; ActiveNotInert = ActiveNotInert
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
             ; idNotInert = idNotInert
             ; projNotInert = projNotInert
             ; InertNotRel = InertNotRel
             ; ActiveNotRel = ActiveNotRel
             }

  import EfficientParamCastAux
  open EfficientParamCastAux pcs

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
  intmd-nd{A}{B} (cfail G H p {A≢⋆}) A≡⋆ = eq-unk-relevant A≢⋆ A≡⋆

  {- 

    We define the composition operation from Figure 5 of Siek,
    Thiemann, and Wadler (2015). We break down the operation into
    a family of four functions in Agda, which enables us to capture
    more invariants about the type of the resulting coercion,
    which is necessary to pass the Agda type checker.
    First, observe that in equation #6, we compose two ground
    coercions (g ⨟ h) and the result must be a ground coercion.
    Second, in equation #5 we compose an intermediate coercion
    with a top-level coercion (i ⨟ t) and the result must
    be an intermediate coercion. Finally, we note that
    rules #6 and #10 compose a ground coercion with an intermediate
    coercion, producing and intermediate coercion.
    Thus, we shall define composition with four functions in Agda,
    * (s ⨟ t) composition of top-level coercions
    * (i i⨟s t) composition of an intermediate coercion with a top coercion
    * (g g⨟i i) composition of ground and intermediate coercion
    * (g g⨟g h) composition of two ground coercions

    Each of the equations from Figure 5 are placed in one of these
    three functions according to which kinds of coercions they refer to.

   -}

  _⨟_ : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
          → Cast (A ⇒ C)
  _i⨟s_ : ∀{A B C} → (i : iCast (A ⇒ B)) → (t : Cast (B ⇒ C))
          → iCast (A ⇒ C)
  _g⨟i_ : ∀{A B C} → (g : gCast (A ⇒ B)) → (i : iCast (B ⇒ C))
          → iCast (A ⇒ C)
  _g⨟g_ : ∀{A B C} → (c : gCast (A ⇒ B)) → (d : gCast (B ⇒ C))
          → gCast (A ⇒ C)

  {- 

   For top-level composition, qe perform case analysis on parameter s,
   so we have three cases. The first case is equation #3 in the paper
   and the second is equation #5. The third case dispatches to a
   helper function for composing an intermediate coercion with a
   top-level coercion.

   -}

  {- Rule #3 id★ ⨟ t = t -}
  id★ ⨟ t = t
  {- Rule #5 (G? ; i) ⨟ t = G? ; (i ⨟ t) -}
  ((G ?? p ⨟ i) {gg} ⨟ t) = (G ?? p ⨟ (i i⨟s t)) {gg}
  {- Dispatch to i⨟s -}
  (` i ⨟ t) = ` (i i⨟s t)
  
  {- 
    The following is composition for ground coercions, which covers
    rules #1 and #2 from Figure 5 of Siek, Thiemann, and Wadler (2015).
   -}
  
  {- Rule #1 -}
  (idι{A} g⨟g idι) = idι{A}
  {- Rule #2 -}
  (s ↣ t g⨟g s' ↣ t') = (s' ⨟ s) ↣ (t ⨟ t')
  {- Equivalent of #2 for pairs -}
  (s ×' t g⨟g s' ×' t') = (s ⨟ s') ×' (t ⨟ t')
  {- Equivalent of #2 for sums -}
  (s +' t g⨟g s' +' t') = (s ⨟ s') +' (t ⨟ t')

  {-
   Composition of an intermediate coercion with a top-level coercion
   results in an intermediate coercion. This includes rule #4, #7,
   #8, and #9 from Figure 5 of Siek, Thiemann, and Wadler (2015).
   -}
    
  {- Rule #4   (g ; G!) ⨟ id★ = (g ; G!)  -}
  ((g ⨟!) {gg} i⨟s id★) = (g ⨟!) {gg}
  {- Rule #7   (g ; G!) ⨟ (G?p ; i) = g ⨟ i
     Rule #8   (g ; G!) ⨟ (H?p ; i) = ⊥GpH    if G ≠ H  -}
  (_⨟! {G = G} g {gg} i⨟s (H ?? p ⨟ i) {hg})
        with gnd-eq? G H {gg}{hg}
  ... | no neq = cfail G H p {gnd-src-nd g}
  ... | yes eq rewrite eq = g g⨟i i
  {- Rule #9    ⊥GpH ⨟ s = ⊥GpH    -}
  (cfail G H p {A≢⋆} i⨟s s) = cfail G H p {A≢⋆}
  {- Dispatch to g⨟i -}
  (` g i⨟s ` i) = g g⨟i i
  {- Vacuous case -}
  ((i₁ ⨟!) i⨟s ` i₂) = contradiction refl (intmd-nd i₂)

  {-
   Composition of a ground coercion with an intermediate coercion.
   This includes rules #6 and #10.
   -}

  {- Rule #6 -}
  g g⨟i ((h ⨟!) {g = gG})  = ((g g⨟g h) ⨟!) {g = gG}
  {- Rule #10 -}
  g g⨟i (cfail G H p {a})  = (cfail G H p {gnd-src-nd g})
  {- Dispatch to g⨟g -}
  g g⨟i ` h                = ` (g g⨟g h) 


  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (SimpleValue M) → (c : Cast (A ⇒ B))
            → ∀ {a : PreCastStruct.Active pcs c} → Γ ⊢ B
  applyCast M v id★ {a} = M
  applyCast M v (` (` idι)) {a} = M
  applyCast M v (` (cfail G H ℓ)) {a} = blame ℓ
  applyCast M v ((G ?? ℓ ⨟ i) {g}) {a} with simple⋆ M v refl
  ... | ()
  applyCast {Γ} {A₁ `× A₂} {B₁ `× B₂} (cons V W) vV (` (` (c ×' d))) =
      cons (V ⟨ c ⟩) (W ⟨ d ⟩)  
  applyCast {A = A₁ `⊎ A₂} (inl V) (V-inl vW) (` (` (c +' d))) = inl (V ⟨ c ⟩)
  applyCast {A = A₁ `⊎ A₂} (inr V) (V-inr vV) (` (` (c +' d))) = inr (V ⟨ d ⟩)
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

  height-i : ∀{A B} → iCast (A ⇒ B) → ℕ
  height-g : ∀{A B} → gCast (A ⇒ B) → ℕ
  
  height-s : ∀{A B} → Cast (A ⇒ B) → ℕ
  height-s id★ = 0
  height-s (G ?? p ⨟ i) = height-i i
  height-s (` i) = height-i i

  height-i (g ⨟!) = height-g g
  height-i (` g) = height-g g
  height-i (cfail G H p) = 0

  height-g idι = 0
  height-g (c ↣ d) = suc ((height-s c) ⊔ (height-s d))
  height-g (c ×' d) = suc ((height-s c) ⊔ (height-s d))
  height-g (c +' d) = suc ((height-s c) ⊔ (height-s d))

  compose-height-s : ∀ {A B C} → (s : Cast (A ⇒ B)) (t : Cast (B ⇒ C))
     → height-s (s ⨟ t) ≤ (height-s s) ⊔ (height-s t)

  applyCastOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}{a}
          → n ∣ false ⊢ M ok → (v : SimpleValue M)
          → Σ[ m ∈ ℕ ] m ∣ false ⊢ applyCast M v c {a} ok × m ≤ 2 + n
  applyCastOK {M = M} {id★} {n} {a} Mok v =
      ⟨ n , ⟨ Mok , (≤-step (≤-step ≤-refl)) ⟩ ⟩
  applyCastOK {M = M} {G ?? ℓ ⨟ i} {n} {a} Mok v = ⊥-elim (simple⋆ M v refl)
  applyCastOK {M = M} {` (g ⨟!)} {n} {A-intmd ()} Mok v
  applyCastOK {M = M} {` (` idι)} {n} {a} Mok v =
      ⟨ n , ⟨ Mok , (≤-step (≤-step ≤-refl)) ⟩ ⟩
  applyCastOK {M = M} {` (` (c ↣ d))} {n} {A-intmd (A-gnd ())} Mok v
  applyCastOK {M = cons V W} {` (` (c ×' d))} {.0} {a} (consOK Vok Wok)
      (V-pair vV vW) =
         let n≤1 = value→ok1 vV Vok in
         let m≤1 = value→ok1 vW Wok in
         ⟨ zero ,
         ⟨ consOK (castOK Vok (≤-trans n≤1 (s≤s z≤n)))
                  (castOK Wok (≤-trans m≤1 (s≤s z≤n))) ,
           z≤n ⟩ ⟩
  applyCastOK {M = inl M} {` (` (c +' d))} {.0} {a} (inlOK Mok) (V-inl x) =
         let n≤1 = value→ok1 x Mok in
         ⟨ zero ,
         ⟨ (inlOK (castOK Mok (≤-trans n≤1 (s≤s z≤n)))) ,
           z≤n ⟩ ⟩
  applyCastOK {M = inr M} {` (` (c +' d))} {.0} {a} (inrOK Mok) (V-inr x) =
         let n≤1 = value→ok1 x Mok in
         ⟨ zero ,
         ⟨ (inrOK (castOK Mok (≤-trans n≤1 (s≤s z≤n)))) ,
           z≤n ⟩ ⟩
  applyCastOK {M = M} {` cfail G H x} {n} {a} Mok v =
      ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩

  open import CastStructure

  ecs : EfficientCastStruct
  ecs = record
             { precast = pcs
             ; applyCast = applyCast
             ; compose = _⨟_
             ; height = height-s
             ; compose-height = compose-height-s
             ; applyCastOK = (λ {Γ}{A}{B}{M}{c}{n}{a} →
                               applyCastOK{Γ}{A}{B}{M}{c}{n}{a})
             }
  
  import EfficientParamCasts
  open EfficientParamCasts ecs public

  c-height = EfficientCastStruct.c-height ecs
  height = EfficientCastStruct.height ecs  

  applyCast-height : ∀{Γ}{A B}{V}{v : SimpleValue {Γ} V}{c : Cast (A ⇒ B)}
        {a : Active c}
      → c-height (applyCast V v c {a}) ≤ c-height V ⊔ height c
  applyCast-height {v = v} {id★} {a} = m≤m⊔n _ _
  applyCast-height {V = V}{v} {(G ?? ℓ ⨟ i)} = ⊥-elim (simple⋆ V v refl)
  applyCast-height {v = v} {` (g ⨟!)} {A-intmd ()}
  applyCast-height {v = v} {` (` idι)} {a} = m≤m⊔n _ _
  applyCast-height {v = v} {` (` (c ↣ d))} {A-intmd (A-gnd ())}
  applyCast-height {V = cons V W} {V-pair vV vW} {` (` (c ×' d))} {a} =
    begin
        (c-height V ⊔ height c) ⊔ (c-height W ⊔ height d)
      ≤⟨ ≤-reflexive (⊔-assoc (c-height V) _ _) ⟩
        c-height V ⊔ (height c ⊔ (c-height W ⊔ height d))
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-reflexive (sym (⊔-assoc (height c) _ _))) ⟩
        c-height V ⊔ ((height c ⊔ c-height W) ⊔ height d)
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoˡ-≤ (height d) (≤-reflexive (⊔-comm (height c) _))) ⟩
        c-height V ⊔ ((c-height W ⊔ height c) ⊔ height d)
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-reflexive (⊔-assoc (c-height W) _ _)) ⟩
        c-height V ⊔ (c-height W ⊔ (height c ⊔ height d))
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height V) _ _)) ⟩
        (c-height V ⊔ c-height W) ⊔ (height c ⊔ height d)
      ≤⟨ ⊔-monoʳ-≤ (c-height V ⊔ c-height W) (≤-step ≤-refl) ⟩ 
        (c-height V ⊔ c-height W) ⊔ suc (height c ⊔ height d)
    ∎ 
    where open ≤-Reasoning
  applyCast-height {V = inl V} {V-inl vV} {` (` (c +' d))} {a} =
    begin
      c-height V ⊔ height c
    ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-step (m≤m⊔n _ _)) ⟩
      c-height V ⊔ suc (height c ⊔ height d)
    ∎ 
    where open ≤-Reasoning
  applyCast-height {V = inr V} {V-inr vV} {` (` (c +' d))} {a} =
    begin
      c-height V ⊔ height d
    ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-step (m≤n⊔m _ _)) ⟩
      c-height V ⊔ suc (height c ⊔ height d)
    ∎ 
    where open ≤-Reasoning
  applyCast-height {v = v} {` cfail G H x} {a} = z≤n
  
  dom-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}.{x : Cross c}
       → height (dom c x) ≤ height c
  dom-height {c = ` (` (c ↣ d))} {x} = ≤-step (m≤m⊔n _ _)
  
  cod-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}.{x : Cross c}
       → height (cod c x) ≤ height c
  cod-height {c = ` (` (c ↣ d))} {x} = ≤-step (m≤n⊔m _ _)
  
  fst-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}.{x : Cross c}
       → height (fstC c x) ≤ height c
  fst-height {c = ` (` (c ×' d))}{x} = ≤-step (m≤m⊔n _ _)
  
  snd-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}.{x : Cross c}
       → height (sndC c x) ≤ height c
  snd-height {c = ` (` (c ×' d))}{x} = ≤-step (m≤n⊔m _ _)
  
  inlC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}.{x : Cross c}
       → height (inlC c x) ≤ height c
  inlC-height {c = ` (` (c +' d))}{x} = ≤-step (m≤m⊔n _ _)
  
  inrC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}.{x : Cross c}
       → height (inrC c x) ≤ height c
  inrC-height {c = ` (` (c +' d))}{x} = ≤-step (m≤n⊔m _ _)

  isize : ∀{A B} (c : iCast (A ⇒ B)) → ℕ
  gsize : ∀{A B} (c : gCast (A ⇒ B)) → ℕ
  
  csize : ∀{A B} (c : Cast (A ⇒ B)) → ℕ
  csize id★ = 0
  csize (G ?? ℓ ⨟ i) = 2 + isize i
  csize (` i) = isize i
  isize (g ⨟!) = 2 + gsize g
  isize (` g) = gsize g
  isize (cfail G H ℓ) = 0
  gsize idι = 0
  gsize (c ↣ d) = 1 + csize c + csize d
  gsize (c ×' d) = 1 + csize c + csize d
  gsize (c +' d) = 1 + csize c + csize d

  isize-height : ∀{A B} (c : iCast (A ⇒ B)) → 7 + isize c ≤ 9 * pow2 (height-i c)
  gsize-height : ∀{A B} (c : gCast (A ⇒ B)) → 9 + gsize c ≤ 9 * pow2 (height-g c)
  
  csize-height : ∀{A B} (c : Cast (A ⇒ B)) → 5 + csize c ≤ 9 * pow2 (height c)
  csize-height id★ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) 
  csize-height (G ?? ℓ ⨟ i) = isize-height i
  csize-height (` i) =
      let IH = isize-height i in
      ≤-trans (≤-step (≤-step ≤-refl)) IH
  isize-height (g ⨟!) = gsize-height g 
  isize-height (` g) =
      let IH = gsize-height g in
      ≤-trans (≤-step (≤-step ≤-refl)) IH
  isize-height (cfail G H ℓ) = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
  gsize-height idι = ≤-refl
  gsize-height (c ↣ d) =
    let IH1 = csize-height c in
    let IH2 = csize-height d in
    begin
        (10 + csize c) + csize d
      ≤⟨ ≤-reflexive (solve 2 (λ x y → ((con 10 :+ x) :+ y) := (con 5 :+ x) :+ (con 5 :+ y)) refl (csize c) (csize d))  ⟩
        (5 + csize c) + (5 + csize d)
      ≤⟨ +-mono-≤ IH1 IH2 ⟩
        9 * pow2 (height c) + 9 * pow2 (height d)
      ≤⟨ +-mono-≤ (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤m⊔n (height c) (height d))))
                  (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤n⊔m (height c) (height d)))) ⟩
        9 * pow2 (height c ⊔ height d) + 9 * pow2 (height c ⊔ height d)
      ≤⟨ ≤-reflexive (solve 1 (λ x → con 9 :* x :+ con 9 :* x := con 9 :* (con 2 :* x)) refl (pow2 (height c ⊔ height d)) ) ⟩
        9 * (2 * pow2 (height c ⊔ height d))
      ≤⟨ ≤-reflexive refl ⟩
        9 * pow2 (suc ((height c) ⊔ (height d)))
    ∎
    where
    open ≤-Reasoning
    open +-*-Solver
  gsize-height (c ×' d) =
    let IH1 = csize-height c in
    let IH2 = csize-height d in
    begin
        (10 + csize c) + csize d
      ≤⟨ ≤-reflexive (solve 2 (λ x y → ((con 10 :+ x) :+ y) := (con 5 :+ x) :+ (con 5 :+ y)) refl (csize c) (csize d))  ⟩
        (5 + csize c) + (5 + csize d)
      ≤⟨ +-mono-≤ IH1 IH2 ⟩
        9 * pow2 (height c) + 9 * pow2 (height d)
      ≤⟨ +-mono-≤ (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤m⊔n (height c) (height d))))
                  (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤n⊔m (height c) (height d)))) ⟩
        9 * pow2 (height c ⊔ height d) + 9 * pow2 (height c ⊔ height d)
      ≤⟨ ≤-reflexive (solve 1 (λ x → con 9 :* x :+ con 9 :* x := con 9 :* (con 2 :* x)) refl (pow2 (height c ⊔ height d)) ) ⟩
        9 * (2 * pow2 (height c ⊔ height d))
      ≤⟨ ≤-reflexive refl ⟩
        9 * pow2 (suc ((height c) ⊔ (height d)))
    ∎
    where
    open ≤-Reasoning
    open +-*-Solver
  gsize-height (c +' d) =
    let IH1 = csize-height c in
    let IH2 = csize-height d in
    begin
        (10 + csize c) + csize d
      ≤⟨ ≤-reflexive (solve 2 (λ x y → ((con 10 :+ x) :+ y) := (con 5 :+ x) :+ (con 5 :+ y)) refl (csize c) (csize d))  ⟩
        (5 + csize c) + (5 + csize d)
      ≤⟨ +-mono-≤ IH1 IH2 ⟩
        9 * pow2 (height c) + 9 * pow2 (height d)
      ≤⟨ +-mono-≤ (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤m⊔n (height c) (height d))))
                  (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤n⊔m (height c) (height d)))) ⟩
        9 * pow2 (height c ⊔ height d) + 9 * pow2 (height c ⊔ height d)
      ≤⟨ ≤-reflexive (solve 1 (λ x → con 9 :* x :+ con 9 :* x := con 9 :* (con 2 :* x)) refl (pow2 (height c ⊔ height d)) ) ⟩
        9 * (2 * pow2 (height c ⊔ height d))
      ≤⟨ ≤-reflexive refl ⟩
        9 * pow2 (suc ((height c) ⊔ (height d)))
    ∎
    where
    open ≤-Reasoning
    open +-*-Solver

  ecsh : EfficientCastStructHeight
  ecsh = record
              { effcast = ecs
              ; applyCast-height = (λ {Γ}{A}{B}{V}{v}{c}{a} → applyCast-height{Γ}{A}{B}{V}{v}{c}{a})
              ; dom-height = (λ {A}{B}{C}{D}{c}{x} → dom-height{A}{B}{C}{D}{c}{x})
              ; cod-height = (λ {A}{B}{C}{D}{c}{x} → cod-height{A}{B}{C}{D}{c}{x})
              ; fst-height = (λ {A}{B}{C}{D}{c}{x} → fst-height{A}{B}{C}{D}{c}{x})
              ; snd-height = (λ {A}{B}{C}{D}{c}{x} → snd-height{A}{B}{C}{D}{c}{x})
              ; inlC-height = (λ {A}{B}{C}{D}{c}{x} → inlC-height{A}{B}{C}{D}{c}{x})
              ; inrC-height = (λ {A}{B}{C}{D}{c}{x} → inrC-height{A}{B}{C}{D}{c}{x})
              ; size = csize
              ; size-height = ⟨ 5 , ⟨ 9 , ⟨ s≤s z≤n , (λ {A}{B} c → csize-height c) ⟩ ⟩ ⟩
              }

  assoc-iss : ∀{A B C D} (i₁ : iCast (A ⇒ B)) → (s₂ : Cast (B ⇒ C))
        → (s₃ : Cast (C ⇒ D))
        → (i₁ i⨟s s₂) i⨟s s₃ ≡ i₁ i⨟s (s₂ ⨟ s₃)

  assoc-gis : ∀{A B C D} (g₁ : gCast (A ⇒ B)) → (i₂ : iCast (B ⇒ C))
        → (s₃ : Cast (C ⇒ D))
        → (g₁ g⨟i i₂) i⨟s s₃ ≡ g₁ g⨟i (i₂ i⨟s s₃)

  assoc-ggi : ∀{A B C D} (g₁ : gCast (A ⇒ B)) → (g₂ : gCast (B ⇒ C))
        → (i₃ : iCast (C ⇒ D))
        → (g₁ g⨟g g₂) g⨟i i₃ ≡ g₁ g⨟i (g₂ g⨟i i₃)

  assoc-ggg : ∀{A B C D} (g₁ : gCast (A ⇒ B)) → (g₂ : gCast (B ⇒ C))
        → (g₃ : gCast (C ⇒ D))
        → (g₁ g⨟g g₂) g⨟g g₃ ≡ g₁ g⨟g (g₂ g⨟g g₃)

  assoc : ∀{A B C D} (s₁ : Cast (A ⇒ B)) → (s₂ : Cast (B ⇒ C))
        → (s₃ : Cast (C ⇒ D))
        → (s₁ ⨟ s₂) ⨟ s₃ ≡ s₁ ⨟ (s₂ ⨟ s₃)
  assoc id★ s₂ s₃ = refl
  assoc (G ?? p ⨟ i₁) s₂ s₃ = cong (λ c → G ?? p ⨟ c) (assoc-iss i₁ s₂ s₃)
  assoc (` i₁) s₂ s₃ = cong `_ (assoc-iss i₁ s₂ s₃)

  assoc-iss (g ⨟!) id★ s₃ = refl
  assoc-iss (_⨟! {G = G} g₁ {gg}) ((H ?? p ⨟ i₂){hg}) s₃
      with gnd-eq? G H {gg}{hg}
  ... | yes refl = assoc-gis g₁ i₂ s₃
  ... | no neq = refl
  assoc-iss (g₁ ⨟!) (` i₂) s₃ = contradiction refl (intmd-nd i₂)
  assoc-iss (` g₁) (` i₂) s₃ = assoc-gis g₁ i₂ s₃
  assoc-iss (cfail G H p) s₂ s₃ = refl

  assoc-gis g₁ (g₂ ⨟!) id★ = refl
  assoc-gis g₁ ((_⨟!{G = G} g₂){gg}) ((H ?? p ⨟ i₃){hg})
      with gnd-eq? G H {gg}{hg}
  ... | yes refl = assoc-ggi g₁ g₂ i₃
  ... | no neq = refl
  assoc-gis g₁ (g₂ ⨟!) (` i₃) = contradiction refl (intmd-nd i₃)
  assoc-gis g₁ (` g₂) (` i₃) = assoc-ggi g₁ g₂ i₃
  assoc-gis g₁ (cfail G H x) s₃ = refl

  assoc-ggi g₁ g₂ (g₃ ⨟!) = cong (λ g → g ⨟!) (assoc-ggg g₁ g₂ g₃)
  assoc-ggi g₁ g₂ (` g₃) = cong `_ (assoc-ggg g₁ g₂ g₃)
  assoc-ggi g₁ g₂ (cfail G H p) = refl

  assoc-ggg idι idι idι = refl
  assoc-ggg (c ↣ d) (c₁ ↣ d₁) (c₂ ↣ d₂) =
     cong₂ _↣_ (sym (assoc c₂ c₁ c)) (assoc d d₁ d₂)
  assoc-ggg (c ×' d) (c₁ ×' d₁) (c₂ ×' d₂) =
     cong₂ _×'_ (assoc c c₁ c₂) (assoc d d₁ d₂)
  assoc-ggg (c +' d) (c₁ +' d₁) (c₂ +' d₂) =
     cong₂ _+'_ (assoc c c₁ c₂) (assoc d d₁ d₂)

  compose-height-is : ∀ {A B C} → (i : iCast (A ⇒ B)) (s : Cast (B ⇒ C))
     → height-i (i i⨟s s) ≤ (height-i i) ⊔ (height-s s)

  compose-height-gi : ∀ {A B C} → (g : gCast (A ⇒ B)) (i : iCast (B ⇒ C))
    → height-i (g g⨟i i) ≤ height-g g ⊔ height-i i

  compose-height-gg : ∀ {A B C} → (g : gCast (A ⇒ B)) (h : gCast (B ⇒ C))
    → height-g (g g⨟g h) ≤ height-g g ⊔ height-g h

  compose-height-s {.⋆} {.⋆} {C} id★ t = ≤-refl
  compose-height-s {.⋆} {B} {C} (G ?? p ⨟ i) t = compose-height-is i t
  compose-height-s {A} {B} {C} (` i) t = compose-height-is i t

  compose-height-is (g ⨟!) id★ = ≤-reflexive (sym (⊔-identityʳ (height-g g)))
  compose-height-is (_⨟! {G = G} g {gg}) ((H ?? p ⨟ i){hg})
      with gnd-eq? G H {gg}{hg}
  ... | yes refl = compose-height-gi g i
  ... | no neq = z≤n
  compose-height-is (g ⨟!) (` i) = contradiction refl (intmd-nd i)
  compose-height-is (` g) (` i) = compose-height-gi g i
  compose-height-is (cfail G H p) s = z≤n

  compose-height-gi g (h ⨟!) = compose-height-gg g h
  compose-height-gi g (` h) = compose-height-gg g h
  compose-height-gi g (cfail G H p) = z≤n

  compose-height-gg idι idι = z≤n
  compose-height-gg (c ↣ d) (c₁ ↣ d₁) =
    let x = compose-height-s c₁ c in
    let y = compose-height-s d d₁ in
     s≤s (≤-trans (⊔-mono-≤ x y) (≤-reflexive
       (begin
       height-s c₁ ⊔ height-s c ⊔ (height-s d ⊔ height-s d₁)
       ≡⟨ (⊔-assoc (height-s c₁) _ _) ⟩
       height-s c₁ ⊔ (height-s c ⊔ (height-s d ⊔ height-s d₁))
       ≡⟨ cong (λ c → height-s c₁ ⊔ c) (sym (⊔-assoc (height-s c)_ _)) ⟩
       height-s c₁ ⊔ (height-s c ⊔ height-s d ⊔ height-s d₁)
       ≡⟨ sym (⊔-assoc (height-s c₁) ((height-s c) ⊔ (height-s d)) (height-s d₁)) ⟩ 
       (height-s c₁ ⊔ (height-s c ⊔ height-s d)) ⊔ height-s d₁
       ≡⟨ (cong₂ _⊔_ (⊔-comm (height-s c₁) (height-s c ⊔ height-s d)) refl) ⟩
       ((height-s c ⊔ height-s d) ⊔ height-s c₁) ⊔ height-s d₁
       ≡⟨ ⊔-assoc (height-s c ⊔ height-s d) (height-s c₁) (height-s d₁) ⟩
       height-s c ⊔ height-s d ⊔ (height-s c₁ ⊔ height-s d₁)
       ∎)))
     where open Eq.≡-Reasoning
  compose-height-gg (c ×' d) (c₁ ×' d₁) =
    let x = compose-height-s c c₁ in
    let y = compose-height-s d d₁ in
      s≤s (≤-trans (⊔-mono-≤ x y) (≤-reflexive
      (begin
      height-s c ⊔ height-s c₁ ⊔ (height-s d ⊔ height-s d₁)
      ≡⟨ ⊔-assoc (height-s c) (height-s c₁) (height-s d ⊔ height-s d₁) ⟩
      height-s c ⊔ (height-s c₁ ⊔ (height-s d ⊔ height-s d₁))
      ≡⟨ cong (λ d → height-s c ⊔ d) (sym (⊔-assoc (height-s c₁) _ _)) ⟩
      height-s c ⊔ ((height-s c₁ ⊔ height-s d) ⊔ height-s d₁)
      ≡⟨ cong (λ e → height-s c ⊔ (e ⊔ height-s d₁)) (⊔-comm (height-s c₁) _) ⟩
      height-s c ⊔ ((height-s d ⊔ height-s c₁) ⊔ height-s d₁)
      ≡⟨ cong (λ e → height-s c ⊔ e) (⊔-assoc (height-s d) _ _) ⟩
      height-s c ⊔ (height-s d ⊔ (height-s c₁ ⊔ height-s d₁))
      ≡⟨ sym (⊔-assoc (height-s c) _ _) ⟩
      (height-s c ⊔ height-s d) ⊔ (height-s c₁ ⊔ height-s d₁)
      ∎)))
     where open Eq.≡-Reasoning
  compose-height-gg (c +' d) (c₁ +' d₁) =
    let x = compose-height-s c c₁ in
    let y = compose-height-s d d₁ in
      s≤s (≤-trans (⊔-mono-≤ x y) (≤-reflexive 
      (begin
      height-s c ⊔ height-s c₁ ⊔ (height-s d ⊔ height-s d₁)
      ≡⟨ ⊔-assoc (height-s c) (height-s c₁) (height-s d ⊔ height-s d₁) ⟩
      height-s c ⊔ (height-s c₁ ⊔ (height-s d ⊔ height-s d₁))
      ≡⟨ cong (λ d → height-s c ⊔ d) (sym (⊔-assoc (height-s c₁) _ _)) ⟩
      height-s c ⊔ ((height-s c₁ ⊔ height-s d) ⊔ height-s d₁)
      ≡⟨ cong (λ e → height-s c ⊔ (e ⊔ height-s d₁)) (⊔-comm (height-s c₁) _) ⟩
      height-s c ⊔ ((height-s d ⊔ height-s c₁) ⊔ height-s d₁)
      ≡⟨ cong (λ e → height-s c ⊔ e) (⊔-assoc (height-s d) _ _) ⟩
      height-s c ⊔ (height-s d ⊔ (height-s c₁ ⊔ height-s d₁))
      ≡⟨ sym (⊔-assoc (height-s c) _ _) ⟩
      (height-s c ⊔ height-s d) ⊔ (height-s c₁ ⊔ height-s d₁)
      ∎)))
    where open Eq.≡-Reasoning


  import PreserveHeight
  module PH = PreserveHeight ecsh

  preserve-height : ∀ {Γ A} {M M′ : Γ ⊢ A} {ctx : ReductionCtx}
       → ctx / M —→ M′ → c-height M′ ≤ c-height M
  preserve-height M—→M′ = PH.preserve-height M—→M′


  import SpaceEfficient
  module SE = SpaceEfficient ecs

  preserve-ok : ∀{Γ A}{M M′ : Γ ⊢ A}{ctx : ReductionCtx}{n}
          → n ∣ false ⊢ M ok  →  ctx / M —→ M′
          → Σ[ m ∈ ℕ ] m ∣ false ⊢ M′ ok × m ≤ 2 + n
  preserve-ok Mok M—→M′ = SE.preserve-ok Mok M—→M′

  module EC = SE.EfficientCompile mkcast

  open import GTLC

  compile-efficient : ∀{Γ A} (M : Term) (d : Γ ⊢G M ⦂ A) (ul : Bool)
      → Σ[ k ∈ ℕ ] k ∣ ul ⊢ (compile M d) ok × k ≤ 1
  compile-efficient d ul = EC.compile-efficient d ul
