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
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
      renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
      using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

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
  ... | yes eq rewrite eq = id {⋆} {A-Unk}
  ... | no neq with ground? A
  ...     | yes g = inj A {g}
  ...     | no ng with ground A {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ = cseq (coerce-to-gnd A G {g} {c} ℓ) (inj G {g})

  coerce-from⋆ : (B : Type) → Label → Cast (⋆ ⇒ B)
  coerce-from⋆ B ℓ with eq-unk B
  ... | yes eq rewrite eq = id {⋆} {A-Unk}
  ... | no neq with ground? B
  ...     | yes g = proj B ℓ {g}
  ...     | no ng with ground B {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ = cseq (proj G ℓ {g}) (coerce-from-gnd G B {g} {Sym~ c} ℓ)

  coerce-to-gnd .⋆ B {gb} {unk~L} ℓ = proj B ℓ {gb}
  coerce-to-gnd A .⋆ {()} {unk~R} ℓ
  coerce-to-gnd (` ι) (` ι) {gb} {base~} ℓ = id {` ι} {A-Base}
  coerce-to-gnd (A₁ ⇒ A₂) .(⋆ ⇒ ⋆) {G-Fun} {fun~ c c₁} ℓ =
     cfun (coerce-from⋆ A₁ (flip ℓ)) (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd (A₁ `× A₂) .(⋆ `× ⋆) {G-Pair} {pair~ c c₁} ℓ =
     cpair (coerce-to⋆ A₁ ℓ) (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd (A₁ `⊎ A₂) .(⋆ `⊎ ⋆) {G-Sum} {sum~ c c₁} ℓ =
     csum (coerce-to⋆ A₁ ℓ) (coerce-to⋆ A₂ ℓ)

  coerce-from-gnd .⋆ B {()} {unk~L} ℓ
  coerce-from-gnd A .⋆ {ga} {unk~R} ℓ = inj A {ga}
  coerce-from-gnd (` ι) (` ι) {ga} {base~} ℓ = id {` ι}  {A-Base}
  coerce-from-gnd (⋆ ⇒ ⋆) (B₁ ⇒ B₂) {G-Fun} {fun~ c c₁} ℓ =
     cfun (coerce-to⋆ B₁ (flip ℓ)) (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd (⋆ `× ⋆) (B₁ `× B₂) {G-Pair} {pair~ c c₁} ℓ =
     cpair (coerce-from⋆ B₁ ℓ) (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd (⋆ `⊎ ⋆) (B₁ `⊎ B₂) {G-Sum} {sum~ c c₁} ℓ =
     csum (coerce-from⋆ B₁ ℓ) (coerce-from⋆ B₂ ℓ)

  coerce : (A : Type) → (B : Type) → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)
  coerce .⋆ B {unk~L} ℓ = coerce-from⋆ B ℓ
  coerce A .⋆ {unk~R} ℓ = coerce-to⋆ A ℓ
  coerce (` ι) (` ι) {base~} ℓ = id {` ι} {A-Base}
  coerce (A ⇒ B) (A' ⇒ B') {fun~ c d} ℓ =
    cfun (coerce A' A {c} (flip ℓ) ) (coerce B B' {d} ℓ)
  coerce (A `× B) (A' `× B') {pair~ c c₁} ℓ =
    cpair (coerce A A' {c} ℓ ) (coerce B B' {c₁} ℓ)
  coerce (A `⊎ B) (A' `⊎ B') {sum~ c c₁} ℓ =
    csum (coerce A A' {c} ℓ ) (coerce B B' {c₁} ℓ)

  {-

  We instantiate the GTLC2CC module, creating a compiler from the GTLC
  to λC.

  -}

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

  import ParamCastCalculus
  open ParamCastCalculus Cast Inert

  import GTLC2CC
  open GTLC2CC Cast Inert (λ A B ℓ {c} → coerce A B {c} ℓ) public

  {-

    Cross casts are casts between types with the same head type
    constructor.

  -}
  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B A' B' c d} → Cross (cfun {A}{B}{A'}{B'} c d)
    C-pair : ∀{A B A' B' c d} → Cross (cpair {A}{B}{A'}{B'} c d)
    C-sum : ∀{A B A' B' c d} → Cross (csum {A}{B}{A'}{B'} c d)

  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ (cfun {A = A}{A' = A'} _ _) I-fun =
      ⟨ C-fun , ⟨ A , ⟨ A' , refl ⟩ ⟩ ⟩

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× c ()

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ c ()

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

  ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
  ActiveNotInert A-proj ()
  ActiveNotInert A-pair ()
  ActiveNotInert A-sum ()
  ActiveNotInert A-id ()
  ActiveNotInert A-seq ()

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

  {-
  Finally, we show that casts to base type are not inert.
  -}

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a (inj ⋆ {()}) I-inj
  idNotInert () (cfun _ _) I-fun

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j id = contradiction refl j
  projNotInert j (proj _ _) = ActiveNotInert A-proj
  projNotInert j (cseq _ _) = ActiveNotInert A-seq

  data CastBlameSafe : ∀ {A} → Cast A → Label → Set where

    safe-id : ∀ {A} {a : Atomic A} {ℓ}
      → CastBlameSafe (id {A} {a}) ℓ

    safe-inj : ∀ {A} {g : Ground A} {ℓ}
      → CastBlameSafe (inj A {g}) ℓ

    safe-proj : ∀ {B} {g : Ground B} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
      → CastBlameSafe (proj B ℓ′ {g}) ℓ

    safe-cfun : ∀ {S₁ S₂ T₁ T₂} {c : Cast (T₁ ⇒ S₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (cfun c d) ℓ

    safe-cpair : ∀ {S₁ S₂ T₁ T₂} {c : Cast (S₁ ⇒ T₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (cpair c d) ℓ

    safe-csum : ∀ {S₁ S₂ T₁ T₂} {c : Cast (S₁ ⇒ T₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (csum c d) ℓ

    safe-cseq : ∀ {T₁ T₂ T₃} {c : Cast (T₁ ⇒ T₂)} {d : Cast (T₂ ⇒ T₃)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (cseq c d) ℓ

  domBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (dom c x) ℓ
  domBlameSafe (safe-cfun safe-c safe-d) C-fun = safe-c

  codBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (cod c x) ℓ
  codBlameSafe (safe-cfun safe-c safe-d) C-fun = safe-d

  fstBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (fstC c x) ℓ
  fstBlameSafe (safe-cpair safe-c safe-d) C-pair = safe-c

  sndBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (sndC c x) ℓ
  sndBlameSafe (safe-cpair safe-c safe-d) C-pair = safe-d

  inlBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inlC c x) ℓ
  inlBlameSafe (safe-csum safe-c safe-d) C-sum = safe-c

  inrBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inrC c x) ℓ
  inrBlameSafe (safe-csum safe-c safe-d) C-sum = safe-d

  {-

  We instantiate the outer module of ParamCastReduction, obtaining the
  definitions for values and frames.

  -}
  open import PreCastStructure
  open import PreCastStructureWithBlameSafety

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
{-
             ; funSrc = funSrc
             ; pairSrc = pairSrc
             ; sumSrc = sumSrc
-}
             ; dom = dom
             ; cod = cod
             ; fstC = fstC
             ; sndC = sndC
             ; inlC = inlC
             ; inrC = inrC
             ; baseNotInert = baseNotInert
             ; idNotInert = idNotInert
             ; projNotInert = projNotInert
             }
  pcss : PreCastStructWithBlameSafety
  pcss = record
             { precast = pcs
             ; CastBlameSafe = CastBlameSafe
             ; domBlameSafe = domBlameSafe
             ; codBlameSafe = codBlameSafe
             ; fstBlameSafe = fstBlameSafe
             ; sndBlameSafe = sndBlameSafe
             ; inlBlameSafe = inlBlameSafe
             ; inrBlameSafe = inrBlameSafe
             }

  import ParamCastAux
  open ParamCastAux pcs
  open import ParamCastSubtyping pcss

  {-

  To instaniate the inner module that defines reduction and progress,
  we need to define a few more functions. The first is applyCast,
  which applies an active cast to a value. We comment each case with
  the reduction rule from Siek, Thiemann, and Wadler (2015). The
  definition of applyCast was driven by pattern matching on the
  parameter {c : Cast (A ⇒ B)}. (Perhaps it would have been better
  to pattern match on {a : Active c}.)

  -}

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  {-
    V⟨id⟩    —→    V
   -}
  applyCast M v id {a} = M
  {-
    V⟨G!⟩⟨G?⟩    —→    V
    V⟨G!⟩⟨H?p⟩   —→   blame p  if G ≠ H
   -}
  applyCast M v (proj B ℓ {gb}) {a} with canonical⋆ M v
  ... | ⟨ G , ⟨ V , ⟨ c , ⟨ I-inj {G}{ga} , meq ⟩ ⟩ ⟩ ⟩
         rewrite meq
         with gnd-eq? G B {ga} {gb}
  ...    | no neq = blame ℓ
  ...    | yes eq
            with eq
  ...       | refl = V
  {-
   V⟨c ; d⟩     —→    V⟨c⟩⟨d⟩
   -}
  applyCast M v (cseq c d) = (M ⟨ c ⟩) ⟨ d ⟩
  applyCast M v (cpair c d) {a} = eta× M (cpair c d) C-pair
  applyCast M v (csum c d) {a} = eta⊎ M (csum c d) C-sum
  applyCast M v (cfun c d) {()}
  applyCast M v (inj A) {()}

  applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → CastBlameSafe c ℓ
    → CastsAllSafe V ℓ
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe {vV = vV} {c = proj B ℓ′ {gB}} A-proj (safe-proj ℓ≢) allsafe with canonical⋆ _ vV
  ... | ⟨ G , ⟨ V′ , ⟨ _ , ⟨ I-inj {G} {g} , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with gnd-eq? G B {g} {gB}
  ...   | no _ = allsafe-blame-diff-ℓ ℓ≢
  ...   | yes refl with allsafe
  ...     | allsafe-wrap _ allsafe-V′ = allsafe-V′
  applyCast-pres-allsafe A-pair (safe-cpair safe-c safe-d) allsafe =
    allsafe-cons (allsafe-cast safe-c (allsafe-fst allsafe)) (allsafe-cast safe-d (allsafe-snd allsafe))
  applyCast-pres-allsafe A-sum (safe-csum safe-c safe-d) allsafe =
    allsafe-case allsafe (allsafe-inl (allsafe-cast safe-c allsafe-var))
                         (allsafe-inr (allsafe-cast safe-d allsafe-var))
  applyCast-pres-allsafe A-id _ allsafe = allsafe
  applyCast-pres-allsafe A-seq (safe-cseq safe-c safe-d) allsafe = allsafe-cast safe-d (allsafe-cast safe-c allsafe)

  {-
  We now instantiate the inner module of ParamCastReduction, thereby
  proving type safety for λC.
  -}

  open import CastStructure
  open import CastStructureWithBlameSafety

  cs : CastStruct
  cs = record { precast = pcs ; applyCast = applyCast }

  css : CastStructWithBlameSafety
  css = record { pcss = pcss ; applyCast = applyCast ; applyCast-pres-allsafe = applyCast-pres-allsafe }

  import ParamCastReduction
  open ParamCastReduction cs public

  -- Instantiate blame-subtyping theorem for `GroundCoercion`.
  open import ParamBlameSubtyping css using (soundness-<:) public
