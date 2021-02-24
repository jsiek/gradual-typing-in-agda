{-

  This module formalizes the λB calculus (Siek, Thiemann, Wadler
  2015), aka. the blame calculus without predicate types, and proves
  type safety via progress and preservation.

  This module is relatively small because it reuses the definitions
  and proofs from the Parameterized Cast Calculus. This module just
  has to provide the appropriate parameters.

-}

module GroundInertX where

  open import Data.Nat
  open import Data.Bool
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
    using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product
    using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
    renaming (_,_ to [_,_])
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)

  {-

   The λB calculus represents a cast as a pair of types, the source and target,
   and a blame label. The two types must be consistent.

   -}

  data Cast : Type → Set where
    cast : (A : Type) → (B : Type) → Label → A ~ B → Cast (A ⇒ B)

  {-

  We categorize casts into the inert ones (that form values) and
  the active ones (that reduce).

  For λB, there are two kinds of inert casts, those from a ground
  type to ⋆ and those between two function types.

n  -}

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A} → Ground A → (c : Cast (A ⇒ ⋆)) → Inert c
    -- All cross casts are inert!
    I-fun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Inert c
    I-pair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Inert c
    I-sum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Inert c

  {-

  The rest of the casts are active casts, which we further subdivide
  according to which reduction rule is applicable. We have the
  identity casts, the injections from non-ground types, the casts
  between pair types, and the casts between sum types.

  -}

  data Active : ∀ {A} → Cast A → Set where
    A-id : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    A-inj : ∀{A} → (c : Cast (A ⇒ ⋆)) → ¬ Ground A → A ≢ ⋆ → Active c
    A-proj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c

  open import ParamCastCalculus Cast Inert public

  open import GTLC2CC Cast Inert (λ A B ℓ {c} → cast A B ℓ c) public

  {-

   To show that every cast is either active or inert, we
   consider all the cases between two consistent types.

   -}

  base-consis-eq : ∀ {ι ι' : Base} → .(` ι ~ ` ι') → ι ≡ ι'
  base-consis-eq {Nat} {Nat} c = refl
  base-consis-eq {Int} {Int} c = refl
  base-consis-eq {𝔹} {𝔹} c = refl
  base-consis-eq {Unit} {Unit} c = refl
  -- Updated the constructor names according to the definition of base types in Primitives . - Tianyu
  base-consis-eq {Base.Void} {Base.Void} _ = refl
  base-consis-eq {Blame} {Blame} _ = refl

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert {.(⋆ ⇒ ⋆)} (cast ⋆ ⋆ ℓ A~B) = inj₁ (A-id {a = A-Unk} (cast ⋆ ⋆ ℓ A~B))
  ActiveOrInert {.(⋆ ⇒ ` ι)} (cast ⋆ (` ι) ℓ A~B) = inj₁ (A-proj (cast ⋆ (` ι) ℓ A~B) (λ ()))
  ActiveOrInert {.(⋆ ⇒ (B ⇒ B₁))} (cast ⋆ (B ⇒ B₁) ℓ A~B) = inj₁ (A-proj (cast ⋆ (B ⇒ B₁) ℓ A~B) (λ ()))
  ActiveOrInert {.(⋆ ⇒ B `× B₁)} (cast ⋆ (B `× B₁) ℓ A~B) = inj₁ (A-proj (cast ⋆ (B `× B₁) ℓ A~B) (λ ()))
  ActiveOrInert {.(⋆ ⇒ B `⊎ B₁)} (cast ⋆ (B `⊎ B₁) ℓ A~B) = inj₁ (A-proj (cast ⋆ (B `⊎ B₁) ℓ A~B) (λ ()))
  ActiveOrInert {.(` ι ⇒ ⋆)} (cast (` ι) ⋆ ℓ A~B) = inj₂ (I-inj G-Base (cast (` ι) ⋆ ℓ A~B))
  ActiveOrInert {.(` ι ⇒ ` ι')} (cast (` ι) (` ι') ℓ A~B)
      with base-consis-eq A~B
  ... | refl = inj₁ (A-id {a = A-Base} (cast (` ι) (` ι) ℓ A~B))
  ActiveOrInert {.((A ⇒ A₁) ⇒ ⋆)} (cast (A ⇒ A₁) ⋆ ℓ A~B)
      with ground? (A ⇒ A₁)
  ... | yes g = inj₂ (I-inj g (cast (A ⇒ A₁) ⋆ ℓ A~B))
  ... | no ng = inj₁ (A-inj (cast (A ⇒ A₁) ⋆ ℓ A~B) ng (λ ()))
  ActiveOrInert {.((A ⇒ A₁) ⇒ (B ⇒ B₁))} (cast (A ⇒ A₁) (B ⇒ B₁) ℓ A~B) = inj₂ (I-fun (cast (A ⇒ A₁) (B ⇒ B₁) ℓ A~B))
  ActiveOrInert {.(A `× A₁ ⇒ ⋆)} (cast (A `× A₁) ⋆ ℓ A~B)
      with ground? (A `× A₁)
  ... | yes g = inj₂ (I-inj g (cast (A `× A₁) ⋆ ℓ A~B))
  ... | no ng = inj₁ (A-inj (cast (A `× A₁) ⋆ ℓ A~B) ng (λ ()))
  ActiveOrInert {.(A `× A₁ ⇒ B `× B₁)} (cast (A `× A₁) (B `× B₁) ℓ A~B) = inj₂ (I-pair (cast (A `× A₁) (B `× B₁) ℓ A~B))
  ActiveOrInert {.(A `⊎ A₁ ⇒ ⋆)} (cast (A `⊎ A₁) ⋆ ℓ A~B)
      with ground? (A `⊎ A₁)
  ... | yes g = inj₂ (I-inj g (cast (A `⊎ A₁) ⋆ ℓ A~B))
  ... | no ng = inj₁ (A-inj (cast (A `⊎ A₁) ⋆ ℓ A~B) ng (λ ()))
  ActiveOrInert {.(A `⊎ A₁ ⇒ B `⊎ B₁)} (cast (A `⊎ A₁) (B `⊎ B₁) ℓ A~B) = inj₂ (I-sum (cast (A `⊎ A₁) (B `⊎ B₁) ℓ A~B))

  ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
  ActiveNotInert (A-id c) (I-inj () .c)
  ActiveNotInert (A-id {a = ()} c) (I-fun .c)
  ActiveNotInert (A-inj c ¬g _) (I-inj g .c) = ¬g g
  ActiveNotInert (A-proj c neq) (I-inj _ .c) = neq refl

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B A' B' ℓ} {cn} → Cross (cast (A ⇒ B) (A' ⇒ B') ℓ cn)
    C-pair : ∀{A B A' B' ℓ} {cn} → Cross (cast (A `× B) (A' `× B') ℓ cn)
    C-sum : ∀{A B A' B' ℓ} {cn} → Cross (cast (A `⊎ B) (A' `⊎ B') ℓ cn)

  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ (cast (A ⇒ B) (C ⇒ D) ℓ cn) (I-fun _) =
      [ C-fun , [ A , [ B , refl ] ] ]

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× (cast (A `× B) (C `× D) _ _) (I-pair _) = [ C-pair , [ A , [ B , refl ] ] ]

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ (cast (A `⊎ B) (C `⊎ D) _ _) (I-sum _) = [ C-sum , [ A , [ B , refl ] ] ]

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
  dom (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ c') x
      with ~-relevant c'
  ... | fun~ c d = cast A' A₁ ℓ c

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ c') x
      with ~-relevant c'
  ... | fun~ c d = cast A₂ B' ℓ d

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (cast (A `× B) (C `× D) ℓ c') x
      with ~-relevant c'
  ... | pair~ c d = cast A C ℓ c

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (cast (A `× B) (C `× D) ℓ c') x
      with ~-relevant c'
  ... | pair~ c d = cast B D ℓ d

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (cast (A `⊎ B) (C `⊎ D) ℓ c') x
      with ~-relevant c'
  ... | sum~ c d = cast A C ℓ c

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (cast (A `⊎ B) (C `⊎ D) ℓ c') x
      with ~-relevant c'
  ... | sum~ c d = cast B D ℓ d

  {-
  Finally, we show that casts to base type are not inert.
  -}

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a c = ActiveNotInert (A-id {a = a} c)

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j c = ActiveNotInert (A-proj c j)

  open import Subtyping using (_<:₃_)
  open _<:₃_
  infix 5 _<:_
  _<:_ = _<:₃_

  data Safe : ∀ {A} → Cast A → Label → Set where

    safe-<: : ∀ {S T} {c~ : S ~ T} {ℓ}
      → S <: T
        ----------------------------
      → Safe (cast S T ℓ c~) ℓ

    safe-ℓ≢ : ∀ {S T} {c~ : S ~ T} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
        -----------------------------
      → Safe (cast S T ℓ′ c~) ℓ

  domSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (dom c x) ℓ
  domSafe (safe-<: {c~ = c~} (<:-⇒ sub-dom sub-cod)) x with ~-relevant c~
  ... | fun~ d~ _ = safe-<: {c~ = d~} sub-dom
  domSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | fun~ d~ _ = safe-ℓ≢ {c~ = d~} ℓ≢

  codSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (cod c x) ℓ
  codSafe (safe-<: {c~ = c~} (<:-⇒ sub-dom sub-cod)) x with ~-relevant c~
  ... | fun~ _ d~ = safe-<: {c~ = d~} sub-cod
  codSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | fun~ _ d~ = safe-ℓ≢ {c~ = d~} ℓ≢

  fstSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (fstC c x) ℓ
  fstSafe (safe-<: {c~ = c~} (<:-× sub-fst sub-snd)) x with ~-relevant c~
  ... | pair~ d~ _ = safe-<: {c~ = d~} sub-fst
  fstSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | pair~ d~ _ = safe-ℓ≢ {c~ = d~} ℓ≢

  sndSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (sndC c x) ℓ
  sndSafe (safe-<: {c~ = c~} (<:-× sub-fst sub-snd)) x with ~-relevant c~
  ... | pair~ _ d~ = safe-<: {c~ = d~} sub-snd
  sndSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | pair~ _ d~ = safe-ℓ≢ {c~ = d~} ℓ≢

  inlSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (inlC c x) ℓ
  inlSafe (safe-<: {c~ = c~} (<:-⊎ sub-l sub-r)) x with ~-relevant c~
  ... | sum~ d~ _ = safe-<: {c~ = d~} sub-l
  inlSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | sum~ d~ _ = safe-ℓ≢ {c~ = d~} ℓ≢

  inrSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → Safe c ℓ → (x : Cross c)
            → Safe (inrC c x) ℓ
  inrSafe (safe-<: {c~ = c~} (<:-⊎ sub-l sub-r)) x with ~-relevant c~
  ... | sum~ _ d~ = safe-<: {c~ = d~} sub-r
  inrSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | sum~ _ d~ = safe-ℓ≢ {c~ = d~} ℓ≢


  infix 6 ⟪_⟫⊑⟪_⟫
  data ⟪_⟫⊑⟪_⟫ : ∀ {A A′ B B′} → {c : Cast (A ⇒ B)} → {c′ : Cast (A′ ⇒ B′)}
                               → (i : Inert c) → (i′ : Inert c′) → Set where

    -- Inert injections
    lpii-inj : ∀ {G} {c : Cast (G ⇒ ⋆)} {c′ : Cast (G ⇒ ⋆)}
      → (g : Ground G)
      → ⟪ I-inj g c ⟫⊑⟪ I-inj g c′ ⟫

    -- Inert cross casts
    lpii-fun : ∀ {A A′ B B′ C C′ D D′} {c : Cast ((A ⇒ B) ⇒ (C ⇒ D))} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
      → A ⇒ B ⊑ A′ ⇒ B′
      → C ⇒ D ⊑ C′ ⇒ D′
        ----------------------------------------------------------------------
      → ⟪ I-fun c ⟫⊑⟪ I-fun c′ ⟫

    lpii-pair : ∀ {A A′ B B′ C C′ D D′} {c : Cast ((A `× B) ⇒ (C `× D))} {c′ : Cast ((A′ `× B′) ⇒ (C′ `× D′))}
      → A `× B ⊑ A′ `× B′
      → C `× D ⊑ C′ `× D′
        ----------------------------------------------------------------------
      → ⟪ I-pair c ⟫⊑⟪ I-pair c′ ⟫

    lpii-sum : ∀ {A A′ B B′ C C′ D D′} {c : Cast ((A `⊎ B) ⇒ (C `⊎ D))} {c′ : Cast ((A′ `⊎ B′) ⇒ (C′ `⊎ D′))}
      → A `⊎ B ⊑ A′ `⊎ B′
      → C `⊎ D ⊑ C′ `⊎ D′
        ----------------------------------------------------------------------
      → ⟪ I-sum c ⟫⊑⟪ I-sum c′ ⟫

  infix 6 ⟪_⟫⊑_
  data ⟪_⟫⊑_ : ∀ {A B} → {c : Cast (A ⇒ B)} → Inert c → Type → Set where

    -- Inert injections
    lpit-inj : ∀ {G A′} {c : Cast (G ⇒ ⋆)}
      → (g : Ground G)
      → G ⊑ A′
        -------------------------
      → ⟪ I-inj g c ⟫⊑ A′

    -- Inert cross casts
    lpit-fun : ∀ {A A′ B B′ C D} {c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}
      → A ⇒ B ⊑ A′ ⇒ B′
      → C ⇒ D ⊑ A′ ⇒ B′
        ------------------------------------------
      → ⟪ I-fun c ⟫⊑ A′ ⇒ B′

    lpit-pair : ∀ {A A′ B B′ C D} {c : Cast ((A `× B) ⇒ (C `× D))}
      → A `× B ⊑ A′ `× B′
      → C `× D ⊑ A′ `× B′
        ------------------------------------------
      → ⟪ I-pair c ⟫⊑ A′ `× B′

    lpit-sum : ∀ {A A′ B B′ C D} {c : Cast ((A `⊎ B) ⇒ (C `⊎ D))}
      → A `⊎ B ⊑ A′ `⊎ B′
      → C `⊎ D ⊑ A′ `⊎ B′
        ------------------------------------------
      → ⟪ I-sum c ⟫⊑ A′ `⊎ B′

  infix 6 _⊑⟪_⟫
  data _⊑⟪_⟫ : ∀ {A′ B′} → {c′ : Cast (A′ ⇒ B′)} → Type → Inert c′ → Set where

    -- Inert cross casts
    lpti-fun : ∀ {A A′ B B′ C′ D′} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
      → A ⇒ B ⊑ A′ ⇒ B′
      → A ⇒ B ⊑ C′ ⇒ D′
        ---------------------------------------------
      → A ⇒ B ⊑⟪ I-fun c′ ⟫

    lpti-pair : ∀ {A A′ B B′ C′ D′} {c′ : Cast ((A′ `× B′) ⇒ (C′ `× D′))}
      → A `× B ⊑ A′ `× B′
      → A `× B ⊑ C′ `× D′
        ----------------------------------------------
      → A `× B ⊑⟪ I-pair c′ ⟫

    lpti-sum : ∀ {A A′ B B′ C′ D′} {c′ : Cast ((A′ `⊎ B′) ⇒ (C′ `⊎ D′))}
      → A `⊎ B ⊑ A′ `⊎ B′
      → A `⊎ B ⊑ C′ `⊎ D′
        ----------------------------------------------
      → A `⊎ B ⊑⟪ I-sum c′ ⟫

  inj-⊑-inj : ∀ {A A′ B′} {c : Cast (A ⇒ ⋆)} {c′ : Cast (A′ ⇒ B′)}
    → (i : Inert c) → (i′ : Inert c′)
    → ⟪ i ⟫⊑⟪ i′ ⟫
      --------------------
    → (A′ ≡ A) × (B′ ≡ ⋆)
  inj-⊑-inj .(I-inj g _) .(I-inj g _) (lpii-inj g) = [ refl , refl ]

  ⋆-⋢-inert : ∀ {A′ B′} {c′ : Cast (A′ ⇒ B′)}
    → (i′ : Inert c′)
      ----------------
    → ¬ (⋆ ⊑⟪ i′ ⟫)
  ⋆-⋢-inert _ = λ ()

  {- Lemmas about precision, suppose all casts are inert:
       1. It implies ⟨ A ⇒ B ⟩ ⊑ A′ if A ⊑ A′ and B ⊑ B′. -}
  ⊑→lpit : ∀ {A B A′} {c : Cast (A ⇒ B)}
    → (i : Inert c)
    → A ⊑ A′ → B ⊑ A′
      ------------------
    → ⟪ i ⟫⊑ A′
  ⊑→lpit (I-inj g _) lp1 lp2 = lpit-inj g lp1
  ⊑→lpit (I-fun _) (fun⊑ lp1 lp3) (fun⊑ lp2 lp4) = lpit-fun (fun⊑ lp1 lp3) (fun⊑ lp2 lp4)
  ⊑→lpit (I-pair _) (pair⊑ lp1 lp3) (pair⊑ lp2 lp4) = lpit-pair (pair⊑ lp1 lp3) (pair⊑ lp2 lp4)
  ⊑→lpit (I-sum _) (sum⊑ lp1 lp3) (sum⊑ lp2 lp4) = lpit-sum (sum⊑ lp1 lp3) (sum⊑ lp2 lp4)

  {-   2. It implies A ⊑ A′ and B ⊑ B′ if ⟨ A ⇒ B ⟩ ⊑ ⟨ A′ ⇒ B′ ⟩ . -}
  lpii→⊑ : ∀ {A A′ B B′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)} {i : Inert c} {i′ : Inert c′}
    → ⟪ i ⟫⊑⟪ i′ ⟫
      --------------------
    → (A ⊑ A′) × (B ⊑ B′)
  lpii→⊑ (lpii-inj g) = [ Refl⊑ , unk⊑ ]
  lpii→⊑ (lpii-fun lp1 lp2) = [ lp1 , lp2 ]
  lpii→⊑ (lpii-pair lp1 lp2) = [ lp1 , lp2 ]
  lpii→⊑ (lpii-sum lp1 lp2) = [ lp1 , lp2 ]

  {-   3. It implies A ⊑ A′ and B ⊑ A′ if ⟨ A ⇒ B ⟩ ⊑ A′ . -}
  lpit→⊑ : ∀ {A A′ B} {c : Cast (A ⇒ B)} {i : Inert c}
    → ⟪ i ⟫⊑ A′
      --------------------
    → (A ⊑ A′) × (B ⊑ A′)
  lpit→⊑ (lpit-inj g lp) = [ lp , unk⊑ ]
  lpit→⊑ (lpit-fun lp1 lp2) = [ lp1 , lp2 ]
  lpit→⊑ (lpit-pair lp1 lp2) = [ lp1 , lp2 ]
  lpit→⊑ (lpit-sum lp1 lp2) = [ lp1 , lp2 ]

  {-   4. It implies A ⊑ A′ and A ⊑ B′ if A ⊑ ⟨ A′ ⇒ B′ ⟩ . -}
  lpti→⊑ : ∀ {A A′ B′} {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
    → A ⊑⟪ i′ ⟫
      --------------------
    → (A ⊑ A′) × (A ⊑ B′)
  lpti→⊑ (lpti-fun lp1 lp2) = [ lp1 , lp2 ]
  lpti→⊑ (lpti-pair lp1 lp2) = [ lp1 , lp2 ]
  lpti→⊑ (lpti-sum lp1 lp2) = [ lp1 , lp2 ]

  open import PreCastStructure
  open import PreCastStructureWithPrecision
  {-

   We take the first step of instantiating the reduction semantics of
   the Parametric Cast Calculus by applying the ParamCastAux module.

   -}
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
             }
  pcss : PreCastStructWithSafety
  pcss = record
             { precast = pcs
             ; Safe = Safe
             ; domSafe = domSafe
             ; codSafe = codSafe
             ; fstSafe = fstSafe
             ; sndSafe = sndSafe
             ; inlSafe = inlSafe
             ; inrSafe = inrSafe
             }
  pcsp : PreCastStructWithPrecision
  pcsp = record {
           pcss = pcss;
           ⟪_⟫⊑⟪_⟫ = ⟪_⟫⊑⟪_⟫;
           ⟪_⟫⊑_ = ⟪_⟫⊑_;
           _⊑⟪_⟫ = _⊑⟪_⟫;
           inj-⊑-inj = inj-⊑-inj;
           ⋆-⋢-inert = ⋆-⋢-inert;
           ⊑→lpit = ⊑→lpit;
           lpii→⊑ = lpii→⊑;
           lpit→⊑ = lpit→⊑;
           lpti→⊑ = lpti→⊑
         }

  import ParamCastAux
  open ParamCastAux pcs
  open import ParamCastSubtyping pcss

  inert-ground : ∀{A} → (c : Cast (A ⇒ ⋆)) → Inert c → Ground A
  inert-ground c (I-inj g .c) = g

  {-

   To instantiate the ParamCastReduction module, we must provide
   several operations, the first of which is applyCast. This handles
   applying an active cast to a value. We comment each case with the
   reduction rule from Siek, Thiemann, and Wadler (2015). The
   definition of applyCast is driven by pattern matching on the
   parameter {a : Active c}.

   -}

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
     → ∀ {a : Active c} → Γ ⊢ B
  {-
    V : ι ⇒ ι   —→   V
   -}
  applyCast M v c {A-id c} = M
  {-
    V : A ⇒ ⋆   —→   V : A ⇒ G ⇒ ⋆
   -}
  applyCast M v (cast A ⋆ ℓ cn) {A-inj c a-ng a-nd}
      with ground A {a-nd}
  ... | [ G , cns ] = (M ⟨ cast A G ℓ (proj₂ cns) ⟩) ⟨ cast G ⋆ ℓ unk~R ⟩
  {-
    V : G ⇒p ⋆ ⇒q G  —→   V
    V : G ⇒p ⋆ ⇒q H  —→   blame q
   -}
  applyCast M v (cast ⋆ B ℓ cn) {A-proj c b-nd}
      with ground? B
  ... | yes b-g
          with canonical⋆ M v
  ...     | [ G , [ V , [ c' , [ i , meq ] ] ] ] rewrite meq
              with gnd-eq? G B {inert-ground c' i} {b-g}
  ...         | yes ap-b rewrite ap-b = V
  ...         | no ap-b = blame ℓ
  {-
    V : ⋆ ⇒ B   —→   V : ⋆ ⇒ H ⇒ B
   -}
  applyCast M v (cast ⋆ B ℓ cn) {A-proj c b-nd}
      | no b-ng with ground B {b-nd}
  ...    | [ H , [ h-g , cns ] ] =
           (M ⟨ cast ⋆ H ℓ unk~L ⟩) ⟨ cast H B ℓ (Sym~ cns) ⟩
  -- Since cross casts are all inert we don't have cases for them.

  applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → Safe c ℓ
    → CastsAllSafe V ℓ
      --------------------------------------
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe (A-id _) safe allsafe = allsafe
  applyCast-pres-allsafe (A-inj (cast ⋆ .⋆ _ _) _ ⋆≢⋆) (safe-<: <:-⋆) allsafe = contradiction refl ⋆≢⋆
  applyCast-pres-allsafe (A-inj (cast A .⋆ ℓ _) ¬gA A≢⋆) (safe-<: (<:-G A<:G gG)) allsafe with A | gG | ground A {A≢⋆}
  ... | ` ι | G-Base | [ ` ι  , [ G-Base , base~ ] ] = allsafe-cast (safe-<: (<:-G A<:G gG)) (allsafe-cast (safe-<: <:-B) allsafe)
  ... | (A₁ ⇒ A₂) | G-Fun | [ ⋆ ⇒ ⋆ , [ G-Fun , _ ] ] =
    allsafe-cast (safe-<: {c~ = unk~R} (<:-G (<:-⇒ <:-⋆ <:-⋆) gG)) (allsafe-cast (safe-<: A<:G) allsafe)
  ... | (A₁ `× A₂) | G-Pair | [ ⋆ `× ⋆ , [ G-Pair , _ ] ] =
    allsafe-cast (safe-<: {c~ = unk~R} (<:-G (<:-× <:-⋆ <:-⋆) gG)) (allsafe-cast (safe-<: A<:G) allsafe)
  ... | (A₁ `⊎ A₂) | G-Sum | [ ⋆ `⊎ ⋆ , [ G-Sum , _ ] ] =
    allsafe-cast (safe-<: {c~ = unk~R} (<:-G (<:-⊎ <:-⋆ <:-⋆) gG)) (allsafe-cast (safe-<: A<:G) allsafe)
  applyCast-pres-allsafe (A-inj (cast A .⋆ ℓ′ _) _ A≢⋆) (safe-ℓ≢ ℓ≢) allsafe with ground A {A≢⋆}
  ... | [ ` ι  , [ G-Base , c~ ] ] = allsafe-cast (safe-ℓ≢ {c~ = unk~R} ℓ≢) (allsafe-cast (safe-ℓ≢ {c~ = c~} ℓ≢) allsafe)
  ... | [ ⋆ ⇒ ⋆ , [ G-Fun , c~ ] ] = allsafe-cast (safe-ℓ≢ {c~ = unk~R} ℓ≢) (allsafe-cast (safe-ℓ≢ {c~ = c~} ℓ≢) allsafe)
  ... | [ ⋆ `× ⋆ , [ G-Pair , c~ ] ] = allsafe-cast (safe-ℓ≢ {c~ = unk~R} ℓ≢) (allsafe-cast (safe-ℓ≢ {c~ = c~} ℓ≢) allsafe)
  ... | [ ⋆ `⊎ ⋆ , [ G-Sum , c~ ] ] = allsafe-cast (safe-ℓ≢ {c~ = unk~R} ℓ≢) (allsafe-cast (safe-ℓ≢ {c~ = c~} ℓ≢) allsafe)
  applyCast-pres-allsafe (A-proj (cast ⋆ .⋆ ℓ _) ⋆≢⋆) (safe-<: <:-⋆) allsafe = contradiction refl ⋆≢⋆
  applyCast-pres-allsafe (A-proj (cast ⋆ .⋆ ℓ _) ⋆≢⋆) (safe-<: (<:-G _ _)) allsafe = contradiction refl ⋆≢⋆
  applyCast-pres-allsafe {vV = vV} (A-proj (cast ⋆ B ℓ′ _) B≢⋆) (safe-ℓ≢ ℓ≢) allsafe with ground? B
  ... | yes gB with canonical⋆ _ vV
  ...   | [ G , [ V , [ c , [ i , meq ] ] ] ] rewrite meq with gnd-eq? G B {inert-ground c i} {gB}
  ...     | yes eq rewrite eq with allsafe
  ...       | allsafe-wrap _ allsafe-V = allsafe-V
  applyCast-pres-allsafe {vV = vV} (A-proj (cast ⋆ B ℓ′ _) B≢⋆) (safe-ℓ≢ ℓ≢) allsafe | yes gB | _ | no _ = allsafe-blame-diff-ℓ ℓ≢
  applyCast-pres-allsafe {vV = vV} (A-proj (cast ⋆ B ℓ′ _) B≢⋆) (safe-ℓ≢ ℓ≢) allsafe | no ¬gB with ground B {B≢⋆}
  ...   | [ H , [ gH , c~ ] ] = allsafe-cast (safe-ℓ≢ {c~ = Sym~ c~} ℓ≢) (allsafe-cast (safe-ℓ≢ {c~ = unk~L} ℓ≢) allsafe)

  open import CastStructure

  cs : CastStruct
  cs = record
             { pcss = pcss
             ; applyCast = applyCast
             ; applyCast-pres-allsafe = applyCast-pres-allsafe
             }

  {-

  We now instantiate the module ParamCastReduction, thereby proving
  type safety for λB.

  -}
  open import ParamCastReduction cs

  -- Instantiate blame-subtyping theorem for `GroundCast`.
  open import ParamBlameSubtyping cs using (soundness-<:) public


  {- A few lemmas to prove `catchup`. -}
  open import ParamCCPrecision pcsp
  private
    wrapV-⊑-inv : ∀ {Γ Γ′ A A′} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ ⋆)}
      → Value V → Value V′ → (i : Inert c) → A′ ≢ ⋆
      → Γ , Γ′ ⊢ V ⟪ i ⟫ ⊑ᶜ V′
        ------------------------
      → Γ , Γ′ ⊢ V ⊑ᶜ V′
    wrapV-⊑-inv v v' (I-inj g c) nd (⊑ᶜ-wrap (lpii-inj .g) lpVi) = contradiction refl nd
    wrapV-⊑-inv v v' i nd (⊑ᶜ-wrapl x lpVi) = lpVi

    ground-to-ndng-inert : ∀ {H B} {ℓ}
      → (c~ : H ~ B)
      → Ground H → B ≢ ⋆ → ¬ Ground B
        --------------------------------
      → Inert (cast H B ℓ c~)
    ground-to-ndng-inert unk~R h-g b-nd b-ng = contradiction refl b-nd
    ground-to-ndng-inert base~ h-g b-nd b-ng = contradiction h-g b-ng
    ground-to-ndng-inert (fun~ c~ c~₁) h-g b-nd b-ng = I-fun _
    ground-to-ndng-inert (pair~ c~ c~₁) h-g b-nd b-ng = I-pair _
    ground-to-ndng-inert (sum~ c~ c~₁) h-g b-nd b-ng = I-sum _

    {-
      We write ground / non-ground as separate lemmas to get around Agda's termination checker:
      this is because the first, ground one does not make any recursive call and the
      second, non-ground one calls into the first one, which serves as a base case.
    -}
    applyCast-proj-g-catchup : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
      → (nd : B ≢ ⋆) → Ground B   -- B ≢ ⋆ is actually implied since B is ground.
      → (vV : Value V) → Value V′
      → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
        ----------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
    applyCast-proj-g-catchup {c = cast .⋆ B ℓ _} nd g v v′ lp lpV
      with ground? B
    ... | yes b-g
      with canonical⋆ _ v
    ...   | [ G , [ V₁ , [ c₁ , [ i , meq ] ] ] ] rewrite meq
      with gnd-eq? G B {inert-ground c₁ i} {b-g}
    ...     | yes ap-b rewrite ap-b
      with v
    ...       | V-wrap vV₁ .i = [ V₁ , [ vV₁ , [ V₁ ∎ , wrapV-⊑-inv vV₁ v′ i (lp-¬⋆ nd lp) lpV ] ] ]
    applyCast-proj-g-catchup {c = cast .⋆ B ℓ _} nd g v v′ lp lpV | yes b-g | [ G , [ V₁ , [ c₁ , [ I-inj g₁ _ , meq ] ] ] ] | no ap-b
      with lpV
    ...       | ⊑ᶜ-wrapl (lpit-inj _ lp₁) _ = contradiction (lp-consis-ground-eq g₁ g Refl~ lp₁ lp) ap-b
    ...       | ⊑ᶜ-wrap (lpii-inj _) _ = contradiction lp (nd⋢⋆ nd)
    applyCast-proj-g-catchup {c = cast .⋆ B ℓ _} nd g v v′ lp lpV | no b-ng = contradiction g b-ng

    applyCast-proj-ng-catchup : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
      → (nd : B ≢ ⋆) → ¬ Ground B
      → (vV : Value V) → Value V′
      → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
        ----------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
    applyCast-proj-ng-catchup {c = cast .⋆ B ℓ _} nd ng v v′ lp lpV
      with ground? B
    ... | yes b-g = contradiction b-g ng
    ... | no b-ng
      with ground B {nd}
    ...   | [ H , [ h-g , c~ ] ]
      with applyCast-proj-g-catchup {c = cast ⋆ H ℓ unk~L} (ground-nd h-g) h-g v v′ (⊑-ground-relax h-g lp c~ nd) lpV
    ...     | [ W , [ vW , [ rd* , lpW ] ] ] =
      {- The important observation here is that the expanded casts are an active projection
         to ground followed by an inert cross cast. -}
      -- The 1st cast ⋆ ⇒ H is active since H is ground.
      let a = A-proj (cast ⋆ H ℓ unk~L) (ground-nd h-g)
      -- The 2nd cast H ⇒ B is inert since it is cross.
          i = ground-to-ndng-inert {ℓ = ℓ} (Sym~ c~) h-g nd ng in
        [ W ⟪ i ⟫ ,
          [ V-wrap vW i ,
            [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {a} ⟩ rd*)) (_ —→⟨ wrap vW {i} ⟩ _ ∎) ,
              ⊑ᶜ-wrapl (⊑→lpit i (⊑-ground-relax h-g lp c~ nd) lp) lpW ] ] ]

    {-
      Finally, we case on whether the target type of the cast, B, is ground, for which
      we've already proved both cases. As is mentioned above, we make it very sure that
      the proof terminates - even if in the expansion case, the term grows bigger by one cast.
    -}
    applyCast-proj-catchup : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
      → (nd : B ≢ ⋆)
      → (vV : Value V) → Value V′
      → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
        ----------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
    applyCast-proj-catchup {B = B} {c = c} nd v v′ lp lpV
      with ground? B
    ... | yes g = applyCast-proj-g-catchup {c = c} nd g v v′ lp lpV
    ... | no ng = applyCast-proj-ng-catchup {c = c} nd ng v v′ lp lpV

  applyCast-catchup : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
    → (a : Active c)
    → (vV : Value V) → Value V′
    → A ⊑ A′ → B ⊑ A′
    → Γ , Γ′ ⊢ V ⊑ᶜ V′
      ----------------------------------------------------------
    → ∃[ W ] ((Value W) × (applyCast V vV c {a} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
  applyCast-catchup (A-id _) vV vV′ lp1 lp2 lpV = [ _ , [ vV , [ _ ∎ , lpV ] ] ]
  applyCast-catchup {A = A} {V = V} {c = cast A ⋆ ℓ _} (A-inj c a-ng a-nd) vV vV′ lp1 lp2 lpV
    with ground A {a-nd}
  ... | [ G , [ g , c~ ] ]
    with g | c~ | lp1
  ...   | G-Base | base~ | _ =
    let i = I-inj g (cast G ⋆ ℓ unk~R) in
      [ V ⟪ i ⟫ , [ V-wrap vV i , [ _ —→⟨ ξ (cast vV {A-id {a = A-Base} _}) ⟩ _ —→⟨ wrap vV {i} ⟩ _ ∎ ,
                                    ⊑ᶜ-wrapl (lpit-inj g lp1) lpV ] ] ]
  ...   | G-Base | unk~L | _ = contradiction refl a-nd
  ...   | G-Fun | fun~ c~₁ c~₂ | fun⊑ lp11 lp12 =
    let i₁ = I-fun (cast A G ℓ (fun~ c~₁ c~₂))
        i₂ = I-inj g (cast G ⋆ ℓ unk~R) in
      [ V ⟪ i₁ ⟫ ⟪ i₂ ⟫ , [ V-wrap (V-wrap vV i₁) i₂ ,
        [ _ —→⟨ ξ (wrap vV {i₁}) ⟩ _ —→⟨ wrap (V-wrap vV i₁) {i₂} ⟩ _ ∎ ,
          ⊑ᶜ-wrapl (lpit-inj g (⊑-ground-relax g lp1 c~ a-nd)) (⊑ᶜ-wrapl (lpit-fun lp1 ground-fun-⊑) lpV) ] ] ]
  ...   | G-Fun | unk~L | _ = contradiction refl a-nd
  ...   | G-Pair | pair~ c~₁ c~₂ | pair⊑ lp11 lp12 =
    let i₁ = I-pair (cast A G ℓ (pair~ c~₁ c~₂))
        i₂ = I-inj g (cast G ⋆ ℓ unk~R) in
      [ V ⟪ i₁ ⟫ ⟪ i₂ ⟫ , [ V-wrap (V-wrap vV i₁) i₂ ,
        [ _ —→⟨ ξ (wrap vV {i₁}) ⟩ _ —→⟨ wrap (V-wrap vV i₁) {i₂} ⟩ _ ∎ ,
          ⊑ᶜ-wrapl (lpit-inj g (⊑-ground-relax g lp1 c~ a-nd)) (⊑ᶜ-wrapl (lpit-pair lp1 ground-pair-⊑) lpV) ] ] ]
  ...   | G-Pair | unk~L | _ = contradiction refl a-nd
  ...   | G-Sum | sum~ c~₁ c~₂ | sum⊑ lp11 lp12 =
    let i₁ = I-sum (cast A G ℓ (sum~ c~₁ c~₂))
        i₂ = I-inj g (cast G ⋆ ℓ unk~R) in
      [ V ⟪ i₁ ⟫ ⟪ i₂ ⟫ , [ V-wrap (V-wrap vV i₁) i₂ ,
        [ _ —→⟨ ξ (wrap vV {i₁}) ⟩ _ —→⟨ wrap (V-wrap vV i₁) {i₂} ⟩ _ ∎ ,
          ⊑ᶜ-wrapl (lpit-inj g (⊑-ground-relax g lp1 c~ a-nd)) (⊑ᶜ-wrapl (lpit-sum lp1 ground-sum-⊑) lpV) ] ] ]
  ...   | G-Sum | unk~L | _ = contradiction refl a-nd
  applyCast-catchup (A-proj c b-nd) vV vV′ lp1 lp2 lpV = applyCast-proj-catchup {c = c} b-nd vV vV′ lp2 lpV

  private
    inert-inj-⊑-inert-inj : ∀ {G G′} → {c : Cast (G ⇒ ⋆)} → {c′ : Cast (G′ ⇒ ⋆)}
      → (g : Ground G) → (g′ : Ground G′)
      → G ⊑ G′
        ------------------------------------------
      → ⟪ Inert.I-inj g c ⟫⊑⟪ Inert.I-inj g′ c′ ⟫
    inert-inj-⊑-inert-inj g g′ lp with ground-⊑-eq g g′ lp | g | g′
    ... | refl | G-Base | G-Base = lpii-inj G-Base
    ... | refl | G-Fun  | G-Fun  = lpii-inj G-Fun
    ... | refl | G-Pair | G-Pair = lpii-inj G-Pair
    ... | refl | G-Sum  | G-Sum  = lpii-inj G-Sum

    dyn-value-⊑-wrap : ∀ {A′ B′} {V : ∅ ⊢ ⋆} {V′ : ∅ ⊢ A′} {c′ : Cast (A′ ⇒ B′)}
      → Value V → Value V′
      → (i′ : Inert c′)
      → ∅ , ∅ ⊢ V ⊑ᶜ V′
        -----------------------
      → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
    dyn-value-⊑-wrap v v′ (Inert.I-inj () (cast .⋆ .⋆ _ _)) (⊑ᶜ-wrap (lpii-inj g) lpV)
    dyn-value-⊑-wrap v v′ (Inert.I-inj g′ (cast A′ .⋆ _ _)) (⊑ᶜ-wrapl (lpit-inj g lp) lpV)
      with ground-⊑-eq g g′ lp
    ... | refl = ⊑ᶜ-wrap (inert-inj-⊑-inert-inj g g′ lp) lpV
    dyn-value-⊑-wrap v v′ (Inert.I-fun (cast .(_ ⇒ _) .(_ ⇒ _) _ _)) (⊑ᶜ-wrapl (lpit-inj G-Fun (fun⊑ _ _)) lpV) =
      ⊑ᶜ-wrapl (lpit-inj G-Fun (fun⊑ unk⊑ unk⊑)) (⊑ᶜ-wrapr (lpti-fun (fun⊑ unk⊑ unk⊑) (fun⊑ unk⊑ unk⊑)) lpV)
    dyn-value-⊑-wrap v v′ (Inert.I-pair (cast .(_ `× _) .(_ `× _) _ _)) (⊑ᶜ-wrapl (lpit-inj G-Pair (pair⊑ _ _)) lpV) =
      ⊑ᶜ-wrapl (lpit-inj G-Pair (pair⊑ unk⊑ unk⊑)) (⊑ᶜ-wrapr (lpti-pair (pair⊑ unk⊑ unk⊑) (pair⊑ unk⊑ unk⊑)) lpV)
    dyn-value-⊑-wrap v v′ (Inert.I-sum (cast .(_ `⊎ _) .(_ `⊎ _) _ _)) (⊑ᶜ-wrapl (lpit-inj G-Sum (sum⊑ _ _)) lpV) =
      ⊑ᶜ-wrapl (lpit-inj G-Sum (sum⊑ unk⊑ unk⊑)) (⊑ᶜ-wrapr (lpti-sum (sum⊑ unk⊑ unk⊑) (sum⊑ unk⊑ unk⊑)) lpV)

  open import ParamGradualGuaranteeAux pcsp

  applyCast-⊑-wrap : ∀ {A A′ B B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → (v : Value V) → Value V′
    → (a : Active c) → (i′ : Inert c′)
    → A ⊑ A′ → B ⊑ B′
    → ∅ , ∅ ⊢ V ⊑ᶜ V′
      -----------------------------------------
    → ∅ , ∅ ⊢ applyCast V v c {a} ⊑ᶜ V′ ⟪ i′ ⟫
  -- Id
  applyCast-⊑-wrap v v′ (A-id _) i′ lp1 unk⊑ lpV = dyn-value-⊑-wrap v v′ i′ lpV
  -- Inj
  applyCast-⊑-wrap v v′ (A-inj (cast .⋆ .⋆ _ _) ng nd) (I-inj g′ _) unk⊑ _ lpV = contradiction refl nd
  applyCast-⊑-wrap v v′ (A-inj (cast .(` _) .⋆ _ _) ng nd) (I-inj G-Base _) base⊑ _ lpV = contradiction G-Base ng
  applyCast-⊑-wrap v v′ (A-inj (cast .(_ ⇒ _) .⋆ _ _) ng nd) (I-inj G-Fun _) (fun⊑ unk⊑ unk⊑) _ lpV = contradiction G-Fun ng
  applyCast-⊑-wrap v v′ (A-inj (cast .(_ `× _) .⋆ _ _) ng nd) (I-inj G-Pair _) (pair⊑ unk⊑ unk⊑) _ lpV = contradiction G-Pair ng
  applyCast-⊑-wrap v v′ (A-inj (cast .(_ `⊎ _) .⋆ _ _) ng nd) (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) _ lpV = contradiction G-Sum ng
  applyCast-⊑-wrap v v′ (A-inj (cast .⋆ .⋆ _ _) ng nd) (I-fun _) unk⊑ _ lpV = contradiction refl nd
  applyCast-⊑-wrap v v′ (A-inj (cast .(_ ⇒ _) .⋆ _ _) ng nd) (I-fun _) (fun⊑ lp1 lp2) _ lpV
    with ground _ {nd}
  ... | [ ⋆ ⇒ ⋆ , [ G-Fun , _ ] ] =
    ⊑ᶜ-castl (fun⊑ unk⊑ unk⊑) unk⊑ (⊑ᶜ-wrapr (lpti-fun (fun⊑ unk⊑ unk⊑) (fun⊑ unk⊑ unk⊑))
                                             (⊑ᶜ-castl (fun⊑ lp1 lp2) (fun⊑ unk⊑ unk⊑) lpV))
  applyCast-⊑-wrap v v′ (A-inj (cast .⋆ .⋆ _ _) ng nd) (I-pair _) unk⊑ _ lpV = contradiction refl nd
  applyCast-⊑-wrap v v′ (A-inj (cast .(_ `× _) .⋆ _ _) ng nd) (I-pair _) (pair⊑ lp1 lp2) _ lpV
    with ground _ {nd}
  ... | [ ⋆ `× ⋆ , [ G-Pair , _ ] ] =
    ⊑ᶜ-castl (pair⊑ unk⊑ unk⊑) unk⊑ (⊑ᶜ-wrapr (lpti-pair (pair⊑ unk⊑ unk⊑) (pair⊑ unk⊑ unk⊑))
                                              (⊑ᶜ-castl (pair⊑ lp1 lp2) (pair⊑ unk⊑ unk⊑) lpV))
  applyCast-⊑-wrap v v′ (A-inj (cast .⋆ .⋆ _ _) ng nd) (I-sum _) unk⊑ _ lpV = contradiction refl nd
  applyCast-⊑-wrap v v′ (A-inj (cast .(_ `⊎ _) .⋆ _ _) ng nd) (I-sum _) (sum⊑ lp1 lp2) _ lpV
    with ground _ {nd}
  ... | [ ⋆ `⊎ ⋆ , [ G-Sum , _ ] ] =
    ⊑ᶜ-castl (sum⊑ unk⊑ unk⊑) unk⊑ (⊑ᶜ-wrapr (lpti-sum (sum⊑ unk⊑ unk⊑) (sum⊑ unk⊑ unk⊑))
                                             (⊑ᶜ-castl (sum⊑ lp1 lp2) (sum⊑ unk⊑ unk⊑) lpV))
  -- Proj
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ B _ _) nd) (I-inj x _) _ unk⊑ lpV = contradiction refl nd
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ .⋆ _ _) nd) (I-fun _) _ unk⊑ lpV = contradiction refl nd
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ (A ⇒ B) _ _) _) (I-fun _) _ (fun⊑ lp1 lp2) lpV
    with ground? (A ⇒ B)
  ... | yes G-Fun
    with canonical⋆ _ v
  ...   | [ G , [ W , [ c₁ , [ i₁ , meq ] ] ] ] rewrite meq
    with gnd-eq? G (A ⇒ B) {inert-ground _ i₁} {G-Fun}
  ...     | yes ap rewrite ap = ⊑ᶜ-wrapr (lpti-fun (fun⊑ unk⊑ unk⊑) (fun⊑ lp1 lp2)) (wrap-⊑-value-inv (λ ()) v v′ lpV)
  ...     | no  ap with lpV
  ...       | ⊑ᶜ-wrapl (lpit-inj G-Fun (fun⊑ _ _)) lpW = contradiction refl ap
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ (A ⇒ B) _ _) nd) (I-fun _) _ (fun⊑ lp1 lp2) lpV | no ng
    with ground _ {nd}
  ... | [ ⋆ ⇒ ⋆ , [ G-Fun , _ ] ] =
    ⊑ᶜ-castl (fun⊑ unk⊑ unk⊑) (fun⊑ lp1 lp2) (⊑ᶜ-wrapr (lpti-fun (fun⊑ unk⊑ unk⊑) (fun⊑ unk⊑ unk⊑))
                                                       (⊑ᶜ-castl unk⊑ (fun⊑ unk⊑ unk⊑) lpV))
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ .⋆ _ _) nd) (I-pair _) _ unk⊑ lpV = contradiction refl nd
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ (A `× B) _ _) _) (I-pair _) _ (pair⊑ lp1 lp2) lpV
    with ground? (A `× B)
  ... | yes G-Pair
    with canonical⋆ _ v
  ...   | [ G , [ W , [ c₁ , [ i₁ , meq ] ] ] ] rewrite meq
    with gnd-eq? G (A `× B) {inert-ground _ i₁} {G-Pair}
  ...     | yes ap rewrite ap = ⊑ᶜ-wrapr (lpti-pair (pair⊑ unk⊑ unk⊑) (pair⊑ lp1 lp2)) (wrap-⊑-value-inv (λ ()) v v′ lpV)
  ...     | no  ap with lpV
  ...       | ⊑ᶜ-wrapl (lpit-inj G-Pair (pair⊑ _ _)) lpW = contradiction refl ap
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ (A `× B) _ _) nd) (I-pair _) _ (pair⊑ lp1 lp2) lpV | no ng
    with ground _ {nd}
  ... | [ ⋆ `× ⋆ , [ G-Pair , _ ] ] =
    ⊑ᶜ-castl (pair⊑ unk⊑ unk⊑) (pair⊑ lp1 lp2) (⊑ᶜ-wrapr (lpti-pair (pair⊑ unk⊑ unk⊑) (pair⊑ unk⊑ unk⊑))
                                                         (⊑ᶜ-castl unk⊑ (pair⊑ unk⊑ unk⊑) lpV))
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ .⋆ _ _) nd) (I-sum _) _ unk⊑ lpV = contradiction refl nd
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ (A `⊎ B) _ _) _) (I-sum _) _ (sum⊑ lp1 lp2) lpV
    with ground? (A `⊎ B)
  ... | yes G-Sum
    with canonical⋆ _ v
  ...   | [ G , [ W , [ c₁ , [ i₁ , meq ] ] ] ] rewrite meq
    with gnd-eq? G (A `⊎ B) {inert-ground _ i₁} {G-Sum}
  ...     | yes ap rewrite ap = ⊑ᶜ-wrapr (lpti-sum (sum⊑ unk⊑ unk⊑) (sum⊑ lp1 lp2)) (wrap-⊑-value-inv (λ ()) v v′ lpV)
  ...     | no  ap with lpV
  ...       | ⊑ᶜ-wrapl (lpit-inj G-Sum (sum⊑ _ _)) lpW = contradiction refl ap
  applyCast-⊑-wrap v v′ (A-proj (cast .⋆ (A `⊎ B) _ _) nd) (I-sum _) _ (sum⊑ lp1 lp2) lpV | no ng
    with ground _ {nd}
  ... | [ ⋆ `⊎ ⋆ , [ G-Sum , _ ] ] =
    ⊑ᶜ-castl (sum⊑ unk⊑ unk⊑) (sum⊑ lp1 lp2) (⊑ᶜ-wrapr (lpti-sum (sum⊑ unk⊑ unk⊑) (sum⊑ unk⊑ unk⊑))
                                                       (⊑ᶜ-castl unk⊑ (sum⊑ unk⊑ unk⊑) lpV))

  open import CastStructureWithPrecision
  csp : CastStructWithPrecision
  csp = record {
          pcsp = pcsp;
          applyCast = applyCast;
          applyCast-pres-allsafe = applyCast-pres-allsafe;
          applyCast-catchup = applyCast-catchup;
          applyCast-⊑-wrap = applyCast-⊑-wrap
        }

  {- Instantiate the proof of "compilation from GTLC to CC preserves precision". -}
  open import CompilePresPrec pcsp
  open CompilePresPrecProof (λ A B ℓ {c} → cast A B ℓ c) using (compile-pres-prec) public

  -- open import ParamGradualGuaranteeSim csp
