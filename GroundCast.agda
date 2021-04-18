{-

  This module formalizes the λB calculus (Siek, Thiemann, Wadler
  2015), aka. the blame calculus without predicate types, and proves
  type safety via progress and preservation.

  This module is relatively small because it reuses the definitions
  and proofs from the Parameterized Cast Calculus. This module just
  has to provide the appropriate parameters.

-}

module GroundCast where

  open import Data.Nat
  open import Data.Bool
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
     renaming (_,_ to [_,_])
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)

  {-

   The λB calculus represents a cast as a pair of types, the source and target,
   and a blame label. The two types must be consistent.

   -}

  data Cast : Type → Set where
    cast : (A : Type) → (B : Type) → Label → .(A ~ B) → Cast (A ⇒ B)

  {-

  We categorize casts into the inert ones (that form values) and
  the active ones (that reduce).

  For λB, there are two kinds of inert casts, those from a ground
  type to ⋆ and those between two function types.

n  -}

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A} → Ground A → (c : Cast (A ⇒ ⋆)) → Inert c
    I-fun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Inert c

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
    A-pair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    A-sum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c

  import ParamCastCalculus
  open ParamCastCalculus Cast Inert public

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
  ActiveOrInert {.(A `× A₁ ⇒ B `× B₁)} (cast (A `× A₁) (B `× B₁) ℓ A~B) = inj₁ (A-pair (cast (A `× A₁) (B `× B₁) ℓ A~B))
  ActiveOrInert {.(A `⊎ A₁ ⇒ ⋆)} (cast (A `⊎ A₁) ⋆ ℓ A~B)
      with ground? (A `⊎ A₁)
  ... | yes g = inj₂ (I-inj g (cast (A `⊎ A₁) ⋆ ℓ A~B))
  ... | no ng = inj₁ (A-inj (cast (A `⊎ A₁) ⋆ ℓ A~B) ng (λ ()))
  ActiveOrInert {.(A `⊎ A₁ ⇒ B `⊎ B₁)} (cast (A `⊎ A₁) (B `⊎ B₁) ℓ A~B) = inj₁ (A-sum (cast (A `⊎ A₁) (B `⊎ B₁) ℓ A~B))

  ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
  ActiveNotInert (A-id c) (I-inj () .c)
  ActiveNotInert (A-id {a = ()} c) (I-fun .c)
  ActiveNotInert (A-inj c ¬g _) (I-inj g .c) = ¬g g
  ActiveNotInert (A-proj c neq) (I-inj _ .c) = neq refl

  from-dyn-active : ∀ {ℓ} → (B : Type) → Active (cast ⋆ B ℓ unk~L)
  from-dyn-active {ℓ} B with eq-unk B
  ... | yes refl = A-id {a = A-Unk} (cast ⋆ ⋆ ℓ unk~L)
  ... | no nd = A-proj (cast ⋆ B ℓ unk~L) nd

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B A' B' ℓ} .{cn} → Cross (cast (A ⇒ B) (A' ⇒ B') ℓ cn)
    C-pair : ∀{A B A' B' ℓ} .{cn} → Cross (cast (A `× B) (A' `× B') ℓ cn)
    C-sum : ∀{A B A' B' ℓ} .{cn} → Cross (cast (A `⊎ B) (A' `⊎ B') ℓ cn)

  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ (cast (A ⇒ B) (C ⇒ D) ℓ cn) (I-fun _) =
      [ C-fun , [ A , [ B , refl ] ] ]

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× (cast A .(_ `× _) x x₁) ()

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ (cast A .(_ `⊎ _) x x₁) ()

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
        -----------------------------------------
      → ⟪ I-inj g c ⟫⊑⟪ I-inj g c′ ⟫

    -- Inert cross casts
    lpii-fun : ∀ {A A′ B B′ C C′ D D′} {c : Cast ((A ⇒ B) ⇒ (C ⇒ D))} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
     → A ⇒ B ⊑ A′ ⇒ B′
     → C ⇒ D ⊑ C′ ⇒ D′
       -------------------------------------
     → ⟪ I-fun c ⟫⊑⟪ I-fun c′ ⟫

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

  infix 6 _⊑⟪_⟫
  data _⊑⟪_⟫ : ∀ {A′ B′} → {c′ : Cast (A′ ⇒ B′)} → Type → Inert c′ → Set where
    -- Inert cross casts
    lpti-fun : ∀ {A A′ B B′ C′ D′} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
      → A ⇒ B ⊑ A′ ⇒ B′
      → A ⇒ B ⊑ C′ ⇒ D′
        ---------------------------------------------
      → A ⇒ B ⊑⟪ Inert.I-fun c′ ⟫

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

  ⊑→lpit : ∀ {A B A′} {c : Cast (A ⇒ B)}
    → (i : Inert c)
    → A ⊑ A′ → B ⊑ A′
      ------------------
    → ⟪ i ⟫⊑ A′
  ⊑→lpit (I-inj g _) lp1 lp2 = lpit-inj g lp1
  ⊑→lpit (I-fun _) (fun⊑ lp1 lp3) (fun⊑ lp2 lp4) = lpit-fun (fun⊑ lp1 lp3) (fun⊑ lp2 lp4)

  lpii→⊑ : ∀ {A A′ B B′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)} {i : Inert c} {i′ : Inert c′}
    → ⟪ i ⟫⊑⟪ i′ ⟫
      --------------------
    → (A ⊑ A′) × (B ⊑ B′)
  lpii→⊑ (lpii-inj g) = [ Refl⊑ , unk⊑ ]
  lpii→⊑ (lpii-fun lp1 lp2) = [ lp1 , lp2 ]

  lpit→⊑ : ∀ {A A′ B} {c : Cast (A ⇒ B)} {i : Inert c}
    → ⟪ i ⟫⊑ A′
      --------------------
    → (A ⊑ A′) × (B ⊑ A′)
  lpit→⊑ (lpit-inj g lp) = [ lp , unk⊑ ]
  lpit→⊑ (lpit-fun lp1 lp2) = [ lp1 , lp2 ]

  lpti→⊑ : ∀ {A A′ B′} {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
    → A ⊑⟪ i′ ⟫
      --------------------
    → (A ⊑ A′) × (A ⊑ B′)
  lpti→⊑ (lpti-fun lp1 lp2) = [ lp1 , lp2 ]


  {-

   We take the first step of instantiating the reduction semantics of
   the Parametric Cast Calculus by applying the ParamCastAux module.

   -}
  open import PreCastStructure
  open import PreCastStructureWithPrecision

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
  -- applyCast M v (cast (A₁ `× A₂) (B₁ `× B₂) ℓ c') {A-pair _}
  --     with ~-relevant c'
  -- ... | pair~ c d =
  --   cons (fst M ⟨ cast A₁ B₁ ℓ c ⟩) (snd M ⟨ cast A₂ B₂ ℓ d ⟩)
  applyCast (cons V W) (V-pair v w) (cast (A₁ `× A₂) (B₁ `× B₂) ℓ c~)
    with ~-relevant c~
  ... | pair~ c d = cons (V ⟨ cast A₁ B₁ ℓ c ⟩) (W ⟨ cast A₂ B₂ ℓ d ⟩)
  -- applyCast M v (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ c') {A-sum _}
  --     with ~-relevant c'
  -- ... | sum~ c d =
  --   let l = inl ((` Z) ⟨ cast A₁ B₁ ℓ c ⟩) in
  --   let r = inr ((` Z) ⟨ cast A₂ B₂ ℓ d ⟩) in
  --   case M l r
  applyCast (inl V) v (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ c~) {A-sum _}
    with ~-relevant c~
  ... | sum~ c d = inl (V ⟨ cast A₁ B₁ ℓ c ⟩)
  applyCast (inr W) w (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ c~) {A-sum _}
    with ~-relevant c~
  ... | sum~ c d = inr (W ⟨ cast A₂ B₂ ℓ d ⟩)

  applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → Safe c ℓ
    → CastsAllSafe V ℓ
      --------------------------------------
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe (A-id _) safe allsafe = allsafe
  applyCast-pres-allsafe (A-inj (cast ⋆ .⋆ _ _) _ ⋆≢⋆) (safe-<: <:-⋆) allsafe = contradiction refl ⋆≢⋆
  applyCast-pres-allsafe (A-inj (cast A .⋆ ℓ _) ¬gA A≢⋆) (safe-<: {c~ = c~} (<:-G A<:G gG)) allsafe with A | gG | ground A {A≢⋆}
  ... | ` ι | G-Base | [ ` ι  , [ G-Base , base~ ] ] =
    allsafe-cast (safe-<: {c~ = c~} (<:-G A<:G gG)) (allsafe-cast (safe-<: {c~ = base~} <:-B) allsafe)
  ... | (A₁ ⇒ A₂) | G-Fun | [ ⋆ ⇒ ⋆ , [ G-Fun , _ ] ] =
    allsafe-cast (safe-<: {c~ = unk~R} (<:-G (<:-⇒ <:-⋆ <:-⋆) gG)) (allsafe-cast (safe-<: {c~ = fun~ unk~L unk~R} A<:G) allsafe)
  ... | (A₁ `× A₂) | G-Pair | [ ⋆ `× ⋆ , [ G-Pair , _ ] ] =
    allsafe-cast (safe-<: {c~ = unk~R} (<:-G (<:-× <:-⋆ <:-⋆) gG)) (allsafe-cast (safe-<: {c~ = pair~ unk~R unk~R} A<:G) allsafe)
  ... | (A₁ `⊎ A₂) | G-Sum | [ ⋆ `⊎ ⋆ , [ G-Sum , _ ] ] =
    allsafe-cast (safe-<: {c~ = unk~R} (<:-G (<:-⊎ <:-⋆ <:-⋆) gG)) (allsafe-cast (safe-<: {c~ = sum~ unk~R unk~R} A<:G) allsafe)
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
  applyCast-pres-allsafe {V = cons V W} {V-pair v w} (A-pair (cast (_ `× _) (_ `× _) ℓ c~))
                         (safe-<: (<:-× sub-fst sub-snd)) (allsafe-cons allsafe-V allsafe-W)
    with ~-relevant c~
  ... | pair~ c~fst c~snd = allsafe-cons (allsafe-cast (safe-<: {c~ = c~fst} sub-fst) allsafe-V)
                                         (allsafe-cast (safe-<: {c~ = c~snd} sub-snd) allsafe-W)
  applyCast-pres-allsafe {V = cons V W} {V-pair v w} (A-pair (cast (_ `× _) (_ `× _) ℓ′ c~))
                         (safe-ℓ≢ ℓ≢) (allsafe-cons allsafe-V allsafe-W)
    with ~-relevant c~
  ... | pair~ c~fst c~snd = allsafe-cons (allsafe-cast (safe-ℓ≢ {c~ = c~fst} ℓ≢) allsafe-V)
                                         (allsafe-cast (safe-ℓ≢ {c~ = c~snd} ℓ≢) allsafe-W)
  applyCast-pres-allsafe {V = inl V} {V-inl v} (A-sum (cast (_ `⊎ _) (_ `⊎ _) ℓ c~)) (safe-<: (<:-⊎ sub-l sub-r)) (allsafe-inl allsafe)
    with ~-relevant c~
  ... | sum~ c~l c~r = allsafe-inl (allsafe-cast (safe-<: {c~ = c~l} sub-l) allsafe)
  applyCast-pres-allsafe {V = inr W} {V-inr w} (A-sum (cast (_ `⊎ _) (_ `⊎ _) ℓ c~)) (safe-<: (<:-⊎ sub-l sub-r)) (allsafe-inr allsafe)
    with ~-relevant c~
  ... | sum~ c~l c~r = allsafe-inr (allsafe-cast (safe-<: {c~ = c~r} sub-r) allsafe)
  applyCast-pres-allsafe {V = inl V} {V-inl v} (A-sum (cast (_ `⊎ _) (_ `⊎ _) ℓ′ c~)) (safe-ℓ≢ ℓ≢) (allsafe-inl allsafe)
    with ~-relevant c~
  ... | sum~ c~l c~r = allsafe-inl (allsafe-cast (safe-ℓ≢ {c~ = c~l} ℓ≢) allsafe)
  applyCast-pres-allsafe {V = inr W} {V-inr w} (A-sum (cast (_ `⊎ _) (_ `⊎ _) ℓ′ c~)) (safe-ℓ≢ ℓ≢) (allsafe-inr allsafe)
    with ~-relevant c~
  ... | sum~ c~l c~r = allsafe-inr (allsafe-cast (safe-ℓ≢ {c~ = c~r} ℓ≢) allsafe)

  {- A few lemmas to prove `catchup`. -}

  open import CastStructure
  open import CastStructureWithPrecision

  cs : CastStruct
  cs = record {
          applyCast = applyCast;
          applyCast-pres-allsafe = applyCast-pres-allsafe
        }

  {-

  We now instantiate the module ParamCastReduction, thereby proving
  type safety for λB.

  -}

  import ParamCastReduction
  module Red = ParamCastReduction cs
  open Red

  import GTLC2CC
  open GTLC2CC Cast Inert (λ A B ℓ {c} → cast A B ℓ c) public

  -- Instantiate the proof of "compilation from GTLC to CC preserves precision".
  open import CompilePresPrec pcsp
  open CompilePresPrecProof (λ A B ℓ {c} → cast A B ℓ c)
    using (compile-pres-prec) public

  -- Instantiate blame-subtyping theorem for `GroundCast`.
  open import ParamBlameSubtyping cs using (soundness-<:) public


  {- A few lemmas to prove `catchup`. -}
  open import ParamCCPrecision pcsp
  open import ParamGradualGuaranteeAux pcsp

  applyCast-catchup : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
    → (a : Active c)
    → (vV : Value V) → Value V′
    → A ⊑ A′ → B ⊑ A′
    → Γ , Γ′ ⊢ V ⊑ᶜ V′
      ----------------------------------------------------------
    → ∃[ W ] ((Value W) × (applyCast V vV c {a} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))

  private
    wrapV-⊑-inv : ∀ {Γ Γ′ A A′} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ ⋆)}
      → Value V → Value V′ → (i : Inert c) → A′ ≢ ⋆
      → Γ , Γ′ ⊢ V ⟪ i ⟫ ⊑ᶜ V′
        ------------------------
      → Γ , Γ′ ⊢ V ⊑ᶜ V′
    wrapV-⊑-inv v v' (I-inj g c) nd (⊑ᶜ-wrap (lpii-inj .g) lpVi) = contradiction refl nd
    wrapV-⊑-inv v v' i nd (⊑ᶜ-wrapl x lpVi) = lpVi

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
    applyCast-proj-ng-catchup {B = ⋆} nd ng v v′ lp lpV = contradiction refl nd
    applyCast-proj-ng-catchup {B = ` B₁} nd ng v v′ lp lpV = contradiction G-Base ng
    applyCast-proj-ng-catchup {B = B₁ ⇒ B₂} {c = cast .⋆ .(B₁ ⇒ B₂) ℓ _} nd ng v v′ lp lpV
      with ground? (B₁ ⇒ B₂)
    ... | yes b-g = contradiction b-g ng
    ... | no b-ng
      with ground (B₁ ⇒ B₂) {nd}
    ...   | [ ⋆ ⇒ ⋆ , [ G-Fun , c~ ] ]
      with applyCast-proj-g-catchup {c = cast ⋆ (⋆ ⇒ ⋆) ℓ unk~L} (ground-nd G-Fun) G-Fun v v′ (⊑-ground-relax G-Fun lp c~ nd) lpV
    ...     | [ W , [ vW , [ rd* , lpW ] ] ] =
      -- The 1st cast ⋆ ⇒ ⋆ → ⋆ is an active projection
      let a = A-proj (cast ⋆ (⋆ ⇒ ⋆) ℓ unk~L) (ground-nd G-Fun)
      -- The 2nd cast ⋆ → ⋆ ⇒ B₁ → B₂ is an inert function cast
          i = I-fun _ in
        [ W ⟪ i ⟫ ,
          [ V-wrap vW i ,
            [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {a} ⟩ rd*)) (_ —→⟨ wrap vW {i} ⟩ _ ∎) ,
              ⊑ᶜ-wrapl (⊑→lpit i (⊑-ground-relax G-Fun lp c~ nd) lp) lpW ] ] ]
    applyCast-proj-ng-catchup {B = B₁ `× B₂} {c = cast .⋆ .(B₁ `× B₂) ℓ _} nd ng v v′ lp lpV
      with ground? (B₁ `× B₂)
    ... | yes b-g = contradiction b-g ng
    ... | no b-ng
      with ground (B₁ `× B₂) {nd}
    ...   | [ ⋆ `× ⋆ , [ G-Pair , c~ ] ]
      with applyCast-proj-g-catchup {c = cast ⋆ (⋆ `× ⋆) ℓ unk~L} (ground-nd G-Pair) G-Pair v v′ (⊑-ground-relax G-Pair lp c~ nd) lpV
    ...     | [ cons W₁ W₂ , [ V-pair w₁ w₂ , [ rd* , lpW ] ] ]
      with lp | v′ | lpW
    ...       | pair⊑ lp₁ lp₂ | V-pair v′₁ v′₂ | ⊑ᶜ-cons lpW₁ lpW₂
      with applyCast-catchup {c = cast ⋆ B₁ ℓ unk~L} (from-dyn-active B₁) w₁ v′₁ unk⊑ lp₁ lpW₁
         | applyCast-catchup {c = cast ⋆ B₂ ℓ unk~L} (from-dyn-active B₂) w₂ v′₂ unk⊑ lp₂ lpW₂
    ...         | [ V₁ , [ v₁ , [ rd*₁ , lpV₁ ] ] ] | [ V₂ , [ v₂ , [ rd*₂ , lpV₂ ] ] ] =
      [ cons V₁ V₂ ,
        [ V-pair v₁ v₂ ,
          {- Here we need to prove V ⟨ ⋆ ⇒ ⋆ × ⋆ ⟩ ⟨ ⋆ × ⋆ ⇒ B₁ × B₂ ⟩ —↠ cons V₁ V₂ -}
          [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {A-proj _ (λ ())} ⟩ rd*))
                     {- cons W₁ W₂ ⟨ ⋆ × ⋆ ⇒ B₁ × B₂ ⟩ —↠ cons V₁ V₂ -}
                     (
                       -- cons W₁ W₂ ⟨ ⋆ × ⋆ ⇒ B₁ × B₂ ⟩
                       _ —→⟨ cast (V-pair w₁ w₂) {A-pair _} ⟩
                       -- -- cons (fst (cons W₁ W₂) ⟨ ⋆ ⇒ B₁ ⟩) (snd (cons W₁ W₂) ⟨ ⋆ ⇒ B₂ ⟩)
                       -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst w₁ w₂)) ⟩
                       -- -- cons (W₁ ⟨ ⋆ ⇒ B₁ ⟩) (snd (cons W₁ W₂) ⟨ ⋆ ⇒ B₂ ⟩)
                       -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd w₁ w₂)) ⟩
                       -- cons (W₁ ⟨ ⋆ ⇒ B₁ ⟩) (W₂ ⟨ ⋆ ⇒ B₂ ⟩)
                       _ —→⟨ ξ {F = F-×₂ _} (cast w₁ {from-dyn-active B₁}) ⟩
                       _ —→⟨ ξ {F = F-×₁ _} (cast w₂ {from-dyn-active B₂}) ⟩
                       -- cons V₁ V₂
                       ↠-trans (plug-cong (F-×₂ _) rd*₁) (plug-cong (F-×₁ _) rd*₂)
                     ) ,
            ⊑ᶜ-cons lpV₁ lpV₂ ] ] ]
    applyCast-proj-ng-catchup {B = B₁ `⊎ B₂} {c = cast .⋆ .(B₁ `⊎ B₂) ℓ _} nd ng v v′ lp lpV
      with ground? (B₁ `⊎ B₂)
    ... | yes b-g = contradiction b-g ng
    ... | no b-ng
      with ground (B₁ `⊎ B₂) {nd}
    ...   | [ ⋆ `⊎ ⋆ , [ G-Sum , c~ ] ]
      with applyCast-proj-g-catchup {c = cast ⋆ (⋆ `⊎ ⋆) ℓ unk~L} (ground-nd G-Sum) G-Sum v v′
                                                                  (⊑-ground-relax G-Sum lp c~ nd) lpV
    ...     | [ inl W , [ V-inl w , [ rd* , lpW ] ] ]
      with lp | v′ | lpW
    ...       | sum⊑ lp₁ lp₂ | V-inl v′₁ | ⊑ᶜ-inl unk⊑ lpW₁
      with applyCast-catchup {c = cast ⋆ B₁ ℓ unk~L} (from-dyn-active B₁) w v′₁ unk⊑ lp₁ lpW₁
    ...         | [ V₁ , [ v₁ , [ rd*₁ , lpV₁ ] ] ] =
      [ inl V₁ ,
        [ V-inl v₁ ,
          {- Here we need to prove V ⟨ ⋆ ⇒ ⋆ ⊎ ⋆ ⟩ ⟨ ⋆ ⊎ ⋆ ⇒ B₁ × B₂ ⟩ —↠ inl V₁ -}
          [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {A-proj _ (λ ())} ⟩ rd*))
                     {- inl W ⟨ ⋆ ⊎ ⋆ ⇒ B₁ ⊎ B₂ ⟩ —↠ inl V₁ -}
                     (
                       -- inl W ⟨ ⋆ ⊎ ⋆ ⇒ B₁ ⊎ B₂ ⟩
                       _ —→⟨ cast (V-inl w) {A-sum _} ⟩
                       -- case (inl W) (inl ((` Z) ⟨ cast ⋆ B₁ ℓ c ⟩)) (inr ((` Z) ⟨ cast ⋆ B₂ ℓ d ⟩))
                       -- _ —→⟨ β-caseL w ⟩
                       -- (inl (` Z ⟨ ⋆ ⇒ B₂ ⟩)) [ W ] ≡ inl (W ⟨ ⋆ ⇒ B₂ ⟩)
                       _ —→⟨ ξ (cast w {from-dyn-active B₁} ) ⟩
                       plug-cong F-inl rd*₁
                       -- inl V₁
                     ),
            ⊑ᶜ-inl lp₂ lpV₁ ] ] ]
    applyCast-proj-ng-catchup {B = B₁ `⊎ B₂} {c = cast .⋆ .(B₁ `⊎ B₂) ℓ _} nd ng v v′ lp lpV
                              | no b-ng | [ ⋆ `⊎ ⋆ , [ G-Sum , c~ ] ] | [ inr W , [ V-inr w , [ rd* , lpW ] ] ]
      with lp | v′ | lpW
    ...       | sum⊑ lp₁ lp₂ | V-inr v′₂ | ⊑ᶜ-inr unk⊑ lpW₂
      with applyCast-catchup {c = cast ⋆ B₂ ℓ unk~L} (from-dyn-active B₂) w v′₂ unk⊑ lp₂ lpW₂
    ...         | [ V₂ , [ v₂ , [ rd*₂ , lpV₂ ] ] ] =
      [ inr V₂ ,
        [ V-inr v₂ ,
          {- Here we need to prove V ⟨ ⋆ ⇒ ⋆ ⊎ ⋆ ⟩ ⟨ ⋆ ⊎ ⋆ ⇒ B₁ × B₂ ⟩ —↠ inr V₂ -}
          [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {A-proj _ (λ ())} ⟩ rd*))
                     {- inr W ⟨ ⋆ ⊎ ⋆ ⇒ B₁ ⊎ B₂ ⟩ —↠ inr V₂ -}
                     (
                       -- inr W ⟨ ⋆ ⊎ ⋆ ⇒ B₁ ⊎ B₂ ⟩
                       _ —→⟨ cast (V-inr w) {A-sum _} ⟩
                       -- case (inr W) (inl ((` Z) ⟨ cast ⋆ B₁ ℓ c ⟩)) (inr ((` Z) ⟨ cast ⋆ B₂ ℓ d ⟩))
                       -- _ —→⟨ β-caseR w ⟩
                       -- (inr (` Z ⟨ ⋆ ⇒ B₂ ⟩)) [ W ] ≡ inr (W ⟨ ⋆ ⇒ B₂ ⟩)
                       _ —→⟨ ξ (cast w {from-dyn-active B₂} ) ⟩
                       plug-cong F-inr rd*₂
                       -- inr V₂
                     ),
            ⊑ᶜ-inr lp₁ lpV₂ ] ] ]

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


  private
    -- We reason about `~-relevant` in a seperate lemma
    applyCast-reduction-pair : ∀ {Γ A B C D} {V : Γ ⊢ A} {W : Γ ⊢ B} {ℓ}
      → (c~ : A `× B ~ C `× D)
      → (v : Value V) → (w : Value W)
      → ∃[ c~1 ] ∃[ c~2 ]
           (applyCast (cons V W) (V-pair v w) (cast (A `× B) (C `× D) ℓ c~) {A-pair _}
              —↠
            cons (V ⟨ cast A C ℓ c~1 ⟩) (W ⟨ cast B D ℓ c~2 ⟩))
    applyCast-reduction-pair c~ v w with ~-relevant c~
    ... | pair~ c~1 c~2 = [ c~1 , [ c~2 , _ ∎ ] ]

    applyCast-reduction-inj : ∀ {Γ A} {V : Γ ⊢ A} {ℓ}
      → (v : Value V)
      → (ng : ¬ Ground A) → (nd : A ≢ ⋆)
      → ∃[ G ] ∃[ c~ ] (applyCast V v (cast A ⋆ ℓ unk~R) {A-inj _ ng nd} —↠ (V ⟨ cast A G ℓ c~ ⟩) ⟨ cast G ⋆ ℓ unk~R ⟩)
    applyCast-reduction-inj {A = A} v ng nd
      with ground A {nd}
    ... | [ G , [ _ , c~ ] ] = [ G , [ c~ , _ ∎ ] ]

    applyCast-reduction-sum-left : ∀ {Γ A B C D} {V : Γ ⊢ A} {ℓ}
      → (c~ : A `⊎ B ~ C `⊎ D)
      → (v : Value V)
      → ∃[ c~1 ]
           (applyCast (inl V) (V-inl v) (cast (A `⊎ B) (C `⊎ D) ℓ c~) {A-sum _}
              —↠
            inl (V ⟨ cast A C ℓ c~1 ⟩))
    applyCast-reduction-sum-left c~ v with ~-relevant c~
    ... | sum~ c~1 c~2 = [ c~1 , _ ∎ ]

    applyCast-reduction-sum-right : ∀ {Γ A B C D} {V : Γ ⊢ B} {ℓ}
      → (c~ : A `⊎ B ~ C `⊎ D)
      → (v : Value V)
      → ∃[ c~2 ]
           (applyCast (inr V) (V-inr v) (cast (A `⊎ B) (C `⊎ D) ℓ c~) {A-sum _}
              —↠
            inr (V ⟨ cast B D ℓ c~2 ⟩))
    applyCast-reduction-sum-right c~ v with ~-relevant c~
    ... | sum~ c~1 c~2 = [ c~2 , _ ∎ ]

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
  ...   | G-Fun | unk~L | _ = contradiction refl a-nd
  ...   | G-Fun | fun~ c~₁ c~₂ | fun⊑ lp11 lp12 =
    let i₁ = I-fun (cast A G ℓ (fun~ c~₁ c~₂))
        i₂ = I-inj g (cast G ⋆ ℓ unk~R) in
      [ V ⟪ i₁ ⟫ ⟪ i₂ ⟫ , [ V-wrap (V-wrap vV i₁) i₂ ,
        [ _ —→⟨ ξ (wrap vV {i₁}) ⟩ _ —→⟨ wrap (V-wrap vV i₁) {i₂} ⟩ _ ∎ ,
          ⊑ᶜ-wrapl (lpit-inj g (⊑-ground-relax g lp1 c~ a-nd)) (⊑ᶜ-wrapl (lpit-fun lp1 ground-fun-⊑) lpV) ] ] ]
  ...   | G-Pair | unk~L | _ = contradiction refl a-nd
  ...   | G-Pair | pair~ c~₁ c~₂ | pair⊑ lp11 lp12
    with vV | vV′ | lpV
  ...     | V-pair {A = A₁} {B₁} {V₁} {V₂} v₁ v₂ | V-pair {V = V₁′} {W = V₂′} v₁′ v₂′ | ⊑ᶜ-cons lpV₁ lpV₂
    {- Need to prove:
      cons V₁ V₂ ⟨ A × B ⇒ ⋆ × ⋆ ⟩ ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩ —↠
      cons (V₁ ⟨ A ⇒ ⋆ ⟩) (V₂ ⟨ B ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
      Note that A ⇒ ⋆ can be either active, such as A-id or A-inj , or inert, such as I-inj , depending on A.
    -}
    with ActiveOrInert (cast A₁ ⋆ ℓ unk~R) | ActiveOrInert (cast B₁ ⋆ ℓ unk~R)
  ...       | inj₁ a₁ | inj₁ a₂ =
      let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ v₁ v₁′ lp11 unk⊑ lpV₁
          [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ v₂ v₂′ lp12 unk⊑ lpV₂ in
        [ cons W₁ W₂ ⟪ I-inj g (cast (⋆ `× ⋆) ⋆ ℓ unk~R) ⟫ ,
          [ V-wrap (V-pair w₁ w₂) _ ,
            [ _ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _})⟩
              ↠-trans (plug-cong (F-cast _) (proj₂ (proj₂ (applyCast-reduction-pair c~ v₁ v₂))))
                       -- cons (V₁ ⟨ A₁ ⇒ ⋆ ⟩) (V₂ ⟨ B₁ ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
                       (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₂ _} (cast v₁ {a₁})) ⟩
                        _ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₁ _} (cast v₂ {a₂})) ⟩
                        ↠-trans (plug-cong (F-cast _) (plug-cong (F-×₂ _) rd*₁))
                                 (↠-trans (plug-cong (F-cast _) (plug-cong (F-×₁ _) rd*₂)) (_ —→⟨ wrap (V-pair w₁ w₂) ⟩ _ ∎))) ,
              ⊑ᶜ-wrapl (lpit-inj _ (pair⊑ unk⊑ unk⊑)) (⊑ᶜ-cons lpW₁ lpW₂) ] ] ]
  ...       | inj₂ i₁ | inj₁ a₂ =
    let [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ v₂ v₂′ lp12 unk⊑ lpV₂ in
      [ cons (V₁ ⟪ i₁ ⟫) W₂ ⟪ I-inj g (cast (⋆ `× ⋆) ⋆ ℓ unk~R) ⟫ ,
        [ V-wrap (V-pair (V-wrap v₁ i₁) w₂) _ ,
          [ _ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _})⟩
              ↠-trans (plug-cong (F-cast _) (proj₂ (proj₂ (applyCast-reduction-pair c~ v₁ v₂))))
                       -- cons (V₁ ⟨ A₁ ⇒ ⋆ ⟩) (V₂ ⟨ B₁ ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
                       (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₂ _} (wrap v₁ {i₁})) ⟩
                        _ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₁ _} (cast v₂ {a₂})) ⟩
                        ↠-trans (plug-cong (F-cast _) (plug-cong (F-×₁ _) rd*₂))
                                 (_ —→⟨ wrap (V-pair (V-wrap v₁ i₁) w₂) ⟩ _ ∎)) ,
            ⊑ᶜ-wrapl (⊑→lpit _ (pair⊑ unk⊑ unk⊑) lp2) (⊑ᶜ-cons (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 unk⊑) lpV₁) lpW₂) ] ] ]
  ...       | inj₁ a₁ | inj₂ i₂ =
    let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ v₁ v₁′ lp11 unk⊑ lpV₁ in
      [ cons W₁ (V₂ ⟪ i₂ ⟫) ⟪ I-inj g (cast (⋆ `× ⋆) ⋆ ℓ unk~R) ⟫ ,
        [ V-wrap (V-pair w₁ (V-wrap v₂ i₂)) _ ,
          [ _ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _})⟩
              ↠-trans (plug-cong (F-cast _) (proj₂ (proj₂ (applyCast-reduction-pair c~ v₁ v₂))))
                       -- cons (V₁ ⟨ A₁ ⇒ ⋆ ⟩) (V₂ ⟨ B₁ ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
                       (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₂ _} (cast v₁ {a₁})) ⟩
                        _ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₁ _} (wrap v₂ {i₂})) ⟩
                        ↠-trans (plug-cong (F-cast _) (plug-cong (F-×₂ _) rd*₁))
                                 (_ —→⟨ wrap (V-pair w₁ (V-wrap v₂ i₂)) ⟩ _ ∎)) ,
            ⊑ᶜ-wrapl (⊑→lpit _ (pair⊑ unk⊑ unk⊑) lp2) (⊑ᶜ-cons lpW₁ (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 unk⊑) lpV₂)) ] ] ]
  ...       | inj₂ i₁ | inj₂ i₂ =
        [ cons (V₁ ⟪ i₁ ⟫) (V₂ ⟪ i₂ ⟫) ⟪ I-inj g (cast (⋆ `× ⋆) ⋆ ℓ unk~R) ⟫ ,
          [ V-wrap (V-pair (V-wrap v₁ _) (V-wrap v₂ _)) _ ,
            [ _ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _})⟩
              ↠-trans (plug-cong (F-cast _) (proj₂ (proj₂ (applyCast-reduction-pair c~ v₁ v₂))))
                       -- cons (V₁ ⟨ A₁ ⇒ ⋆ ⟩) (V₂ ⟨ B₁ ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
                       (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₂ _} (wrap v₁ {i₁})) ⟩
                        _ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₁ _} (wrap v₂ {i₂})) ⟩
                        _ —→⟨ wrap (V-pair (V-wrap v₁ i₁) (V-wrap v₂ i₂)) ⟩
                        _ ∎) ,
              ⊑ᶜ-wrapl (lpit-inj _ (pair⊑ unk⊑ unk⊑)) (⊑ᶜ-cons (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 unk⊑) lpV₁)
                                                               (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 unk⊑) lpV₂)) ] ] ]

  applyCast-catchup {V = V} {c = cast A ⋆ ℓ _} (A-inj c a-ng a-nd) vV vV′ lp1 lp2 lpV
    | [ G , [ g , c~ ] ] | G-Sum | unk~L | _ =
    contradiction refl a-nd
  applyCast-catchup {V = V} {c = cast (A₁ `⊎ B₁) ⋆ ℓ _} (A-inj c a-ng a-nd) (V-inl {V = W} w) (V-inl {V = W′} w′) lp1 lp2 (⊑ᶜ-inl lpB lpW)
    | [ G , [ g , c~ ] ] | G-Sum | sum~ c~₁ c~₂ | sum⊑ lp11 lp12
    {-       (inl W ⟨ A ⊎ B ⇒ ⋆ ⊎ ⋆ ⟩) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        —↠ (case (inl W) (inl (` Z ⟨ A ⇒ ⋆ ⟩)) (inr (` Z ⟨ B ⇒ ⋆ ⟩))) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        —↠ ((inl (` Z ⟨ A ⇒ ⋆ ⟩)) [ W ]) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        —↠ inl (W ⟨ A ⇒ ⋆ ⟩) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        At this point we need to case on whether A ⇒ ⋆ is active or inert. If active, goes to:
        —↠ inl W₁ ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        Otherwise if inert, goes to:
        —↠ inl (W ⟨ A ⇒ ⋆ ⟩) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
    -}
    with ActiveOrInert (cast A₁ ⋆ ℓ unk~R)
  ... | inj₁ a₁ =
    let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ w w′ lp11 unk⊑ lpW in
      [ inl W₁ ⟪ I-inj G-Sum (cast (⋆ `⊎ ⋆) ⋆ ℓ unk~R) ⟫ ,
        [ V-wrap (V-inl w₁) (I-inj G-Sum _) ,
          [ _ —→⟨ ξ {F = F-cast _} (cast (V-inl w) {A-sum _}) ⟩
            ↠-trans (plug-cong (F-cast _) (proj₂ (applyCast-reduction-sum-left c~ w)))
                     (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-inl} (cast w {a₁})) ⟩
                      ↠-trans (plug-cong (F-cast _) (plug-cong F-inl rd*₁))
                               (_ —→⟨ wrap (V-inl w₁) {I-inj G-Sum _} ⟩ _ ∎)) ,
            ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) lp2) (⊑ᶜ-inl unk⊑ lpW₁) ] ] ]
  ... | inj₂ i₁ =
    [ inl (W ⟪ i₁ ⟫) ⟪ I-inj G-Sum (cast (⋆ `⊎ ⋆) ⋆ ℓ unk~R) ⟫ ,
      [ V-wrap (V-inl (V-wrap w i₁)) (I-inj G-Sum _) ,
        [ _ —→⟨ ξ {F = F-cast _} (cast (V-inl w) {A-sum _}) ⟩
          ↠-trans (plug-cong (F-cast _) (proj₂ (applyCast-reduction-sum-left c~ w)))
                   (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-inl} (wrap w {i₁})) ⟩
                    _ —→⟨ wrap (V-inl (V-wrap w i₁)) {I-inj G-Sum _} ⟩
                    _ ∎) ,
          ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) unk⊑)
                   (⊑ᶜ-inl unk⊑ (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 unk⊑) lpW)) ] ] ]
  applyCast-catchup {A = A} {V = V} {c = cast (A₁ `⊎ B₁) ⋆ ℓ _} (A-inj c a-ng a-nd) (V-inr {V = W} w) (V-inr {V = W′} w′) lp1 lp2 (⊑ᶜ-inr lpA lpW)
    | [ G , [ g , c~ ] ] | G-Sum | sum~ c~₁ c~₂ | sum⊑ lp11 lp12
    with ActiveOrInert (cast B₁ ⋆ ℓ unk~R)
  ... | inj₁ a₂ =
    let [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ w w′ lp12 unk⊑ lpW in
      [ inr W₂ ⟪ I-inj G-Sum (cast (⋆ `⊎ ⋆) ⋆ ℓ unk~R) ⟫ ,
        [ V-wrap (V-inr w₂) (I-inj G-Sum _) ,
          [ _ —→⟨ ξ {F = F-cast _} (cast (V-inr w) {A-sum _}) ⟩
            ↠-trans (plug-cong (F-cast _) (proj₂ (applyCast-reduction-sum-right c~ w)))
                     (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-inr} (cast w {a₂})) ⟩
                      ↠-trans (plug-cong (F-cast _) (plug-cong F-inr rd*₂))
                               (_ —→⟨ wrap (V-inr w₂) {I-inj G-Sum _} ⟩ _ ∎)) ,
            ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) lp2) (⊑ᶜ-inr unk⊑ lpW₂) ] ] ]
  ... | inj₂ i₂ =
    [ inr (W ⟪ i₂ ⟫) ⟪ I-inj G-Sum (cast (⋆ `⊎ ⋆) ⋆ ℓ unk~R) ⟫ ,
      [ V-wrap (V-inr (V-wrap w i₂)) (I-inj G-Sum _) ,
        [ _ —→⟨ ξ {F = F-cast _} (cast (V-inr w) {A-sum _}) ⟩
          ↠-trans (plug-cong (F-cast _) (proj₂ (applyCast-reduction-sum-right c~ w)))
                   (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-inr} (wrap w {i₂})) ⟩
                    _ —→⟨ wrap (V-inr (V-wrap w i₂)) {I-inj G-Sum _} ⟩
                    _ ∎) ,
          ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) unk⊑)
                   (⊑ᶜ-inr unk⊑ (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 unk⊑) lpW)) ] ] ]


  applyCast-catchup (A-proj c b-nd) vV vV′ lp1 lp2 lpV = applyCast-proj-catchup {c = c} b-nd vV vV′ lp2 lpV
  applyCast-catchup {V = cons V W} (A-pair (cast (A `× B) (C `× D) ℓ c~)) (V-pair v w) (V-pair v′ w′) (pair⊑ lp11 lp12) (pair⊑ lp21 lp22) (⊑ᶜ-cons lpV lpW)
    with ~-relevant c~
  ... | pair~ c~1 c~2
    with ActiveOrInert (cast A C ℓ c~1) | ActiveOrInert (cast B D ℓ c~2)
  ...   | inj₁ a₁ | inj₁ a₂ =
    let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ v v′ lp11 lp21 lpV
        [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ w w′ lp12 lp22 lpW in
      [ cons W₁ W₂ ,
        [ V-pair w₁ w₂ ,
          [
            -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst v w)) ⟩
            -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd v w)) ⟩
            _ —→⟨ ξ {F = F-×₂ _} (cast v {a₁}) ⟩
            _ —→⟨ ξ {F = F-×₁ _} (cast w {a₂}) ⟩
            ↠-trans (plug-cong (F-×₂ _) rd*₁)
                     (↠-trans (plug-cong (F-×₁ _) rd*₂) (_ ∎)) ,
            ⊑ᶜ-cons lpW₁ lpW₂ ] ] ]
  ...   | inj₁ a₁ | inj₂ i₂ =
    let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ v v′ lp11 lp21 lpV in
      [ cons W₁ (W ⟪ i₂ ⟫) ,
        [ V-pair w₁ (V-wrap w i₂) ,
          [
            -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst v w)) ⟩
            -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd v w)) ⟩
            _ —→⟨ ξ {F = F-×₂ _} (cast v {a₁}) ⟩
            _ —→⟨ ξ {F = F-×₁ _} (wrap w {i₂}) ⟩
            (plug-cong (F-×₂ _) rd*₁) ,
            ⊑ᶜ-cons lpW₁ (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 lp22) lpW) ] ] ]
  ...   | inj₂ i₁ | inj₁ a₂ =
    let [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ w w′ lp12 lp22 lpW in
      [ cons (V ⟪ i₁ ⟫) W₂ ,
        [ V-pair (V-wrap v i₁) w₂ ,
          [
            -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst v w)) ⟩
            -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd v w)) ⟩
            _ —→⟨ ξ {F = F-×₂ _} (wrap v {i₁}) ⟩
            _ —→⟨ ξ {F = F-×₁ _} (cast w {a₂}) ⟩
            (plug-cong (F-×₁ _) rd*₂) ,
            ⊑ᶜ-cons (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 lp21) lpV) lpW₂ ] ] ]
  ...   | inj₂ i₁ | inj₂ i₂ =
    [ cons (V ⟪ i₁ ⟫) (W ⟪ i₂ ⟫) ,
      [ V-pair (V-wrap v i₁) (V-wrap w i₂) ,
        [
          -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst v w)) ⟩
          -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd v w)) ⟩
          _ —→⟨ ξ {F = F-×₂ _} (wrap v {i₁}) ⟩
          _ —→⟨ ξ {F = F-×₁ _} (wrap w {i₂}) ⟩
          _ ∎ ,
          ⊑ᶜ-cons (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 lp21) lpV) (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 lp22) lpW) ] ] ]
  applyCast-catchup {V = inl V} (A-sum (cast (A `⊎ B) (C `⊎ D) ℓ c~)) (V-inl v) (V-inl v′) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inl lpB lpV)
    with ~-relevant c~
  ... | sum~ c~1 c~2
    with ActiveOrInert (cast A C ℓ c~1)
  ...   | inj₁ a₁ =
    let [ W , [ w , [ rd* , lpW ] ] ] = applyCast-catchup a₁ v v′ lp11 lp21 lpV in
      [ inl W ,
        [ V-inl w ,
          [ -- _ —→⟨ β-caseL v ⟩
            _ —→⟨ ξ {F = F-inl} (cast v {a₁}) ⟩
            plug-cong F-inl rd* ,
            ⊑ᶜ-inl lp22 lpW ] ] ]
  ...   | inj₂ i₁ =
    [ inl (V ⟪ i₁ ⟫) ,
      [ V-inl (V-wrap v i₁) ,
        [ -- _ —→⟨ β-caseL v ⟩
          _ —→⟨ ξ {F = F-inl} (wrap v {i₁}) ⟩
          _ ∎ ,
          ⊑ᶜ-inl lp22 (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 lp21) lpV) ] ] ]
  applyCast-catchup {V = inr V} (A-sum (cast (A `⊎ B) (C `⊎ D) ℓ c~)) (V-inr v) (V-inr v′) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inr lpA lpV)
    with ~-relevant c~
  ... | sum~ c~1 c~2
    with ActiveOrInert (cast B D ℓ c~2)
  ...   | inj₁ a₂ =
    let [ W , [ w , [ rd* , lpW ] ] ] = applyCast-catchup a₂ v v′ lp12 lp22 lpV in
      [ inr W ,
        [ V-inr w ,
          [ -- _ —→⟨ β-caseR v ⟩
            _ —→⟨ ξ {F = F-inr} (cast v {a₂}) ⟩
            plug-cong F-inr rd* ,
            ⊑ᶜ-inr lp21 lpW ] ] ]
  ...   | inj₂ i₂ =
    [ inr (V ⟪ i₂ ⟫) ,
      [ V-inr (V-wrap v i₂) ,
        [ -- _ —→⟨ β-caseR v ⟩
          _ —→⟨ ξ {F = F-inr} (wrap v {i₂}) ⟩
          _ ∎ ,
          ⊑ᶜ-inr lp21 (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 lp22) lpV) ] ] ]


  sim-wrap : ∀ {A A′ B B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → Value V → (v′ : Value V′)
    → (i′ : Inert c′)
    → A ⊑ A′ → B ⊑ B′
    → ∅ , ∅ ⊢ V ⊑ᶜ V′
      -----------------------------------------------------
    → ∃[ N ] ((V ⟨ c ⟩ —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ V′ ⟪ i′ ⟫))
  {- In this case, A is less than a ground type A′, so it can either be ⋆ or ground.
     This is the only case where the cast ⟨ ⋆ ⇒ ⋆ ⟩ is actually active! -}
  sim-wrap v v′ (Inert.I-inj g′ _) unk⊑ unk⊑ lpV =
    [ _ , [ _ —→⟨ cast v {Active.A-id {a = A-Unk} _} ⟩ _ ∎ , dyn-value-⊑-wrap v v′ (Inert.I-inj g′ _) lpV ] ]
  sim-wrap v v′ (Inert.I-inj g′ _) base⊑ unk⊑ lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj g′ _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-inj g′) lpV ] ]
  sim-wrap v v′ (Inert.I-inj G-Fun _) (fun⊑ unk⊑ unk⊑) unk⊑ lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj G-Fun _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-inj G-Fun) lpV ] ]
  sim-wrap v v′ (Inert.I-inj G-Pair _) (pair⊑ unk⊑ unk⊑) unk⊑ lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj G-Pair _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-inj G-Pair) lpV ] ]
  sim-wrap v v′ (Inert.I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) unk⊑ lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj G-Sum _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-inj G-Sum) lpV ] ]

  sim-wrap v v′ (Inert.I-fun _) unk⊑ unk⊑ lpV =
    [ _ , [ _ —→⟨ cast v {Active.A-id {a = A-Unk} _} ⟩ _ ∎ , dyn-value-⊑-wrap v v′ (Inert.I-fun _) lpV ] ]
  -- c : ⋆ ⇒ (A → B) is an active projection
  sim-wrap v v′ (Inert.I-fun _) unk⊑ (fun⊑ lp1 lp2) lpV =
    let a = Active.A-proj _ (λ ()) in
      [ _ , [ _ —→⟨ cast v {a} ⟩ _ ∎ , applyCast-⊑-wrap v v′ a (Inert.I-fun _) unk⊑ (fun⊑ lp1 lp2) lpV ] ]
  -- c : (A → B) ⇒ ⋆ can be either active or inert
  sim-wrap {c = c} v v′ (Inert.I-fun _) (fun⊑ lp1 lp2) unk⊑ lpV
    with ActiveOrInert c
  ... | inj₁ a = [ _ , [ _ —→⟨ cast v {a} ⟩ _ ∎ , applyCast-⊑-wrap v v′ a (Inert.I-fun _) (fun⊑ lp1 lp2) unk⊑ lpV ] ]
  ... | inj₂ (Inert.I-inj G-Fun _) =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj G-Fun c} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (lpit-inj G-Fun (fun⊑ unk⊑ unk⊑)) (⊑ᶜ-wrapr (lpti-fun (fun⊑ lp1 lp2) (fun⊑ unk⊑ unk⊑)) lpV) ] ]
  sim-wrap v v′ (Inert.I-fun _) (fun⊑ lp1 lp2) (fun⊑ lp3 lp4) lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-fun _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-fun (fun⊑ lp1 lp2) (fun⊑ lp3 lp4)) lpV ] ]

  sim-cast : ∀ {A A′ B B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → Value V → (v′ : Value V′)
    → (a′ : Active c′)
    → A ⊑ A′ → B ⊑ B′
    → ∅ , ∅ ⊢ V ⊑ᶜ V′
      ------------------------------------------------------------
    → ∃[ N ] ((V ⟨ c ⟩ —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ applyCast V′ v′ c′ {a′}))
  sim-cast v v′ (A-id _) lp1 lp2 lpV = [ _ , [ _ ∎ , ⊑ᶜ-castl lp1 lp2 lpV ] ]
  sim-cast v v′ (A-inj (cast A′ ⋆ _ _) ng nd) lp1 unk⊑ lpV
    with ground A′ {nd}
  ... | [ G′ , _ ] = [ _ , [ _ ∎ , ⊑ᶜ-castr unk⊑ unk⊑ (⊑ᶜ-cast lp1 unk⊑ lpV) ] ]
  sim-cast v v′ (A-proj (cast ⋆ B′ _ _) nd) unk⊑ lp2 lpV
    with ground? B′
  ... | yes b′-g
    with canonical⋆ _ v′
  ...   | [ G′ , [ W′ , [ c′ , [ i′ , meq′ ] ] ] ] rewrite meq′
    with gnd-eq? G′ B′ {inert-ground _ i′} {b′-g}
  ...     | yes ap rewrite ap = [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ lp2 (value-⊑-wrap-inv v v′ lpV) ] ]
  ...     | no  ap = [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ lp2 (⊑ᶜ-blame unk⊑) ] ]
  sim-cast v v′ (A-proj (cast ⋆ B′ _ _) nd) lp1 lp2 lpV | no b′-ng
    with ground B′ {nd}
  ...   | [ G′ , [ g′ , _ ] ] = [ _ , [ _ ∎ , ⊑ᶜ-cast unk⊑ lp2 (⊑ᶜ-castr unk⊑ unk⊑ lpV) ] ]

  sim-cast (V-wrap v i) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) unk⊑ unk⊑ (⊑ᶜ-wrapl (lpit-inj G-Pair _) (⊑ᶜ-cons lpV₁ lpV₂))
    with ~-relevant c~′
  ... | pair~ c~1′ c~2′ with v
  ...   | V-pair v₁ v₂ =
    [ _ ,
      [ _ —→⟨ cast (V-wrap v i) {A-id {a = A-Unk} _} ⟩ _ ∎ ,
        ⊑ᶜ-wrapl (⊑→lpit i (pair⊑ unk⊑ unk⊑) unk⊑) (⊑ᶜ-cons (⊑ᶜ-castr unk⊑ unk⊑ lpV₁) (⊑ᶜ-castr unk⊑ unk⊑ lpV₂)) ] ]
  sim-cast (V-wrap v i) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) unk⊑ lp2 (⊑ᶜ-wrapl (lpit-inj G-Pair _) (⊑ᶜ-cons lpV₁ lpV₂))
    with ~-relevant c~′
  ... | pair~ c~1′ c~2′ = [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ lp2 (⊑ᶜ-wrapl (⊑→lpit i ground-pair-⊑ unk⊑)
                                                                    (⊑ᶜ-cons (⊑ᶜ-castr unk⊑ unk⊑ lpV₁) (⊑ᶜ-castr unk⊑ unk⊑ lpV₂))) ] ]
  sim-cast {c = c} (V-pair v₁ v₂) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) (pair⊑ lp11 lp12) unk⊑ (⊑ᶜ-cons lpV₁ lpV₂)
    with ~-relevant c~′
  ... | pair~ c~1′ c~2′
    with ActiveOrInert c
  ...   | inj₁ a with a
  ...     | A-inj (cast (A `× B) ⋆ ℓ _) ng nd =
    let [ G , [ g~ , rd*₁ ] ] = applyCast-reduction-inj {ℓ = ℓ} (V-pair v₁ v₂) ng nd in
    let [ _ , [ _ , rd*₂ ] ] = applyCast-reduction-pair {ℓ = ℓ} g~ v₁ v₂ in
      [ _ , [ _ —→⟨ cast (V-pair v₁ v₂) {A-inj _ ng nd} ⟩
                ↠-trans rd*₁ (_ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _}) ⟩ plug-cong (F-cast _) rd*₂) ,
                ⊑ᶜ-castl ground-pair-⊑ unk⊑ (⊑ᶜ-cons (⊑ᶜ-cast lp11 unk⊑ lpV₁) (⊑ᶜ-cast lp12 unk⊑ lpV₂)) ] ]
  sim-cast {c = c} (V-pair v₁ v₂) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) (pair⊑ lp11 lp12) unk⊑ (⊑ᶜ-cons lpV₁ lpV₂)
    | pair~ _ _ | inj₂ i with i
  ...     | I-inj G-Pair .c =
    [ _ , [ _ —→⟨ wrap (V-pair v₁ v₂) {i} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (⊑→lpit i (pair⊑ unk⊑ unk⊑) unk⊑)
                     (⊑ᶜ-cons (⊑ᶜ-castr unk⊑ unk⊑ lpV₁) (⊑ᶜ-castr unk⊑ unk⊑ lpV₂)) ] ]
  sim-cast {c = c} (V-pair v₁ v₂) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) (pair⊑ lp11 lp12) (pair⊑ lp21 lp22) (⊑ᶜ-cons lpV₁ lpV₂)
    with ~-relevant c~′
  ... | pair~ c~1′ c~2′ with c
  ...   | cast (A `× B) (C `× D) ℓ c~ =
    let [ _ , [ _ , rd* ] ] = applyCast-reduction-pair (~-relevant c~) v₁ v₂ in
      [ _ , [ _ —→⟨ cast (V-pair v₁ v₂) {A-pair _} ⟩ rd* ,
              ⊑ᶜ-cons (⊑ᶜ-cast lp11 lp21 lpV₁) (⊑ᶜ-cast lp12 lp22 lpV₂) ] ]

  sim-cast (V-wrap v i) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) unk⊑ unk⊑ (⊑ᶜ-wrapl (lpit-inj G-Sum _) (⊑ᶜ-inl unk⊑ lpV))
    with ~-relevant c~′
  ... | sum~ _ _ with v
  ...   | V-inl w =
    [ _ , [ _ —→⟨ cast (V-wrap v (I-inj G-Sum _)) {A-id {a = A-Unk} _} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (⊑→lpit i ground-sum-⊑ unk⊑) (⊑ᶜ-inl unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV)) ] ]
  sim-cast (V-wrap v i) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) unk⊑ (sum⊑ lp21 lp22) (⊑ᶜ-wrapl (lpit-inj G-Sum _) (⊑ᶜ-inl lp lpV))
    with ~-relevant c~′
  ... | sum~ _ _ =
    [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ (sum⊑ lp21 lp22) (⊑ᶜ-wrapl (lpit-inj G-Sum ground-sum-⊑) (⊑ᶜ-inl unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV))) ] ]
  sim-cast {c = c} (V-inl v) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) unk⊑ (⊑ᶜ-inl lp lpV)
    with ~-relevant c~′
  ... | sum~ _ _ with ActiveOrInert c
  ...   | inj₁ a with a
  ...     | A-inj (cast (A `⊎ B) ⋆ ℓ _) ng nd =
    let [ G , [ g~ , rd*₁ ] ] = applyCast-reduction-inj {ℓ = ℓ} (V-inl v) ng nd in
    let [ _ , rd*₂ ] = applyCast-reduction-sum-left {ℓ = ℓ} (~-relevant g~) v in
      [ _ , [ _ —→⟨ cast (V-inl v) {A-inj _ ng nd} ⟩
                ↠-trans rd*₁ (_ —→⟨ ξ {F = F-cast _} (cast (V-inl v) {A-sum _}) ⟩ plug-cong (F-cast _) rd*₂) ,
                ⊑ᶜ-castl ground-sum-⊑ unk⊑ (⊑ᶜ-inl unk⊑ (⊑ᶜ-cast lp11 unk⊑ lpV)) ] ]
  sim-cast {c = c} (V-inl v) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) unk⊑ (⊑ᶜ-inl lp lpV)
    | sum~ _ _ | inj₂ i with i
  ...     | I-inj G-Sum .c =
    [ _ , [ _ —→⟨ wrap (V-inl v) {i} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (⊑→lpit i (sum⊑ unk⊑ unk⊑) unk⊑) (⊑ᶜ-inl unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV)) ] ]
  sim-cast {c = c} (V-inl v) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inl lp lpV)
    with ~-relevant c~′
  ... | sum~ _ _ with c
  ...   | cast (A `⊎ B) (C `⊎ D) ℓ c~ =
    let [ _ , rd* ] = applyCast-reduction-sum-left {ℓ = ℓ} (~-relevant c~) v in
      [ _ , [ _ —→⟨ cast (V-inl v) {A-sum _} ⟩ rd* , ⊑ᶜ-inl lp22 (⊑ᶜ-cast lp11 lp21 lpV) ] ]
  sim-cast v (V-inr v′) (A-sum c) lp1 lp2 lpV = {!!}
