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
  applyCast M v (cast (A₁ `× A₂) (B₁ `× B₂) ℓ c') {A-pair _}
      with ~-relevant c'
  ... | pair~ c d =
    cons (fst M ⟨ cast A₁ B₁ ℓ c ⟩) (snd M ⟨ cast A₂ B₂ ℓ d ⟩)
  applyCast M v (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ c') {A-sum _}
      with ~-relevant c'
  ... | sum~ c d =
    let l = inl ((` Z) ⟨ cast A₁ B₁ ℓ c ⟩) in
    let r = inr ((` Z) ⟨ cast A₂ B₂ ℓ d ⟩) in
    case M l r

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
  applyCast-pres-allsafe (A-pair (cast (_ `× _) (_ `× _) ℓ c~)) (safe-<: (<:-× sub-fst sub-snd)) allsafe with ~-relevant c~
  ... | pair~ c~fst c~snd = allsafe-cons (allsafe-cast (safe-<: {c~ = c~fst} sub-fst) (allsafe-fst allsafe))
                                         (allsafe-cast (safe-<: {c~ = c~snd} sub-snd) (allsafe-snd allsafe))
  applyCast-pres-allsafe (A-pair (cast (_ `× _) (_ `× _) ℓ′ c~)) (safe-ℓ≢ ℓ≢) allsafe with ~-relevant c~
  ... | pair~ c~fst c~snd = allsafe-cons (allsafe-cast (safe-ℓ≢ {c~ = c~fst} ℓ≢) (allsafe-fst allsafe))
                                         (allsafe-cast (safe-ℓ≢ {c~ = c~snd} ℓ≢) (allsafe-snd allsafe))
  applyCast-pres-allsafe (A-sum (cast (_ `⊎ _) (_ `⊎ _) ℓ c~)) (safe-<: (<:-⊎ sub-l sub-r)) allsafe with ~-relevant c~
  ... | sum~ c~l c~r = allsafe-case allsafe (allsafe-inl (allsafe-cast (safe-<: {c~ = c~l} sub-l) allsafe-var))
                                            (allsafe-inr (allsafe-cast (safe-<: {c~ = c~r} sub-r) allsafe-var))
  applyCast-pres-allsafe (A-sum (cast (_ `⊎ _) (_ `⊎ _) ℓ′ c~)) (safe-ℓ≢ ℓ≢) allsafe with ~-relevant c~
  ... | sum~ c~l c~r = allsafe-case allsafe (allsafe-inl (allsafe-cast (safe-ℓ≢ {c~ = c~l} ℓ≢) allsafe-var))
                                            (allsafe-inr (allsafe-cast (safe-ℓ≢ {c~ = c~r} ℓ≢) allsafe-var))

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

    applyCast-proj-catchup : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
      → (nd : B ≢ ⋆)
      → (vV : Value V) → Value V′
      → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
        ----------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))

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
      [ cons V₁ V₂ , [ V-pair v₁ v₂ , [ {!!} , ⊑ᶜ-cons lpV₁ lpV₂ ] ] ]
    applyCast-proj-ng-catchup {B = B₁ `⊎ B₂} nd ng v v′ lp lpV = {!!}


