module SimpleCast where

  open import Data.Nat
  open import Data.Bool
  open import Data.Maybe
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)

  data Cast : Type → Set where
    _⇒⟨_⟩_ : (A : Type) → Label → (B : Type) → {c : A ~ B } → Cast (A ⇒ B)

  data Inert : ∀ {A} → Cast A → Set where
    inert : ∀{A} → .(A ≢ ⋆) → (c : Cast (A ⇒ ⋆)) → Inert c

  InertNotRel : ∀{A}{c : Cast A} (i1 : Inert c)(i2 : Inert c) → i1 ≡ i2
  InertNotRel (inert x _) (inert x₁ _) = refl

  data Active : ∀ {A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → .(B ≢ ⋆) → Active c
    activeFun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c

  ActiveNotRel : ∀{A}{c : Cast A} (a1 : Active c) (a2 : Active c) → a1 ≡ a2
  ActiveNotRel (activeId {a = a1} _) (activeId {a = a2} _)
      with AtomicNotRel a1 a2
  ... | refl = refl
  ActiveNotRel (activeId _) (activeProj _ x) = ⊥-elimi (x refl)
  ActiveNotRel (activeProj _ x) (activeId _) = ⊥-elimi (x refl)
  ActiveNotRel (activeProj _ x) (activeProj _ x₁) = refl
  ActiveNotRel (activeFun _) (activeFun _) = refl
  ActiveNotRel (activePair _) (activePair _) = refl
  ActiveNotRel (activeSum _) (activeSum _) = refl

  open import ParamCastCalculus Cast Inert public

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert ((.⋆ ⇒⟨ ℓ ⟩ B) {unk~L}) with eq-unk B
  ... | yes eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (⋆ ⇒⟨ ℓ ⟩ ⋆))
  ... | no neq = inj₁ (activeProj (⋆ ⇒⟨ ℓ ⟩ B) neq)
  ActiveOrInert ((A ⇒⟨ ℓ ⟩ .⋆) {unk~R}) with eq-unk A
  ... | yes eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (⋆ ⇒⟨ ℓ ⟩ ⋆))
  ... | no neq = inj₂ (inert neq (A ⇒⟨ ℓ ⟩ ⋆))
  ActiveOrInert (((` ι)  ⇒⟨ ℓ ⟩ (` ι)) {base~}) =
      inj₁ (activeId{` ι}{A-Base} ((` ι) ⇒⟨ ℓ ⟩ (` ι)))
  ActiveOrInert (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {fun~ c d}) =
      inj₁ (activeFun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)))
  ActiveOrInert (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {pair~ c d}) =
      inj₁ (activePair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))
  ActiveOrInert (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {sum~ c d}) =
      inj₁ (activeSum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))

  ActiveNotInert : ∀ {A} {c : Cast A} → (a : Active c) → ¬ Inert c
  ActiveNotInert (activeId c) (inert neq .c) = ⊥-elimi (neq refl)
  ActiveNotInert (activeProj c neq) (inert _ .c) = ⊥-elimi (neq refl)

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B C D} → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D))) → Cross c
    C-pair : ∀{A B C D} → (c : Cast ((A `× B) ⇒ (C `× D))) → Cross c
    C-sum : ∀{A B C D} → (c : Cast ((A `⊎ B) ⇒ (C `⊎ D))) → Cross c

  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ c ()

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× c ()

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ c ()

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         → Cast (A' ⇒ A₁)
  dom (((A ⇒ B) ⇒⟨ ℓ ⟩ (C ⇒ D)){c}) x
      with ~-relevant c
  ... | fun~ c' d' = (C ⇒⟨ ℓ ⟩ A) {c = c'}

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  cod (((A ⇒ B) ⇒⟨ ℓ ⟩ (C ⇒ D)){c}) x
      with ~-relevant c
  ... | fun~ c' d' = (B ⇒⟨ ℓ ⟩ D) {c = d'}

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  fstC (((A `× B) ⇒⟨ ℓ ⟩ (C `× D)){c}) x
      with ~-relevant c
  ... | pair~ c' d' = (A ⇒⟨ ℓ ⟩ C){c'}

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  sndC (((A `× B) ⇒⟨ ℓ ⟩ (C `× D)){c}) x
      with ~-relevant c
  ... | pair~ c' d' = (B ⇒⟨ ℓ ⟩ D){d'}

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  inlC (((A `⊎ B) ⇒⟨ ℓ ⟩ (C `⊎ D)){c}) x
      with ~-relevant c
  ... | sum~ c' d' = (A ⇒⟨ ℓ ⟩ C){c'}

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  inrC (((A `⊎ B) ⇒⟨ ℓ ⟩ (C `⊎ D)){c}) x
      with ~-relevant c
  ... | sum~ c' d' = (B ⇒⟨ ℓ ⟩ D){d'}

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a c (inert x .c) = ⊥-elimi (x refl)

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j c = ActiveNotInert (activeProj c j)

  {- Here we define the precision relation for casts: -}
  infix 6 ⟪_⟫⊑⟪_⟫
  data ⟪_⟫⊑⟪_⟫ : ∀ {A A′ B B′} → {c : Cast (A ⇒ B)} → {c′ : Cast (A′ ⇒ B′)}
                               → (i : Inert c) → (i′ : Inert c′) → Set where
    -- Inert injections
    lpii-inj : ∀ {A A′} {c : Cast (A ⇒ ⋆)} {c′ : Cast (A′ ⇒ ⋆)}
       → (nd : A ≢ ⋆) → (nd′ : A′ ≢ ⋆)
       → A ⊑ A′
         --------------------------------
       → ⟪ inert nd c ⟫⊑⟪ inert nd′ c′ ⟫

  infix 6 ⟪_⟫⊑_
  data ⟪_⟫⊑_ : ∀ {A B} → {c : Cast (A ⇒ B)} → Inert c → Type → Set where
    -- Inert injections
    lpit-inj : ∀ {A A′} {c : Cast (A ⇒ ⋆)}
      → (nd : A ≢ ⋆)
      → A ⊑ A′
        --------------------
      → ⟪ inert nd c ⟫⊑ A′

  infix 6 _⊑⟪_⟫
  data _⊑⟪_⟫ : ∀ {A′ B′} → {c′ : Cast (A′ ⇒ B′)} → Type → Inert c′ → Set where

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

  open import ParamCastAux pcs public

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  {- Id -}
  applyCast {Γ} {A} {.A} M v ((A ⇒⟨ ℓ ⟩ .A) {c}) {activeId .(A ⇒⟨ ℓ ⟩ A)} = M
  {- Collapse and Conflict -}
  applyCast {Γ} {.⋆} {B} M v ((.⋆ ⇒⟨ ℓ ⟩ B) {c}) {activeProj .(⋆ ⇒⟨ ℓ ⟩ B) x}
         with canonical⋆ M v
  ...  | ⟨ A' , ⟨ M' , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | yes ap-b = M' ⟨ (A' ⇒⟨ ℓ ⟩ B) {ap-b} ⟩
  ...    | no ap-b = blame ℓ
  {- Wrap -}
  applyCast {Γ} {A₁ ⇒ A₂} {B₁ ⇒ B₂} M v ((.(_ ⇒ _) ⇒⟨ ℓ ⟩ .(_ ⇒ _)) {c})
      {activeFun .((_ ⇒ _) ⇒⟨ ℓ ⟩ (_ ⇒ _))} =
      eta⇒ M (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {c})
          (C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)))
  {- Cast Pair -}
  applyCast{Γ}{A₁ `× A₂}{B₁ `× B₂}M v ((_ ⇒⟨ ℓ ⟩ _){c}){activePair(_ ⇒⟨ ℓ ⟩ _)} =
       eta× M (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)){c})
          (C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))
  {- Cast Sum -}
  applyCast{Γ}{A₁ `⊎ A₂}{B₁ `⊎ B₂}M v((_ ⇒⟨ ℓ ⟩ _){c}){activeSum .(_ ⇒⟨ ℓ ⟩ _)} =
     eta⊎ M (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)){c})
       (C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))

  open import CastStructure

  cs : CastStruct
  cs = record { precast = pcs ; applyCast = applyCast }

  open import ParamCastReduction cs public

  open import ParamCastDeterministic cs public

  import GTLC2CC
  open GTLC2CC Cast Inert (λ A B ℓ {c} → (A ⇒⟨ ℓ ⟩ B) {c}) public

