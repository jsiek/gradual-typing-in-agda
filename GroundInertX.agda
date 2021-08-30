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
  open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)

  {- Definitions: Cast, Active, and Inert -}
  data Cast : Type → Set where
    cast : (A : Type) → (B : Type) → Label → A ~ B → Cast (A ⇒ B)

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A} → Ground A → (c : Cast (A ⇒ ⋆)) → Inert c
    -- All cross casts are inert!
    I-fun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Inert c
    I-pair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Inert c
    I-sum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Inert c

  InertNotRel : ∀{A}{c : Cast A} (i1 : Inert c)(i2 : Inert c) → i1 ≡ i2
  InertNotRel (I-inj g1 _) (I-inj g2 _)
      with GroundNotRel g1 g2
  ... | refl = refl
  InertNotRel (I-fun _) (I-fun _) = refl
  InertNotRel (I-pair _) (I-pair _) = refl
  InertNotRel (I-sum _) (I-sum _) = refl

  data Active : ∀ {A} → Cast A → Set where
    A-id : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    A-inj : ∀{A} → (c : Cast (A ⇒ ⋆)) → .(¬ Ground A) → .(A ≢ ⋆) → Active c
    A-proj : ∀{B} → (c : Cast (⋆ ⇒ B)) → .(B ≢ ⋆) → Active c

  ActiveNotRel : ∀{A}{c : Cast A} (a1 : Active c) (a2 : Active c) → a1 ≡ a2
  ActiveNotRel (A-id {a = a1} _) (A-id {a = a2} _)
      with AtomicNotRel a1 a2
  ... | refl = refl
  ActiveNotRel (A-id _) (A-inj _ x x₁) = ⊥-elimi (x₁ refl)
  ActiveNotRel (A-id _) (A-proj _ x) = ⊥-elimi (x refl)
  ActiveNotRel (A-inj _ x x₁) (A-id _) = ⊥-elimi (x₁ refl)
  ActiveNotRel (A-inj _ x x₁) (A-inj _ x₂ x₃) = refl
  ActiveNotRel (A-inj _ x x₁) (A-proj _ x₂) = ⊥-elimi (x₁ refl)
  ActiveNotRel (A-proj _ x) (A-id _) = ⊥-elimi (x refl)
  ActiveNotRel (A-proj _ x) (A-inj _ x₁ x₂) = ⊥-elimi (x refl)
  ActiveNotRel (A-proj _ x) (A-proj _ x₁) = refl

  open import ParamCastCalculus Cast Inert public

  open import GTLC2CC Cast Inert (λ A B ℓ {c} → cast A B ℓ c) public

  base-consis-eq : ∀ {ι ι' : Base} → .(` ι ~ ` ι') → ι ≡ ι'
  base-consis-eq {Nat} {Nat} c = refl
  base-consis-eq {Int} {Int} c = refl
  base-consis-eq {𝔹} {𝔹} c = refl
  base-consis-eq {Unit} {Unit} c = refl
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
  ActiveNotInert (A-inj c ¬g _) (I-inj g .c) = ⊥-elimi (¬g g)
  ActiveNotInert (A-proj c neq) (I-inj _ .c) = ⊥-elimi (neq refl)

  {- Cross casts: -}
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

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         → Cast (A' ⇒ A₁)
  dom (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ c') x
      with ~-relevant c'
  ... | fun~ c d = cast A' A₁ ℓ c

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  cod (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ c') x
      with ~-relevant c'
  ... | fun~ c d = cast A₂ B' ℓ d

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  fstC (cast (A `× B) (C `× D) ℓ c') x
      with ~-relevant c'
  ... | pair~ c d = cast A C ℓ c

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  sndC (cast (A `× B) (C `× D) ℓ c') x
      with ~-relevant c'
  ... | pair~ c d = cast B D ℓ d

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  inlC (cast (A `⊎ B) (C `⊎ D) ℓ c') x
      with ~-relevant c'
  ... | sum~ c d = cast A C ℓ c

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  inrC (cast (A `⊎ B) (C `⊎ D) ℓ c') x
      with ~-relevant c'
  ... | sum~ c d = cast B D ℓ d

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a c = ActiveNotInert (A-id {a = a} c)

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j c = ActiveNotInert (A-proj c j)

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

  open import ParamCastAux pcs public

  inert-ground : ∀{A} → (c : Cast (A ⇒ ⋆)) → Inert c → Ground A
  inert-ground c (I-inj g .c) = g

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
     → ∀ {a : Active c} → Γ ⊢ B
  {- V : ι ⇒ ι   —→   V -}
  applyCast M v c {A-id c} = M
  {- V : A ⇒ ⋆   —→   V : A ⇒ G ⇒ ⋆ -}
  applyCast M v (cast A ⋆ ℓ cn) {A-inj c a-ng a-nd}
      with ground A {a-nd}
  ... | [ G , cns ] = (M ⟨ cast A G ℓ (proj₂ cns) ⟩) ⟨ cast G ⋆ ℓ unk~R ⟩
  {- V : G ⇒p ⋆ ⇒q G  —→   V
     V : G ⇒p ⋆ ⇒q H  —→   blame q -}
  applyCast M v (cast ⋆ B ℓ cn) {A-proj c b-nd}
      with ground? B
  ... | yes b-g
          with canonical⋆ M v
  ...     | [ G , [ V , [ c' , [ i , meq ] ] ] ] rewrite meq
              with gnd-eq? G B {inert-ground c' i} {b-g}
  ...         | yes ap-b rewrite ap-b = V
  ...         | no ap-b = blame ℓ
  {- V : ⋆ ⇒ B   —→   V : ⋆ ⇒ H ⇒ B -}
  applyCast M v (cast ⋆ B ℓ cn) {A-proj c b-nd}
      | no b-ng with ground B {b-nd}
  ...    | [ H , [ h-g , cns ] ] =
           (M ⟨ cast ⋆ H ℓ unk~L ⟩) ⟨ cast H B ℓ (Sym~ cns) ⟩
  {- Since cross casts are all inert we don't have cases for them here. -}

  open import CastStructure

  cs : CastStruct
  cs = record { precast = pcs ; applyCast = applyCast }

  {- We now instantiate the module ParamCastReduction and thereby prove type safety. -}
  open import ParamCastReduction cs public
  open import ParamCastDeterministic cs public
