module LazyCoercions where

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

  infix 7 _↣_
  infix 5 _!!
  infix 5 _??_
  infix 5 ⊥_⟨_⟩_

  data Cast : Type → Set where
    id : ∀ {A : Type} {a : Atomic A} → Cast (A ⇒ A)
    _!! : (A : Type) → ∀ {i : A ≢ ⋆} → Cast (A ⇒ ⋆)
    _??_ : (B : Type) → Label → ∀ {j : B ≢ ⋆} → Cast (⋆ ⇒ B)
    _↣_ : ∀ {A B A' B'}
      → (c : Cast (B ⇒ A)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A ⇒ A') ⇒ (B ⇒ B'))
    _`×_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A `× A') ⇒ (B `× B'))
    _`+_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A `⊎ A') ⇒ (B `⊎ B'))
    ⊥_⟨_⟩_ :
        (A : Type) → Label → (B : Type)
      → Cast (A ⇒ B)

  coerce : (A : Type) → (B : Type) → Label → Cast (A ⇒ B)
  coerce-aux : ∀{A B : Type} → A ⌣ B → Label → Cast (A ⇒ B)

  coerce A B ℓ
      with (A `⌣ B)
  ... | yes d = coerce-aux d ℓ
  ... | no _ = ⊥ A ⟨ ℓ ⟩ B

  coerce-aux {B = B} unk⌣L ℓ with eq-unk B
  ... | yes eq rewrite eq = id {a = A-Unk}
  ... | no neq = (B ?? ℓ) {j = neq}
  coerce-aux {A = A} unk⌣R ℓ  with eq-unk A
  ... | yes eq rewrite eq = id {a = A-Unk}
  ... | no neq = (A !!) {i = neq}
  coerce-aux base⌣ ℓ = id {a = A-Base}
  coerce-aux (fun⌣{A₁}{A₂}{B₁}{B₂}) ℓ =
    (coerce B₁ A₁ (flip ℓ)) ↣ (coerce A₂ B₂ ℓ)
  coerce-aux (pair⌣{A₁}{A₂}{B₁}{B₂}) ℓ = (coerce A₁ B₁ ℓ) `× (coerce A₂ B₂ ℓ)
  coerce-aux (sum⌣{A₁}{A₂}{B₁}{B₂}) ℓ = (coerce A₁ B₁ ℓ) `+ (coerce A₂ B₂ ℓ)

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A i} → Inert ((A !!) {i})

  InertNotRel : ∀{A}{c : Cast A} (i1 : Inert c)(i2 : Inert c) → i1 ≡ i2
  InertNotRel I-inj I-inj = refl

  data Active : ∀ {A} → Cast A → Set where
    A-proj : ∀{ B ℓ j} → Active ((B ?? ℓ) {j})
    A-fun : ∀{A B A' B'}{c : Cast (A ⇒ B)} {d : Cast (A' ⇒ B')} → Active(c ↣ d)
    A-pair : ∀{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')} → Active(c `× d)
    A-sum : ∀{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')} → Active(c `+ d)
    A-id : ∀{A a} → Active (id {A}{a})
    A-fail : ∀{A B ℓ} → Active (⊥ A ⟨ ℓ ⟩ B)

  ActiveNotRel : ∀{A}{c : Cast A} (a1 : Active c) (a2 : Active c) → a1 ≡ a2
  ActiveNotRel A-proj A-proj = refl
  ActiveNotRel A-fun A-fun = refl
  ActiveNotRel A-pair A-pair = refl
  ActiveNotRel A-sum A-sum = refl
  ActiveNotRel A-id A-id = refl
  ActiveNotRel A-fail A-fail = refl

  open import ParamCastCalculus Cast Inert public

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id = inj₁ A-id
  ActiveOrInert (A !!) = inj₂ I-inj
  ActiveOrInert (B ?? ℓ) = inj₁ A-proj
  ActiveOrInert (c ↣ c₁) = inj₁ A-fun
  ActiveOrInert (c `× c₁) = inj₁ A-pair
  ActiveOrInert (c `+ c₁) = inj₁ A-sum
  ActiveOrInert (⊥ A ⟨ ℓ ⟩ B) = inj₁ A-fail

  ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
  ActiveNotInert A-proj ()
  ActiveNotInert A-fun ()
  ActiveNotInert A-pair ()
  ActiveNotInert A-sum ()
  ActiveNotInert A-id ()
  ActiveNotInert A-fail ()

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B A' B'}{c : Cast (B ⇒ A)}{d : Cast (A' ⇒ B')} → Cross (c ↣ d)
    C-pair : ∀{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')} → Cross (c `× d)
    C-sum : ∀{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')} → Cross (c `+ d)

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
  dom (c ↣ d) x = c

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  cod (c ↣ d) x = d

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  fstC (c `× d) x = c

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  sndC (c `× d) x = d

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  inlC (c `+ d) x = c

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  inrC (c `+ d) x = d

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a (_!! ⋆ {i}) I-inj = contradiction refl i

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j id = contradiction refl j
  projNotInert j (.⋆ !!) = contradiction refl j
  projNotInert j (B ?? x) = ActiveNotInert A-proj
  projNotInert j (⊥ .⋆ ⟨ x ⟩ B) = ActiveNotInert A-fail

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

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
              → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id {a} = M
  applyCast M v (A !!) {()}
  applyCast M v (B ?? ℓ) {a} with canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq = M' ⟨ coerce A' B ℓ ⟩
  applyCast{Γ} M v (c ↣ d) {a} =
     ƛ (((rename (λ {A} → S_) M) · ((` Z) ⟨ c ⟩)) ⟨ d ⟩)
  applyCast M v (c `× d) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast M v (c `+ d) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in
    let r = inr ((` Z) ⟨ d ⟩) in
    case M l r
  applyCast M v (⊥ A ⟨ ℓ ⟩ B) = blame ℓ


  open import CastStructure

  cs : CastStruct
  cs = record { precast = pcs ; applyCast = applyCast }

  open import ParamCastReduction cs public
  open import ParamCastDeterministic cs public

  import GTLC2CC
  open GTLC2CC Cast Inert (λ A B ℓ {c} → coerce A B ℓ) public

