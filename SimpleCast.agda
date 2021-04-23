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

  data Cast : Type → Set where
    _⇒⟨_⟩_ : (A : Type) → Label → (B : Type) → {c : A ~ B } → Cast (A ⇒ B)

  data Inert : ∀ {A} → Cast A → Set where
    inert : ∀{A} → A ≢ ⋆ → (c : Cast (A ⇒ ⋆)) → Inert c

  data Active : ∀ {A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c
    activeFun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast Inert
  open CastCalc

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
  ActiveNotInert (activeId c) (inert neq .c) = neq refl
  ActiveNotInert (activeProj c neq) (inert _ .c) = neq refl

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

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
  dom (((A ⇒ B) ⇒⟨ ℓ ⟩ (C ⇒ D)){c}) x
      with ~-relevant c
  ... | fun~ c' d' = (C ⇒⟨ ℓ ⟩ A) {c = c'}

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (((A ⇒ B) ⇒⟨ ℓ ⟩ (C ⇒ D)){c}) x
      with ~-relevant c
  ... | fun~ c' d' = (B ⇒⟨ ℓ ⟩ D) {c = d'}

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (((A `× B) ⇒⟨ ℓ ⟩ (C `× D)){c}) x
      with ~-relevant c
  ... | pair~ c' d' = (A ⇒⟨ ℓ ⟩ C){c'}

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (((A `× B) ⇒⟨ ℓ ⟩ (C `× D)){c}) x
      with ~-relevant c
  ... | pair~ c' d' = (B ⇒⟨ ℓ ⟩ D){d'}

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (((A `⊎ B) ⇒⟨ ℓ ⟩ (C `⊎ D)){c}) x
      with ~-relevant c
  ... | sum~ c' d' = (A ⇒⟨ ℓ ⟩ C){c'}

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (((A `⊎ B) ⇒⟨ ℓ ⟩ (C `⊎ D)){c}) x
      with ~-relevant c
  ... | sum~ c' d' = (B ⇒⟨ ℓ ⟩ D){d'}

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a c (inert x .c) = contradiction refl x

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

  open import Subtyping using (_<:₁_)
  open _<:₁_
  infix 5 _<:_
  _<:_ = _<:₁_

  data CastBlameSafe : ∀ {A} → Cast A → Label → Set where

    safe-<: : ∀ {S T} {c~ : S ~ T} {ℓ}
      → S <: T
        ----------------------------
      → CastBlameSafe ((S ⇒⟨ ℓ ⟩ T) {c~}) ℓ

    safe-ℓ≢ : ∀ {S T} {c~ : S ~ T} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
        -----------------------------
      → CastBlameSafe ((S ⇒⟨ ℓ′ ⟩ T) {c~}) ℓ

  domBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (dom c x) ℓ
  domBlameSafe (safe-<: {c~ = c~} (<:-⇒ sub-dom sub-cod)) x with ~-relevant c~
  ... | fun~ _ _ = safe-<: sub-dom
  domBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | fun~ _ _ = safe-ℓ≢ ℓ≢

  codBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (cod c x) ℓ
  codBlameSafe (safe-<: {c~ = c~} (<:-⇒ sub-dom sub-cod)) x with ~-relevant c~
  ... | fun~ _ _ = safe-<: sub-cod
  codBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | fun~ _ _ = safe-ℓ≢ ℓ≢

  fstBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (fstC c x) ℓ
  fstBlameSafe (safe-<: {c~ = c~} (<:-× sub-fst sub-snd)) x with ~-relevant c~
  ... | pair~ _ _ = safe-<: sub-fst
  fstBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | pair~ _ _ = safe-ℓ≢ ℓ≢

  sndBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (sndC c x) ℓ
  sndBlameSafe (safe-<: {c~ = c~} (<:-× sub-fst sub-snd)) x with ~-relevant c~
  ... | pair~ _ _ = safe-<: sub-snd
  sndBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | pair~ _ _ = safe-ℓ≢ ℓ≢

  inlBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inlC c x) ℓ
  inlBlameSafe (safe-<: {c~ = c~} (<:-⊎ sub-l sub-r)) x with ~-relevant c~
  ... | sum~ _ _ = safe-<: sub-l
  inlBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | sum~ _ _ = safe-ℓ≢ ℓ≢

  inrBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inrC c x) ℓ
  inrBlameSafe (safe-<: {c~ = c~} (<:-⊎ sub-l sub-r)) x with ~-relevant c~
  ... | sum~ _ _ = safe-<: sub-r
  inrBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | sum~ _ _ = safe-ℓ≢ ℓ≢

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

  applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → CastBlameSafe c ℓ
    → CastsAllSafe V ℓ
      --------------------------------------
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe (activeId (A ⇒⟨ x ⟩ .A)) safe allsafe = allsafe
  applyCast-pres-allsafe {vV = vV} (activeProj (⋆ ⇒⟨ ℓ ⟩ .⋆) ⋆≢⋆) (safe-<: T<:⋆) = contradiction refl ⋆≢⋆
  applyCast-pres-allsafe {vV = vV} (activeProj (⋆ ⇒⟨ ℓ′ ⟩ B) x) (safe-ℓ≢ ℓ≢) allsafe with canonical⋆ _ vV
  ... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A′ `~ B
  ...   | no _  = allsafe-blame-diff-ℓ ℓ≢
  ...   | yes _ with allsafe
  ...     | (allsafe-wrap _ allsafe-M′) = allsafe-cast (safe-ℓ≢ ℓ≢) allsafe-M′
  applyCast-pres-allsafe (activeFun ((.(_ ⇒ _) ⇒⟨ ℓ ⟩ .(_ ⇒ _)) {c~})) (safe-<: (<:-⇒ sub-dom sub-cod)) allsafe
    with ~-relevant c~
  ... | fun~ _ _ = allsafe-ƛ (allsafe-cast (safe-<: sub-cod) (allsafe-· (rename-pres-allsafe S_ allsafe)
                                                             (allsafe-cast (safe-<: sub-dom) allsafe-var)))
  applyCast-pres-allsafe (activeFun ((.(_ ⇒ _) ⇒⟨ ℓ′ ⟩ .(_ ⇒ _)) {c~})) (safe-ℓ≢ ℓ≢) allsafe
    with ~-relevant c~
  ... | fun~ _ _ = allsafe-ƛ (allsafe-cast (safe-ℓ≢ ℓ≢) (allsafe-· (rename-pres-allsafe S_ allsafe)
                                                        (allsafe-cast (safe-ℓ≢ ℓ≢) allsafe-var)))
  applyCast-pres-allsafe (activePair ((.(_ `× _) ⇒⟨ ℓ ⟩ .(_ `× _)) {c~})) (safe-<: (<:-× sub-fst sub-snd)) allsafe
    with ~-relevant c~
  ... | pair~ _ _ = allsafe-cons (allsafe-cast (safe-<: sub-fst) (allsafe-fst allsafe))
                                 (allsafe-cast (safe-<: sub-snd) (allsafe-snd allsafe))
  applyCast-pres-allsafe (activePair ((.(_ `× _) ⇒⟨ ℓ ⟩ .(_ `× _)) {c~})) (safe-ℓ≢ ℓ≢) allsafe
    with ~-relevant c~
  ... | pair~ _ _ = allsafe-cons (allsafe-cast (safe-ℓ≢ ℓ≢) (allsafe-fst allsafe))
                                 (allsafe-cast (safe-ℓ≢ ℓ≢) (allsafe-snd allsafe))
  applyCast-pres-allsafe (activeSum ((.(_ `⊎ _) ⇒⟨ ℓ ⟩ .(_ `⊎ _)) {c~})) (safe-<: (<:-⊎ sub-l sub-r)) allsafe
    with ~-relevant c~
  ... | sum~ _ _ = allsafe-case allsafe (allsafe-inl (allsafe-cast (safe-<: sub-l) allsafe-var))
                                        (allsafe-inr (allsafe-cast (safe-<: sub-r) allsafe-var))
  applyCast-pres-allsafe (activeSum ((.(_ `⊎ _) ⇒⟨ ℓ ⟩ .(_ `⊎ _)) {c~})) (safe-ℓ≢ ℓ≢) allsafe
    with ~-relevant c~
  ... | sum~ _ _ = allsafe-case allsafe (allsafe-inl (allsafe-cast (safe-ℓ≢ ℓ≢) allsafe-var))
                                        (allsafe-inr (allsafe-cast (safe-ℓ≢ ℓ≢) allsafe-var))

  open import CastStructure
  open import CastStructureWithBlameSafety

  cs : CastStruct
  cs = record { precast = pcs ; applyCast = applyCast }

  css : CastStructWithBlameSafety
  css = record { pcss = pcss ; applyCast = applyCast ; applyCast-pres-allsafe = applyCast-pres-allsafe }

  import ParamCastReduction
  open ParamCastReduction cs public

  import GTLC2CC
  open GTLC2CC Cast Inert (λ A B ℓ {c} → (A ⇒⟨ ℓ ⟩ B) {c}) public

  -- Instantiate blame-subtyping theorem for `SimpleCast`.
  open import ParamBlameSubtyping css using (soundness-<:) public
