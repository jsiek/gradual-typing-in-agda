module LazyCast where

  open import Data.Nat
  open import Data.Bool
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
  import ParamCastReduction

  data Cast : Type → Set where
    cast : (A : Type) → (B : Type) → Label → Cast (A ⇒ B)

  data Inert : ∀ {A} → Cast A → Set where
    inert : ∀{A} → A ≢ ⋆ → (c : Cast (A ⇒ ⋆)) → Inert c

  data Active : ∀ {A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c
    activeFun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c
    activeErr : ∀ {A B} → (c : Cast (A ⇒ B)) → ¬ (A ⌣ B) → Active c

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast Inert
  open CastCalc

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert (cast ⋆ B ℓ) with eq-unk B
  ... | yes eq rewrite eq = inj₁ (activeId {a = A-Unk} (cast ⋆ ⋆ ℓ))
  ... | no neq = inj₁ (activeProj (cast ⋆ B ℓ) neq)
  ActiveOrInert (cast (` ι) B ℓ) with (` ι) `⌣ B
  ... | yes c with c
  ...    | base⌣ = inj₁ (activeId {a = A-Base} (cast (` ι) (` ι) ℓ))
  ...    | unk⌣R = inj₂ (inert (λ ()) (cast (` ι) ⋆ ℓ))
  ActiveOrInert (cast (` ι) B ℓ) | no nc = inj₁ (activeErr (cast (` ι) B ℓ) nc)
  ActiveOrInert (cast (A₁ ⇒ A₂) B ℓ) with (A₁ ⇒ A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ ⇒ A₂) B ℓ) nc)
  ... | yes c with c
  ...    | unk⌣R = inj₂ (inert (λ ()) (cast (A₁ ⇒ A₂) ⋆ ℓ))
  ...    | fun⌣{A' = A'}{B' = B'} =
            inj₁ (activeFun (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ))
  ActiveOrInert (cast (A₁ `× A₂) B ℓ) with (A₁ `× A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ `× A₂) B ℓ) nc)
  ... | yes c with c
  ...    | unk⌣R = inj₂ (inert (λ ()) (cast (A₁ `× A₂) ⋆ ℓ))
  ...    | pair⌣{A' = A'}{B' = B'} =
             inj₁ (activePair (cast (A₁ `× A₂) (A' `× B') ℓ))
  ActiveOrInert (cast (A₁ `⊎ A₂) B ℓ) with (A₁ `⊎ A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ `⊎ A₂) B ℓ) nc)
  ... | yes c with c
  ...    | unk⌣R = inj₂ (inert (λ ()) (cast (A₁ `⊎ A₂) ⋆ ℓ))
  ...    | sum⌣{A' = A'}{B' = B'} =
             inj₁ (activeSum (cast (A₁ `⊎ A₂) (A' `⊎ B') ℓ))

  ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
  ActiveNotInert (activeId c) (inert neq .c) = neq refl
  ActiveNotInert (activeProj c neq) (inert _ .c) = neq refl
  ActiveNotInert (activeErr c neq) (inert _ .c) = neq unk⌣R

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
  dom (cast (A ⇒ B) (C ⇒ D) ℓ) x = cast C A ℓ

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (cast (A ⇒ B) (C ⇒ D) ℓ) x = cast B D ℓ

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (cast (A `× B) (C `× D) ℓ) x = cast A C ℓ

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (cast (A `× B) (C `× D) ℓ) x = cast B D ℓ

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (cast (A `⊎ B) (C `⊎ D) ℓ) x = cast A C ℓ

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (cast (A `⊎ B) (C `⊎ D) ℓ) x = cast B D ℓ

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a c (inert x .c) = contradiction refl x

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j c = ActiveNotInert (activeProj c j)

  open import Subtyping using (_<:₁_)
  open _<:₁_
  infix 5 _<:_
  _<:_ = _<:₁_

  data CastBlameSafe : ∀ {A} → Cast A → Label → Set where

    safe-<: : ∀ {S T} {ℓ}
      → S <: T
        ----------------------------
      → CastBlameSafe (cast S T ℓ) ℓ

    safe-ℓ≢ : ∀ {S T} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
        -----------------------------
      → CastBlameSafe (cast S T ℓ′) ℓ

  domBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (dom c x) ℓ
  domBlameSafe (safe-<: (<:-⇒ sub-dom sub-cod)) x = safe-<: sub-dom
  domBlameSafe (safe-ℓ≢ ℓ≢) x = safe-ℓ≢ ℓ≢

  codBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (cod c x) ℓ
  codBlameSafe (safe-<: (<:-⇒ sub-dom sub-cod)) x = safe-<: sub-cod
  codBlameSafe (safe-ℓ≢ ℓ≢) x = safe-ℓ≢ ℓ≢

  fstBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (fstC c x) ℓ
  fstBlameSafe (safe-<: (<:-× sub-fst sub-snd)) x = safe-<: sub-fst
  fstBlameSafe (safe-ℓ≢ ℓ≢) x = safe-ℓ≢ ℓ≢

  sndBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (sndC c x) ℓ
  sndBlameSafe (safe-<: (<:-× sub-fst sub-snd)) x = safe-<: sub-snd
  sndBlameSafe (safe-ℓ≢ ℓ≢) x = safe-ℓ≢ ℓ≢

  inlBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inlC c x) ℓ
  inlBlameSafe (safe-<: (<:-⊎ sub-l sub-r)) x = safe-<: sub-l
  inlBlameSafe (safe-ℓ≢ ℓ≢) x = safe-ℓ≢ ℓ≢

  inrBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inrC c x) ℓ
  inrBlameSafe (safe-<: (<:-⊎ sub-l sub-r)) x = safe-<: sub-r
  inrBlameSafe (safe-ℓ≢ ℓ≢) x = safe-ℓ≢ ℓ≢

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
  applyCast M v (cast A A ℓ) {activeId (cast A A ℓ)} = M
  applyCast M v (cast ⋆ B ℓ) {activeProj (cast ⋆ B ℓ) x}
        with canonical⋆ M v
  ... | ⟨ A , ⟨ M' , ⟨ c' , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq =
            M' ⟨ cast A B ℓ ⟩
  applyCast {Γ} M v (cast (A ⇒ B) (A' ⇒ B') ℓ) {activeFun _} =
     ƛ (((rename (λ {A₂} → S_) M) · ((` Z) ⟨ cast A' A ℓ ⟩)) ⟨ cast B B' ℓ ⟩)
  applyCast {Γ} M v (cast (A `× B) (A' `× B') ℓ) {activePair _} =
     cons (fst M ⟨ cast A A' ℓ ⟩) (snd M ⟨ cast B B' ℓ ⟩)
  applyCast {Γ} M v (cast (A `⊎ B) (A' `⊎ B') ℓ) {activeSum _} =
     let l = inl ((` Z) ⟨ cast A A' ℓ ⟩) in
     let r = inr ((` Z) ⟨ cast B B' ℓ ⟩) in
     case M l r
  applyCast {Γ} {A} {B} M v (cast A B ℓ) {activeErr .(cast A B ℓ) x} =
     blame ℓ

  applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → CastBlameSafe c ℓ
    → CastsAllSafe V ℓ
      --------------------------------------
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe (activeId (cast A A ℓ)) safe allsafe = allsafe
  applyCast-pres-allsafe {vV = vV} (activeProj (cast ⋆ .⋆ ℓ) ⋆≢⋆) (safe-<: T<:⋆) = contradiction refl ⋆≢⋆
  applyCast-pres-allsafe {vV = vV} (activeProj (cast ⋆ B ℓ′) x) (safe-ℓ≢ ℓ≢) allsafe with canonical⋆ _ vV
  ... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with allsafe
  ...   | allsafe-wrap _ allsafe-M′ = allsafe-cast (safe-ℓ≢ ℓ≢) allsafe-M′
  applyCast-pres-allsafe (activeFun _) (safe-<: (<:-⇒ sub-dom sub-cod)) allsafe =
    allsafe-ƛ (allsafe-cast (safe-<: sub-cod) (allsafe-· (rename-pres-allsafe S_ allsafe)
                                                         (allsafe-cast (safe-<: sub-dom) allsafe-var)))
  applyCast-pres-allsafe (activeFun _) (safe-ℓ≢ ℓ≢) allsafe =
    allsafe-ƛ (allsafe-cast (safe-ℓ≢ ℓ≢) (allsafe-· (rename-pres-allsafe S_ allsafe)
                                                    (allsafe-cast (safe-ℓ≢ ℓ≢) allsafe-var)))
  applyCast-pres-allsafe (activePair _) (safe-<: (<:-× sub-fst sub-snd)) allsafe =
    allsafe-cons (allsafe-cast (safe-<: sub-fst) (allsafe-fst allsafe))
                               (allsafe-cast (safe-<: sub-snd) (allsafe-snd allsafe))
  applyCast-pres-allsafe (activePair _) (safe-ℓ≢ ℓ≢) allsafe =
    allsafe-cons (allsafe-cast (safe-ℓ≢ ℓ≢) (allsafe-fst allsafe))
                               (allsafe-cast (safe-ℓ≢ ℓ≢) (allsafe-snd allsafe))
  applyCast-pres-allsafe (activeSum _) (safe-<: (<:-⊎ sub-l sub-r)) allsafe =
    allsafe-case allsafe (allsafe-inl (allsafe-cast (safe-<: sub-l) allsafe-var))
                         (allsafe-inr (allsafe-cast (safe-<: sub-r) allsafe-var))
  applyCast-pres-allsafe (activeSum _) (safe-ℓ≢ ℓ≢) allsafe =
    allsafe-case allsafe (allsafe-inl (allsafe-cast (safe-ℓ≢ ℓ≢) allsafe-var))
                         (allsafe-inr (allsafe-cast (safe-ℓ≢ ℓ≢) allsafe-var))
  applyCast-pres-allsafe (activeErr .(cast _ ⋆ _) ¬c⌣) (safe-<: T<:⋆) allsafe = allsafe-blame-diff-ℓ (λ _ → ¬c⌣ unk⌣R)
  applyCast-pres-allsafe (activeErr .(cast (` _) (` _) _) ¬c⌣) (safe-<: <:-B) allsafe = allsafe-blame-diff-ℓ (λ _ → ¬c⌣ base⌣)
  applyCast-pres-allsafe (activeErr .(cast (_ `× _) (_ `× _) _) ¬c⌣) (safe-<: (<:-× x x₁)) allsafe = allsafe-blame-diff-ℓ (λ _ → ¬c⌣ pair⌣)
  applyCast-pres-allsafe (activeErr .(cast (_ `⊎ _) (_ `⊎ _) _) ¬c⌣) (safe-<: (<:-⊎ x x₁)) allsafe = allsafe-blame-diff-ℓ (λ _ → ¬c⌣ sum⌣)
  applyCast-pres-allsafe (activeErr .(cast (_ ⇒ _) (_ ⇒ _) _) ¬c⌣) (safe-<: (<:-⇒ x x₁)) allsafe = allsafe-blame-diff-ℓ (λ _ → ¬c⌣ fun⌣)
  applyCast-pres-allsafe (activeErr .(cast _ _ _) ¬c⌣) (safe-ℓ≢ ℓ≢) allsafe = allsafe-blame-diff-ℓ ℓ≢

  open import CastStructure
  open import CastStructureWithBlameSafety

  cs : CastStruct
  cs = record { precast = pcs ; applyCast = applyCast }

  css : CastStructWithBlameSafety
  css = record { pcss = pcss ; applyCast = applyCast ; applyCast-pres-allsafe = applyCast-pres-allsafe }

  import ParamCastReduction
  open ParamCastReduction cs public

  import GTLC2CC
  open GTLC2CC Cast Inert (λ A B ℓ {c} → (cast A B ℓ)) public

  -- Instantiate blame-subtyping theorem for `LazyCast`.
  open import ParamBlameSubtyping css using (soundness-<:) public
