module GroundCastBlame where

  open import Data.Nat
  open import Data.Bool
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to [_,_])
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)

  open import Types
  open import Variables
  open import Labels
  open import GroundCast

  open import Subtyping using (_<:₃_)
  open _<:₃_
  infix 5 _<:_
  _<:_ = _<:₃_

  data CastBlameSafe : ∀ {A} → Cast A → Label → Set where

    safe-<: : ∀ {S T} {c~ : S ~ T} {ℓ}
      → S <: T
        ----------------------------
      → CastBlameSafe (cast S T ℓ c~) ℓ

    safe-ℓ≢ : ∀ {S T} {c~ : S ~ T} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
        -----------------------------
      → CastBlameSafe (cast S T ℓ′ c~) ℓ

  domBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (dom c x) ℓ
  domBlameSafe (safe-<: {c~ = c~} (<:-⇒ sub-dom sub-cod)) x with ~-relevant c~
  ... | fun~ d~ _ = safe-<: {c~ = d~} sub-dom
  domBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | fun~ d~ _ = safe-ℓ≢ {c~ = d~} ℓ≢

  codBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (cod c x) ℓ
  codBlameSafe (safe-<: {c~ = c~} (<:-⇒ sub-dom sub-cod)) x with ~-relevant c~
  ... | fun~ _ d~ = safe-<: {c~ = d~} sub-cod
  codBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | fun~ _ d~ = safe-ℓ≢ {c~ = d~} ℓ≢

  fstBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (fstC c x) ℓ
  fstBlameSafe (safe-<: {c~ = c~} (<:-× sub-fst sub-snd)) x with ~-relevant c~
  ... | pair~ d~ _ = safe-<: {c~ = d~} sub-fst
  fstBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | pair~ d~ _ = safe-ℓ≢ {c~ = d~} ℓ≢

  sndBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (sndC c x) ℓ
  sndBlameSafe (safe-<: {c~ = c~} (<:-× sub-fst sub-snd)) x with ~-relevant c~
  ... | pair~ _ d~ = safe-<: {c~ = d~} sub-snd
  sndBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | pair~ _ d~ = safe-ℓ≢ {c~ = d~} ℓ≢

  inlBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inlC c x) ℓ
  inlBlameSafe (safe-<: {c~ = c~} (<:-⊎ sub-l sub-r)) x with ~-relevant c~
  ... | sum~ d~ _ = safe-<: {c~ = d~} sub-l
  inlBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | sum~ d~ _ = safe-ℓ≢ {c~ = d~} ℓ≢

  inrBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inrC c x) ℓ
  inrBlameSafe (safe-<: {c~ = c~} (<:-⊎ sub-l sub-r)) x with ~-relevant c~
  ... | sum~ _ d~ = safe-<: {c~ = d~} sub-r
  inrBlameSafe (safe-ℓ≢ {c~ = c~} ℓ≢) x with ~-relevant c~
  ... | sum~ _ d~ = safe-ℓ≢ {c~ = d~} ℓ≢

  open import PreCastStructureWithBlameSafety

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

  open import ParamCastSubtyping pcss

  applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → CastBlameSafe c ℓ
    → CastsAllSafe V ℓ
      --------------------------------------
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe (A-id _) safe allsafe = allsafe
  applyCast-pres-allsafe (A-inj (cast ⋆ .⋆ _ _) _ ⋆≢⋆) (safe-<: <:-⋆) allsafe = ⊥-elimi (⋆≢⋆ refl)
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
  applyCast-pres-allsafe (A-proj (cast ⋆ .⋆ ℓ _) ⋆≢⋆) (safe-<: <:-⋆) allsafe = ⊥-elimi (⋆≢⋆ refl)
  applyCast-pres-allsafe (A-proj (cast ⋆ .⋆ ℓ _) ⋆≢⋆) (safe-<: (<:-G _ _)) allsafe = ⊥-elimi (⋆≢⋆ refl)
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

  open import CastStructureWithBlameSafety
  
  css : CastStructWithBlameSafety
  css = record { pcss = pcss ; applyCast = applyCast ; applyCast-pres-allsafe = applyCast-pres-allsafe }

  -- Instantiate blame-subtyping theorem for `GroundCast`.
  open import ParamBlameSubtyping css using (soundness-<:) public


