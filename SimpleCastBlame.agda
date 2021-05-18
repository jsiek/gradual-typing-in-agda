module SimpleCastBlame where

  open import Data.Nat
  open import Data.Bool
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)

  open import Types
  open import Variables
  open import Labels
  open import SimpleCast

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
  applyCast-pres-allsafe (activeId (A ⇒⟨ x ⟩ .A)) safe allsafe = allsafe
  applyCast-pres-allsafe {vV = vV} (activeProj (⋆ ⇒⟨ ℓ ⟩ .⋆) ⋆≢⋆) (safe-<: T<:⋆) = ⊥-elimi (⋆≢⋆ refl)
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

  open import CastStructureWithBlameSafety

  css : CastStructWithBlameSafety
  css = record { pcss = pcss ; applyCast = applyCast ; applyCast-pres-allsafe = applyCast-pres-allsafe }

  -- Instantiate blame-subtyping theorem for `SimpleCast`.
  open import ParamBlameSubtyping css using (soundness-<:) public
