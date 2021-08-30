module SimpleCoercionsBlame where

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
  open import SimpleCoercions

  data CastBlameSafe : ∀ {A} → Cast A → Label → Set where

    safe-id : ∀ {A} {a : Atomic A} {ℓ}
      → CastBlameSafe (id {A} {a}) ℓ

    safe-inj : ∀ {A} {i : A ≢ ⋆} {ℓ}
      → CastBlameSafe (inj A {i}) ℓ

    safe-proj : ∀ {B} {j : B ≢ ⋆} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
      → CastBlameSafe (proj B ℓ′ {j}) ℓ

    safe-cfun : ∀ {S₁ S₂ T₁ T₂} {c : Cast (T₁ ⇒ S₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (cfun c d) ℓ

    safe-cpair : ∀ {S₁ S₂ T₁ T₂} {c : Cast (S₁ ⇒ T₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (cpair c d) ℓ

    safe-csum : ∀ {S₁ S₂ T₁ T₂} {c : Cast (S₁ ⇒ T₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (csum c d) ℓ

  domBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (dom c x) ℓ
  domBlameSafe (safe-cfun safe-c safe-d) x = safe-c

  codBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (cod c x) ℓ
  codBlameSafe (safe-cfun safe-c safe-d) x = safe-d

  fstBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (fstC c x) ℓ
  fstBlameSafe (safe-cpair safe-c safe-d) x = safe-c

  sndBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (sndC c x) ℓ
  sndBlameSafe (safe-cpair safe-c safe-d) x = safe-d

  inlBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inlC c x) ℓ
  inlBlameSafe (safe-csum safe-c safe-d) x = safe-c

  inrBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inrC c x) ℓ
  inrBlameSafe (safe-csum safe-c safe-d) x = safe-d

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

  coerce-safe : ∀ {A B} {ℓ ℓ′}
    → (c~ : A ~ B)
    → ℓ ≢̂ ℓ′
    → CastBlameSafe (coerce A B {c~} ℓ′) ℓ
  coerce-safe {A} {B} unk~L ℓ≢ with eq-unk B
  ... | yes eq rewrite eq = safe-id
  ... | no  _ = safe-proj ℓ≢
  coerce-safe {A} {B} unk~R ℓ≢ with eq-unk A
  ... | yes eq rewrite eq = safe-id
  ... | no _ = safe-inj
  coerce-safe base~ ℓ≢ = safe-id
  coerce-safe (fun~ c~ d~) ℓ≢ = safe-cfun (coerce-safe c~ (≢̂→≢̂flip ℓ≢)) (coerce-safe d~ ℓ≢)
  coerce-safe (pair~ c~ d~) ℓ≢ = safe-cpair (coerce-safe c~ ℓ≢) (coerce-safe d~ ℓ≢)
  coerce-safe (sum~ c~ d~) ℓ≢ = safe-csum (coerce-safe c~ ℓ≢) (coerce-safe d~ ℓ≢)

  applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → CastBlameSafe c ℓ
    → CastsAllSafe V ℓ
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe {vV = vV} (A-proj {B}) (safe-proj ℓ≢) allsafe with canonical⋆ _ vV
  ... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A′ `~ B
  ...   | no _ = allsafe-blame-diff-ℓ ℓ≢
  ...   | yes A′~B with allsafe
  ...     | (allsafe-wrap _ allsafe-M′) = allsafe-cast (coerce-safe A′~B ℓ≢) allsafe-M′
  applyCast-pres-allsafe A-fun (safe-cfun safe-c safe-d) allsafe =
    allsafe-ƛ (allsafe-cast safe-d (allsafe-· (rename-pres-allsafe S_ allsafe) (allsafe-cast safe-c allsafe-var)))
  applyCast-pres-allsafe A-pair (safe-cpair safe-c safe-d) allsafe =
    allsafe-cons (allsafe-cast safe-c (allsafe-fst allsafe))
                 (allsafe-cast safe-d (allsafe-snd allsafe))
  applyCast-pres-allsafe A-sum (safe-csum safe-c safe-d) allsafe =
    allsafe-case allsafe (allsafe-inl (allsafe-cast safe-c allsafe-var))
                         (allsafe-inr (allsafe-cast safe-d allsafe-var))
  applyCast-pres-allsafe A-id safe allsafe = allsafe

  open import CastStructureWithBlameSafety

  css : CastStructWithBlameSafety
  css = record { pcss = pcss ; applyCast = applyCast ; applyCast-pres-allsafe = applyCast-pres-allsafe }

  -- Instantiate blame-subtyping theorem for `SimpleCoercion`.
  open import ParamBlameSubtyping css using (soundness-<:) public

