module GroundCoercionsBlame where

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
  open import GroundCoercions

  data CastBlameSafe : ∀ {A} → Cast A → Label → Set where

    safe-id : ∀ {A} {a : Atomic A} {ℓ}
      → CastBlameSafe (id {A} {a}) ℓ

    safe-inj : ∀ {A} {g : Ground A} {ℓ}
      → CastBlameSafe (inj A {g}) ℓ

    safe-proj : ∀ {B} {g : Ground B} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
      → CastBlameSafe (proj B ℓ′ {g}) ℓ

    safe-cfun : ∀ {S₁ S₂ T₁ T₂} {c : Cast (T₁ ⇒ S₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (cfun c d) ℓ

    safe-cpair : ∀ {S₁ S₂ T₁ T₂} {c : Cast (S₁ ⇒ T₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (cpair c d) ℓ

    safe-csum : ∀ {S₁ S₂ T₁ T₂} {c : Cast (S₁ ⇒ T₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (csum c d) ℓ

    safe-cseq : ∀ {T₁ T₂ T₃} {c : Cast (T₁ ⇒ T₂)} {d : Cast (T₂ ⇒ T₃)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (cseq c d) ℓ

  domBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (dom c x) ℓ
  domBlameSafe (safe-cfun safe-c safe-d) C-fun = safe-c

  codBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (cod c x) ℓ
  codBlameSafe (safe-cfun safe-c safe-d) C-fun = safe-d

  fstBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (fstC c x) ℓ
  fstBlameSafe (safe-cpair safe-c safe-d) C-pair = safe-c

  sndBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (sndC c x) ℓ
  sndBlameSafe (safe-cpair safe-c safe-d) C-pair = safe-d

  inlBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inlC c x) ℓ
  inlBlameSafe (safe-csum safe-c safe-d) C-sum = safe-c

  inrBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inrC c x) ℓ
  inrBlameSafe (safe-csum safe-c safe-d) C-sum = safe-d

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
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe {vV = vV} {c = proj B ℓ′ {gB}} A-proj (safe-proj ℓ≢) allsafe with canonical⋆ _ vV
  ... | ⟨ G , ⟨ V′ , ⟨ _ , ⟨ I-inj {G} {g} , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with gnd-eq? G B {g} {gB}
  ...   | no _ = allsafe-blame-diff-ℓ ℓ≢
  ...   | yes refl with allsafe
  ...     | allsafe-wrap _ allsafe-V′ = allsafe-V′
  applyCast-pres-allsafe A-pair (safe-cpair safe-c safe-d) allsafe =
    allsafe-cons (allsafe-cast safe-c (allsafe-fst allsafe)) (allsafe-cast safe-d (allsafe-snd allsafe))
  applyCast-pres-allsafe A-sum (safe-csum safe-c safe-d) allsafe =
    allsafe-case allsafe (allsafe-inl (allsafe-cast safe-c allsafe-var))
                         (allsafe-inr (allsafe-cast safe-d allsafe-var))
  applyCast-pres-allsafe A-id _ allsafe = allsafe
  applyCast-pres-allsafe A-seq (safe-cseq safe-c safe-d) allsafe = allsafe-cast safe-d (allsafe-cast safe-c allsafe)

  open import CastStructureWithBlameSafety

  css : CastStructWithBlameSafety
  css = record { pcss = pcss ; applyCast = applyCast ; applyCast-pres-allsafe = applyCast-pres-allsafe }

  -- Instantiate blame-subtyping theorem for `GroundCoercion`.
  open import ParamBlameSubtyping css using (soundness-<:) public
