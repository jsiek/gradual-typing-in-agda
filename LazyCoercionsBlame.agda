module LazyCoercionsBlame where

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
  open import LazyCoercions

  data CastBlameSafe : ∀ {A} → Cast A → Label → Set where

    safe-id : ∀ {A} {a : Atomic A} {ℓ}
      → CastBlameSafe (id {A} {a}) ℓ

    safe-!! : ∀ {A} {i : A ≢ ⋆} {ℓ}
      → CastBlameSafe ((A !!) {i}) ℓ

    safe-?? : ∀ {B} {j : B ≢ ⋆} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
      → CastBlameSafe ((B ?? ℓ′) {j}) ℓ

    safe-↣ : ∀ {S₁ S₂ T₁ T₂} {c : Cast (T₁ ⇒ S₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (c ↣ d) ℓ

    safe-× : ∀ {S₁ S₂ T₁ T₂} {c : Cast (S₁ ⇒ T₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (c `× d) ℓ

    safe-+ : ∀ {S₁ S₂ T₁ T₂} {c : Cast (S₁ ⇒ T₁)} {d : Cast (S₂ ⇒ T₂)} {ℓ}
      → CastBlameSafe c ℓ → CastBlameSafe d ℓ
      → CastBlameSafe (c `+ d) ℓ

    safe-⊥ : ∀ {A B} {ℓ ℓ′}
      → ℓ ≢̂ ℓ′
      → CastBlameSafe (⊥ A ⟨ ℓ′ ⟩ B) ℓ

  domBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (dom c x) ℓ
  domBlameSafe (safe-↣ safe-c safe-d) x = safe-c

  codBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (cod c x) ℓ
  codBlameSafe (safe-↣ safe-c safe-d) x = safe-d

  fstBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (fstC c x) ℓ
  fstBlameSafe (safe-× safe-c safe-d) x = safe-c

  sndBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (sndC c x) ℓ
  sndBlameSafe (safe-× safe-c safe-d) x = safe-d

  inlBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inlC c x) ℓ
  inlBlameSafe (safe-+ safe-c safe-d) x = safe-c

  inrBlameSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} {ℓ} → CastBlameSafe c ℓ → (x : Cross c)
            → CastBlameSafe (inrC c x) ℓ
  inrBlameSafe (safe-+ safe-c safe-d) x = safe-d

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

  coerce-aux-safe : ∀ {A B} {ℓ ℓ′}
    → (c⌣ : A ⌣ B)
    → ℓ ≢̂ ℓ′
    → CastBlameSafe (coerce-aux c⌣ ℓ′) ℓ
  coerce-safe : ∀ {A B} {ℓ ℓ′}
    → ℓ ≢̂ ℓ′
    → CastBlameSafe (coerce A B ℓ′) ℓ
  {- Follow the definitions of `coerce-aux` and `coerce`. -}
  coerce-aux-safe {A} {B} unk⌣L ℓ≢ with eq-unk B
  ... | yes eq rewrite eq = safe-id
  ... | no _ = safe-?? ℓ≢
  coerce-aux-safe {A} {B} unk⌣R ℓ≢ with eq-unk A
  ... | yes eq rewrite eq = safe-id
  ... | no _ = safe-!!
  coerce-aux-safe base⌣ ℓ≢ = safe-id
  coerce-aux-safe fun⌣ ℓ≢ = safe-↣ (coerce-safe (≢̂→≢̂flip ℓ≢)) (coerce-safe ℓ≢)
  coerce-aux-safe pair⌣ ℓ≢ = safe-× (coerce-safe ℓ≢) (coerce-safe ℓ≢)
  coerce-aux-safe sum⌣ ℓ≢ = safe-+ (coerce-safe ℓ≢) (coerce-safe ℓ≢)

  coerce-safe {A} {B} ℓ≢ with A `⌣ B
  ... | yes c⌣ = coerce-aux-safe c⌣ ℓ≢
  ... | no _ = safe-⊥ ℓ≢

  applyCast-pres-allsafe : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → CastBlameSafe c ℓ
    → CastsAllSafe V ℓ
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe {vV = vV} A-proj (safe-?? ℓ≢) allsafe with canonical⋆ _ vV
  ... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with allsafe
  ...   | (allsafe-wrap _ allsafe-M′) = allsafe-cast (coerce-safe ℓ≢) allsafe-M′
  applyCast-pres-allsafe A-fun (safe-↣ safe-c safe-d) allsafe =
    allsafe-ƛ (allsafe-cast safe-d (allsafe-· (rename-pres-allsafe S_ allsafe) (allsafe-cast safe-c allsafe-var)))
  applyCast-pres-allsafe A-pair (safe-× safe-c safe-d) allsafe =
    allsafe-cons (allsafe-cast safe-c (allsafe-fst allsafe)) (allsafe-cast safe-d (allsafe-snd allsafe))
  applyCast-pres-allsafe A-sum (safe-+ safe-c safe-d) allsafe =
    allsafe-case allsafe (allsafe-inl (allsafe-cast safe-c allsafe-var))
                         (allsafe-inr (allsafe-cast safe-d allsafe-var))
  applyCast-pres-allsafe A-id safe-id allsafe = allsafe
  applyCast-pres-allsafe A-fail (safe-⊥ ℓ≢) allsafe = allsafe-blame-diff-ℓ ℓ≢

  open import CastStructureWithBlameSafety

  css : CastStructWithBlameSafety
  css = record { pcss = pcss ; applyCast = applyCast ; applyCast-pres-allsafe = applyCast-pres-allsafe }

  -- Instantiate blame-subtyping theorem for `LazyCoercion`.
  open import ParamBlameSubtyping css using (soundness-<:) public
