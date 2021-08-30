module LazyCast where

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
  import ParamCastReduction

  data Cast : Type → Set where
    cast : (A : Type) → (B : Type) → Label → Cast (A ⇒ B)

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
    activeErr : ∀ {A B} → (c : Cast (A ⇒ B)) → .(nsc : ¬ (A ⌣ B)) → Active c

  {- Yuck! Is there a nice short proof of ActiveNotRel? -}
  ActiveNotRel : ∀{A}{c : Cast A} (a1 : Active c) (a2 : Active c) → a1 ≡ a2
  ActiveNotRel {⋆ ⇒ ⋆} (activeId {a = a1} _) (activeId {a = a2} _)
      with AtomicNotRel a1 a2
  ... | refl = refl
  ActiveNotRel {⋆ ⇒ ⋆} (activeId _) (activeProj _ x) = ⊥-elimi (x refl)
  ActiveNotRel {⋆ ⇒ ⋆} (activeId _) (activeErr _ nsc) = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ ⋆} (activeProj _ x) a2 = ⊥-elimi (x refl)
  ActiveNotRel {⋆ ⇒ ⋆} (activeErr _ nsc) a2 = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ ` x} (activeProj _ x₁) (activeProj _ x₂) = refl
  ActiveNotRel {⋆ ⇒ ` x} (activeProj _ x₁) (activeErr _ nsc) = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ ` x} (activeErr _ nsc) a2 = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ (B ⇒ B₁)} (activeProj _ x) (activeProj _ x₁) = refl
  ActiveNotRel {⋆ ⇒ (B ⇒ B₁)} (activeProj _ x) (activeErr _ nsc) = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ (B ⇒ B₁)} (activeErr _ nsc) a2 = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ B `× B₁} (activeProj _ x) (activeProj _ x₁) = refl
  ActiveNotRel {⋆ ⇒ B `× B₁} (activeProj _ x) (activeErr _ nsc) = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ B `× B₁} (activeErr _ nsc) a2 = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ B `⊎ B₁} (activeProj _ x) (activeProj _ x₁) = refl
  ActiveNotRel {⋆ ⇒ B `⊎ B₁} (activeProj _ x) (activeErr _ nsc) = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {⋆ ⇒ B `⊎ B₁} (activeErr _ nsc) a2 = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {` x ⇒ ⋆} (activeErr _ nsc) a2 = ⊥-elimi (nsc unk⌣R)
  ActiveNotRel {` x ⇒ ` .x} (activeId {a = a1} _) (activeId {a = a2} _)
      with AtomicNotRel a1 a2
  ... | refl = refl
  ActiveNotRel {` x ⇒ ` .x} (activeId _) (activeErr _ nsc) = ⊥-elimi (nsc base⌣)
  ActiveNotRel {` x ⇒ ` .x} (activeErr _ nsc) (activeId _) = ⊥-elimi (nsc base⌣)
  ActiveNotRel {` x ⇒ ` x₁} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {` x ⇒ (B ⇒ B₁)} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {` x ⇒ B `× B₁} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {` x ⇒ B `⊎ B₁} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {(A ⇒ A₁) ⇒ ⋆} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {(A ⇒ A₁) ⇒ ` x} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {(A ⇒ A₁) ⇒ (B ⇒ B₁)} (activeFun _) (activeFun _) = refl
  ActiveNotRel {(A ⇒ A₁) ⇒ (B ⇒ B₁)} (activeFun _) (activeErr _ nsc) = ⊥-elimi (nsc fun⌣)
  ActiveNotRel {(A ⇒ A₁) ⇒ (B ⇒ B₁)} (activeErr _ nsc) (activeFun _) = ⊥-elimi (nsc fun⌣)
  ActiveNotRel {(A ⇒ A₁) ⇒ (B ⇒ B₁)} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {(A ⇒ A₁) ⇒ B `× B₁} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {(A ⇒ A₁) ⇒ B `⊎ B₁} (activeErr _ nsc₁) (activeErr _ nsc) = refl
  ActiveNotRel {A `× A₁ ⇒ ⋆} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {A `× A₁ ⇒ ` x} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {A `× A₁ ⇒ (B ⇒ B₁)} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {A `× A₁ ⇒ B `× B₁} (activePair _) (activePair _) = refl
  ActiveNotRel {A `× A₁ ⇒ B `× B₁} (activePair _) (activeErr _ nsc) = ⊥-elimi (nsc pair⌣)
  ActiveNotRel {A `× A₁ ⇒ B `× B₁} (activeErr _ nsc) a2 = ⊥-elimi (nsc pair⌣)
  ActiveNotRel {A `× A₁ ⇒ B `⊎ B₁} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {A `⊎ A₁ ⇒ ⋆} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {A `⊎ A₁ ⇒ ` x} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {A `⊎ A₁ ⇒ (B ⇒ B₁)} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {A `⊎ A₁ ⇒ B `× B₁} (activeErr _ nsc) (activeErr _ nsc₁) = refl
  ActiveNotRel {A `⊎ A₁ ⇒ B `⊎ B₁} (activeSum _) (activeSum _) = refl
  ActiveNotRel {A `⊎ A₁ ⇒ B `⊎ B₁} (activeSum _) (activeErr _ nsc) = ⊥-elimi (nsc sum⌣)
  ActiveNotRel {A `⊎ A₁ ⇒ B `⊎ B₁} (activeErr _ nsc) a2 = ⊥-elimi (nsc sum⌣)
  
  open import ParamCastCalculus Cast Inert public

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
  ActiveNotInert (activeId c) (inert neq .c) = ⊥-elimi (neq refl)
  ActiveNotInert (activeProj c neq) (inert _ .c) = ⊥-elimi (neq refl)
  ActiveNotInert (activeErr c neq) (inert _ .c) = ⊥-elimi (neq unk⌣R)

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
  dom (cast (A ⇒ B) (C ⇒ D) ℓ) x = cast C A ℓ

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  cod (cast (A ⇒ B) (C ⇒ D) ℓ) x = cast B D ℓ

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  fstC (cast (A `× B) (C `× D) ℓ) x = cast A C ℓ

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  sndC (cast (A `× B) (C `× D) ℓ) x = cast B D ℓ

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  inlC (cast (A `⊎ B) (C `⊎ D) ℓ) x = cast A C ℓ

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  inrC (cast (A `⊎ B) (C `⊎ D) ℓ) x = cast B D ℓ

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a c (inert x .c) = ⊥-elimi (x refl)

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j c = ActiveNotInert (activeProj c j)

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

  open import CastStructure

  cs : CastStruct
  cs = record { precast = pcs ; applyCast = applyCast }

  open import ParamCastReduction cs public
  open import ParamCastDeterministic cs public

  open import GTLC2CC Cast Inert (λ A B ℓ {c} → (cast A B ℓ)) public

