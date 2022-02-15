module LazyGroundCast where

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
    cast : (A : Type) → (B : Type) → Label → (A ~ B) → Cast (A ⇒ B)

  data Inert : ∀ {A} → Cast A → Set where
    inert : ∀{A} → Ground A → (c : Cast (A ⇒ ⋆)) → Inert c

  InertNotRel : ∀{A}{c : Cast A} (i1 : Inert c)(i2 : Inert c) → i1 ≡ i2
  InertNotRel (inert g _) (inert h _) rewrite GroundNotRel g h = refl

  data Active : ∀ {A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeInj : ∀{A} → (c : Cast (A ⇒ ⋆)) → .(¬ Ground A) → .(A ≢ ⋆) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → .(B ≢ ⋆) → Active c
    activeFun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c
    activeErr : ∀ {A B} → (c : Cast (A ⇒ B)) → .(nsc : ¬ (A ⌣ B)) → Active c

  {- Yuck! Is there a nice short proof of ActiveNotRel? -}
  ActiveNotRel : ∀{A}{c : Cast A} (a1 : Active c) (a2 : Active c) → a1 ≡ a2
  ActiveNotRel {.(A ⇒ A)} {cast A .A ℓ _} (activeId {a = a1} .(cast A A ℓ _)) (activeId {a = a2} .(cast A A ℓ _))
    rewrite AtomicNotRel a1 a2 = refl
  ActiveNotRel {.(⋆ ⇒ ⋆)} {cast .⋆ .⋆ ℓ _} (activeId .(cast ⋆ ⋆ ℓ _)) (activeInj .(cast ⋆ ⋆ ℓ _) x x₁) = ⊥-elimi (x₁ refl)
  ActiveNotRel {.(⋆ ⇒ ⋆)} {cast .⋆ .⋆ ℓ _} (activeId .(cast ⋆ ⋆ ℓ _)) (activeProj .(cast ⋆ ⋆ ℓ _) x) = ⊥-elimi (x refl)
  ActiveNotRel {.(A ⇒ A)} {cast A .A ℓ _} (activeId .(cast A A ℓ _)) (activeErr .(cast A A ℓ _) nsc) = ⊥-elimi (nsc (⌣-refl A))
  ActiveNotRel {.(⋆ ⇒ ⋆)} {cast .⋆ .⋆ ℓ _} (activeInj .(cast ⋆ ⋆ ℓ _) x x₁) (activeId .(cast ⋆ ⋆ ℓ _)) = ⊥-elimi (x₁ refl)
  ActiveNotRel {.(A ⇒ ⋆)} {cast A .⋆ ℓ _} (activeInj .(cast A ⋆ ℓ _) x x₁) (activeInj .(cast A ⋆ ℓ _) x₂ x₃) = refl
  ActiveNotRel {.(⋆ ⇒ ⋆)} {cast .⋆ .⋆ ℓ _} (activeInj .(cast ⋆ ⋆ ℓ _) x x₁) (activeProj .(cast ⋆ ⋆ ℓ _) x₂) = ⊥-elimi (x₂ refl)
  ActiveNotRel {.(A ⇒ ⋆)} {cast A .⋆ ℓ _} (activeInj .(cast A ⋆ ℓ _) x x₁) (activeErr .(cast A ⋆ ℓ _) nsc) = ⊥-elimi (nsc unk⌣R)
  ActiveNotRel {.(⋆ ⇒ ⋆)} {cast .⋆ .⋆ ℓ _} (activeProj .(cast ⋆ ⋆ ℓ _) x) (activeId .(cast ⋆ ⋆ ℓ _)) = ⊥-elimi (x refl)
  ActiveNotRel {.(⋆ ⇒ ⋆)} {cast .⋆ .⋆ ℓ _} (activeProj .(cast ⋆ ⋆ ℓ _) x) (activeInj .(cast ⋆ ⋆ ℓ _) x₁ x₂) = ⊥-elimi (x₂ refl)
  ActiveNotRel {.(⋆ ⇒ B)} {cast .⋆ B ℓ _} (activeProj .(cast ⋆ B ℓ _) x) (activeProj .(cast ⋆ B ℓ _) x₁) = refl
  ActiveNotRel {.(⋆ ⇒ B)} {cast .⋆ B ℓ _} (activeProj .(cast ⋆ B ℓ _) x) (activeErr .(cast ⋆ B ℓ _) nsc) = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {.((_ ⇒ _) ⇒ (_ ⇒ _))} {cast .(_ ⇒ _) .(_ ⇒ _) ℓ _} (activeFun .(cast (_ ⇒ _) (_ ⇒ _) ℓ _)) (activeFun .(cast (_ ⇒ _) (_ ⇒ _) ℓ _)) = refl
  ActiveNotRel {.((_ ⇒ _) ⇒ (_ ⇒ _))} {cast .(_ ⇒ _) .(_ ⇒ _) ℓ _} (activeFun .(cast (_ ⇒ _) (_ ⇒ _) ℓ _)) (activeErr .(cast (_ ⇒ _) (_ ⇒ _) ℓ _) nsc) = ⊥-elimi (nsc fun⌣)
  ActiveNotRel {.(_ `× _ ⇒ _ `× _)} {cast .(_ `× _) .(_ `× _) ℓ _} (activePair .(cast (_ `× _) (_ `× _) ℓ _)) (activePair .(cast (_ `× _) (_ `× _) ℓ _)) = refl
  ActiveNotRel {.(_ `× _ ⇒ _ `× _)} {cast .(_ `× _) .(_ `× _) ℓ _} (activePair .(cast (_ `× _) (_ `× _) ℓ _)) (activeErr .(cast (_ `× _) (_ `× _) ℓ _) nsc) = ⊥-elimi (nsc pair⌣)
  ActiveNotRel {.(_ `⊎ _ ⇒ _ `⊎ _)} {cast .(_ `⊎ _) .(_ `⊎ _) ℓ _} (activeSum .(cast (_ `⊎ _) (_ `⊎ _) ℓ _)) (activeSum .(cast (_ `⊎ _) (_ `⊎ _) ℓ _)) = refl
  ActiveNotRel {.(_ `⊎ _ ⇒ _ `⊎ _)} {cast .(_ `⊎ _) .(_ `⊎ _) ℓ _} (activeSum .(cast (_ `⊎ _) (_ `⊎ _) ℓ _)) (activeErr .(cast (_ `⊎ _) (_ `⊎ _) ℓ _) nsc) = ⊥-elimi (nsc sum⌣)
  ActiveNotRel {.(A ⇒ A)} {cast A .A ℓ _} (activeErr .(cast A A ℓ _) nsc) (activeId .(cast A A ℓ _)) = ⊥-elimi (nsc (⌣-refl A))
  ActiveNotRel {.(A ⇒ ⋆)} {cast A .⋆ ℓ _} (activeErr .(cast A ⋆ ℓ _) nsc) (activeInj .(cast A ⋆ ℓ _) x x₁) = ⊥-elimi (nsc unk⌣R)
  ActiveNotRel {.(⋆ ⇒ B)} {cast .⋆ B ℓ _} (activeErr .(cast ⋆ B ℓ _) nsc) (activeProj .(cast ⋆ B ℓ _) x) = ⊥-elimi (nsc unk⌣L)
  ActiveNotRel {.((_ ⇒ _) ⇒ (_ ⇒ _))} {cast .(_ ⇒ _) .(_ ⇒ _) ℓ _} (activeErr .(cast (_ ⇒ _) (_ ⇒ _) ℓ _) nsc) (activeFun .(cast (_ ⇒ _) (_ ⇒ _) ℓ _)) = ⊥-elimi (nsc fun⌣)
  ActiveNotRel {.(_ `× _ ⇒ _ `× _)} {cast .(_ `× _) .(_ `× _) ℓ _} (activeErr .(cast (_ `× _) (_ `× _) ℓ _) nsc) (activePair .(cast (_ `× _) (_ `× _) ℓ _)) = ⊥-elimi (nsc pair⌣)
  ActiveNotRel {.(_ `⊎ _ ⇒ _ `⊎ _)} {cast .(_ `⊎ _) .(_ `⊎ _) ℓ _} (activeErr .(cast (_ `⊎ _) (_ `⊎ _) ℓ _) nsc) (activeSum .(cast (_ `⊎ _) (_ `⊎ _) ℓ _)) = ⊥-elimi (nsc sum⌣)
  ActiveNotRel {.(A ⇒ B)} {cast A B ℓ _} (activeErr .(cast A B ℓ _) nsc) (activeErr .(cast A B ℓ _) nsc₁) = refl

  open import ParamCastCalculus Cast Inert public

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert (cast ⋆ B ℓ _) with eq-unk B
  ... | yes eq rewrite eq = inj₁ (activeId {a = A-Unk} (cast ⋆ ⋆ ℓ _))
  ... | no neq = inj₁ (activeProj (cast ⋆ B ℓ _) neq)
  ActiveOrInert (cast (` ι) B ℓ _) with (` ι) `⌣ B
  ... | yes c with c
  ...    | base⌣ = inj₁ (activeId {a = A-Base} (cast (` ι) (` ι) ℓ _))
  ...    | unk⌣R = inj₂ (inert G-Base (cast (` ι) ⋆ ℓ _))
  ActiveOrInert (cast (` ι) B ℓ _) | no nc = inj₁ (activeErr (cast (` ι) B ℓ _) nc)
  ActiveOrInert (cast (A₁ ⇒ A₂) B ℓ _) with (A₁ ⇒ A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ ⇒ A₂) B ℓ _) nc)
  ... | yes c with c
  ...    | fun⌣{A' = A'}{B' = B'} =
            inj₁ (activeFun (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ _))
  ...    | unk⌣R with ground? (A₁ ⇒ A₂)
  ...       | yes g = inj₂ (inert g (cast (A₁ ⇒ A₂) ⋆ ℓ _))
  ...       | no ¬g = inj₁ (activeInj (cast (A₁ ⇒ A₂) ⋆ ℓ _) ¬g λ ())
  ActiveOrInert (cast (A₁ `× A₂) B ℓ _) with (A₁ `× A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ `× A₂) B ℓ _) nc)
  ... | yes c with c
  ...    | pair⌣{A' = A'}{B' = B'} =
             inj₁ (activePair (cast (A₁ `× A₂) (A' `× B') ℓ _))
  ...    | unk⌣R with ground? (A₁ `× A₂)
  ...       | yes g = inj₂ (inert g (cast (A₁ `× A₂) ⋆ ℓ _))
  ...       | no ¬g = inj₁ (activeInj (cast (A₁ `× A₂) ⋆ ℓ _) ¬g λ ())
  ActiveOrInert (cast (A₁ `⊎ A₂) B ℓ _) with (A₁ `⊎ A₂) `⌣ B
  ... | no nc = inj₁ (activeErr (cast (A₁ `⊎ A₂) B ℓ _) nc)
  ... | yes c with c
  ...    | sum⌣{A' = A'}{B' = B'} =
             inj₁ (activeSum (cast (A₁ `⊎ A₂) (A' `⊎ B') ℓ _))
  ...    | unk⌣R with ground? (A₁ `⊎ A₂)
  ...       | yes g = inj₂ (inert g (cast (A₁ `⊎ A₂) ⋆ ℓ _))
  ...       | no ¬g = inj₁ (activeInj (cast (A₁ `⊎ A₂) ⋆ ℓ _) ¬g λ ())
  ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
  ActiveNotInert (activeId c) (inert () .c)
  ActiveNotInert (activeInj c ng nd) (inert g .c) = ⊥-elimi (ng g)
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
  dom (cast (A ⇒ B) (C ⇒ D) ℓ (fun~ c d)) x = cast C A ℓ c

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  cod (cast (A ⇒ B) (C ⇒ D) ℓ (fun~ c d)) x = cast B D ℓ d

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  fstC (cast (A `× B) (C `× D) ℓ (pair~ c d)) x = cast A C ℓ c

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  sndC (cast (A `× B) (C `× D) ℓ (pair~ c d)) x = cast B D ℓ d

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  inlC (cast (A `⊎ B) (C `⊎ D) ℓ (sum~ c d)) x = cast A C ℓ c

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  inrC (cast (A `⊎ B) (C `⊎ D) ℓ (sum~ c d)) x = cast B D ℓ d

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert a c (inert () .c)

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
  applyCast M v (cast A A ℓ _) {activeId (cast A A ℓ _)} = M
  applyCast M v (cast A ⋆ ℓ _) {activeInj c ng nd}
      with ground A {nd}
  ... | ⟨ G , ⟨ g , A~G ⟩ ⟩ = (M ⟨ cast A G ℓ A~G ⟩) ⟨ cast G ⋆ ℓ unk~R ⟩
  applyCast (M′ ⟪ inert {G} g c ⟫) (V-wrap v i) (cast ⋆ B ℓ _)
                               {activeProj .(cast ⋆ B ℓ _) bnd}
      with ground B {bnd}
  ... | ⟨ H , ⟨ h , B~H ⟩ ⟩
      with gnd-eq? G H {g}{h}
  ... | yes refl = M′ ⟨ cast G B ℓ (Sym~ B~H) ⟩ 
      {-
       M′ ⟪ G ⇒ ⋆ ⟫ ⟨ ⋆ ⇒ B ⟩ —→ M′ ⟨ G ⇒ B ⟩   if G = gnd(B)
      -}
  ... | no neq = blame ℓ
  applyCast {Γ} M v (cast (A ⇒ B) (A' ⇒ B') ℓ (fun~ c d)) {activeFun _} = 
      ƛ ((rename S_ M · ((` Z) ⟨ cast A' A ℓ c ⟩)) ⟨ cast B B' ℓ d ⟩)
  applyCast {Γ} M v (cast (A `× B) (A' `× B') ℓ (pair~ c d)) {activePair _} =
     cons (fst M ⟨ cast A A' ℓ c ⟩) (snd M ⟨ cast B B' ℓ d ⟩)
  applyCast {Γ} M v (cast (A `⊎ B) (A' `⊎ B') ℓ (sum~ c d)) {activeSum _} =
     let l = inl ((` Z) ⟨ cast A A' ℓ c ⟩) in
     let r = inr ((` Z) ⟨ cast B B' ℓ d ⟩) in
     case M l r
  applyCast {Γ} {A} {B} M v (cast A B ℓ _) {activeErr .(cast A B ℓ _) x} =
     blame ℓ

  open import CastStructure

  cs : CastStruct
  cs = record { precast = pcs ; applyCast = applyCast }

  open import ParamCastReduction cs public
  open import ParamCastDeterministic cs public

  open import GTLC2CC Cast Inert (λ A B ℓ {c} → (cast A B ℓ c)) public

