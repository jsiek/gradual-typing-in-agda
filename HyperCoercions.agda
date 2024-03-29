{-

   The notion of hyper-coercions is an unpublished idea from Jeremy
   Siek and Andre Kuhlenschmidt, inspired by the super-coercions of
   Ronald Garcia (ICFP 2013).  The goal is to reduce the amount of
   space and the number of indirections (pointers) needed in the
   representation of coercions. We conjecture that a hyper-coercion
   can fit into a 64-bit word. The hyper-coercions in this file are
   for the lazy UD semantics, so they can be seen as an alternative to
   the coercion of λS.

-}

module HyperCoercions where

  open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s; _+_; _*_)
  open import Data.Nat.Properties using (⊔-identityʳ; ≤-refl; ≤-reflexive; ≤-trans; ≤-step;
       ⊔-mono-≤; ⊔-monoʳ-≤; ⊔-monoˡ-≤; ⊔-comm; ⊔-assoc; m≤m⊔n; m≤n⊔m; ⊔-idem; +-mono-≤; +-comm; *-monoʳ-≤)
  open Data.Nat.Properties.≤-Reasoning
  open import Data.Nat.Solver
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
      renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Pow2
  open import Types hiding (_⊔_)
  open import Variables
  open import Labels

  data Inj : Type → Set
  data Proj : Type → Set
  data Middle : Type → Set
  data Cast : Type → Set

  data Cast where
    id★ : Cast (⋆ ⇒ ⋆)
    _↷_,_ : ∀{A B C D} → Proj (A ⇒ B) → Middle (B ⇒ C) → Inj (C ⇒ D)
          → Cast (A ⇒ D)

  data Proj where
    𝜖 : ∀{A} → Proj (A ⇒ A)
    ?? : Label → {H : Type} {g : Ground H} → Proj (⋆ ⇒ H)

  data Middle where
    id : (ι : Base) → Middle ((` ι) ⇒ (` ι))
    _↣_ : ∀ {A B A' B'}
        → (c : Cast (B ⇒ A)) → (d : Cast (A' ⇒ B'))
          -----------------------------------------
        → Middle ((A ⇒ A') ⇒ (B ⇒ B'))
    _×'_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Middle ((A `× A') ⇒ (B `× B'))
    _+'_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Middle ((A `⊎ A') ⇒ (B `⊎ B'))


  data Inj where
    𝜖 : ∀{A} → Inj (A ⇒ A)
    !! : ∀ {G} {g : Ground G} → Inj (G ⇒ ⋆)
    cfail : ∀{A B} → Label → Inj (A ⇒ B)


  height-m : ∀{A B} → (c : Middle (A ⇒ B)) → ℕ

  height : ∀{A B} → (c : Cast (A ⇒ B)) → ℕ
  height id★ = 0
  height (p ↷ m , i) = height-m m

  height-m (id ι) = 0
  height-m (c ↣ d) = suc ((height c) ⊔ (height d))
  height-m (c ×' d) = suc ((height c) ⊔ (height d))
  height-m (c +' d) = suc ((height c) ⊔ (height d))

  import ParamCastCalculusOrig
  module CastCalc = ParamCastCalculusOrig Cast
  open CastCalc

  coerce-to-gnd : (A : Type) → (B : Type) → {g : Ground B}
     → ∀ {c : A ~ B}{a : A ≢ ⋆} → Label → Middle (A ⇒ B)
  coerce-from-gnd : (A : Type) → (B : Type) → {g : Ground A}
     → ∀ {c : A ~ B}{b : B ≢ ⋆} → Label → Middle (A ⇒ B)
  coerce : (A : Type) → (B : Type) → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)

  coerce-to⋆ : (A : Type) → Label → Cast (A ⇒ ⋆)
  coerce-to⋆ A ℓ with eq-unk A
  ... | yes eq rewrite eq = id★
  ... | no neq with ground? A
  ...     | yes g =  𝜖 ↷ (coerce-to-gnd A A {g}{Refl~}{neq} ℓ) , !! {A} {g}
  ...     | no ng with ground A {neq}
  ...          | ⟨ G , ⟨ g , c ⟩ ⟩ =
                 𝜖 ↷ (coerce-to-gnd A G {g}{c}{neq} ℓ) , !! {G} {g}

  coerce-from⋆ : (B : Type) → Label → Cast (⋆ ⇒ B)
  coerce-from⋆ B ℓ with eq-unk B
  ... | yes eq rewrite eq = id★
  ... | no neq with ground? B
  ...     | yes g = (?? ℓ) {B}{g} ↷ (coerce-from-gnd B B {g}{Refl~}{neq} ℓ) , 𝜖
  ...     | no ng with ground B {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ =
               (?? ℓ) {G}{g} ↷ (coerce-from-gnd G B {g}{Sym~ c}{neq} ℓ) , 𝜖

  coerce-to-gnd .⋆ B {g} {unk~L} {neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (` ι) (` ι) {g} {base~} {neq} ℓ = id ι
  coerce-to-gnd (A ⇒ B) (⋆ ⇒ ⋆) {G-Fun} {fun~ c d} {neq} ℓ =
     (coerce-from⋆ A ℓ) ↣ (coerce-to⋆ B ℓ)
  coerce-to-gnd (A `× B) (⋆ `× ⋆) {G-Pair} {pair~ c d} {neq} ℓ =
     (coerce-to⋆ A ℓ) ×' (coerce-to⋆ B ℓ)
  coerce-to-gnd (A `⊎ B) (⋆ `⊎ ⋆) {G-Sum} {sum~ c d} {neq} ℓ =
     (coerce-to⋆ A ℓ) +' (coerce-to⋆ B ℓ)

  coerce-from-gnd A .⋆ {g} {unk~R} {neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd (` ι) (` ι) {g} {base~} {neq} ℓ = id ι
  coerce-from-gnd (⋆ ⇒ ⋆) (A ⇒ B) {G-Fun} {fun~ c d} {neq} ℓ =
     (coerce-to⋆ A ℓ) ↣ (coerce-from⋆ B ℓ)
  coerce-from-gnd (⋆ `× ⋆) (A `× B) {G-Pair} {pair~ c d} {neq} ℓ =
     (coerce-from⋆ A ℓ) ×' (coerce-from⋆ B ℓ)
  coerce-from-gnd (⋆ `⊎ ⋆) (A `⊎ B) {G-Sum} {sum~ c d} {neq} ℓ =
     (coerce-from⋆ A ℓ) +' (coerce-from⋆ B ℓ)

  coerce .⋆ B {unk~L} ℓ = coerce-from⋆ B ℓ
  coerce A .⋆ {unk~R} ℓ = coerce-to⋆ A ℓ
  coerce (` ι) (` ι) {base~} ℓ = 𝜖 ↷ id ι , 𝜖
  coerce (A ⇒ B) (C ⇒ D) {fun~ c d} ℓ =
     𝜖 ↷ (coerce C A {c} ℓ ↣ coerce B D {d} ℓ) , 𝜖
  coerce (A `× B) (C `× D) {pair~ c d} ℓ =
     𝜖 ↷ (coerce A C {c} ℓ ×' coerce B D {d} ℓ) , 𝜖
  coerce (A `⊎ B) (C `⊎ D) {sum~ c d} ℓ =
     𝜖 ↷ (coerce A C {c} ℓ +' coerce B D {d} ℓ) , 𝜖


  mkcast = (λ A B ℓ {c} → coerce A B {c} ℓ)
  import GTLC2CCOrig
  module Compile = GTLC2CCOrig Cast mkcast


  data InertMiddle : ∀ {A} → Middle A → Set where
    I-cfun : ∀{A B A' B'}{s : Cast (B ⇒ A)} {t : Cast (A' ⇒ B')}
          → InertMiddle (s ↣ t)

  data ActiveMiddle : ∀ {A} → Middle A → Set where
    A-cpair : ∀{A B A' B'}{s : Cast (A ⇒ B)} {t : Cast (A' ⇒ B')}
          → ActiveMiddle (s ×' t)
    A-csum : ∀{A B A' B'}{s : Cast (A ⇒ B)} {t : Cast (A' ⇒ B')}
          → ActiveMiddle (s +' t)
    A-idι : ∀{ι}
          → ActiveMiddle (id ι)

  data Active : ∀ {A} → Cast A → Set where
    A-id★ : Active id★
    A-proj : ∀{A B}{ℓ}{g : Ground A}{m : Middle (A ⇒ B)}
           → Active ((?? ℓ) {A}{g} ↷ m , 𝜖)
    A-proj-inj : ∀{A B}{ℓ}{g : Ground A}{m : Middle (A ⇒ B)}{gB : Ground B}
           → Active ((?? ℓ) {A}{g} ↷ m , !! {g = gB})
    A-fail : ∀{A B C D}{ℓ}{p : Proj (A ⇒ B)}{m : Middle (B ⇒ C)}
           → Active (p ↷ m , cfail {C} {D} ℓ)
    A-mid : ∀{A B}{m : Middle (A ⇒ B)}
          → ActiveMiddle m
          → Active (𝜖 ↷ m , 𝜖)

  ActiveMiddleNotRel : ∀{A}{c : Middle A} (a1 : ActiveMiddle c) (a2 : ActiveMiddle c) → a1 ≡ a2
  ActiveMiddleNotRel A-cpair A-cpair = refl
  ActiveMiddleNotRel A-csum A-csum = refl 
  ActiveMiddleNotRel A-idι A-idι = refl
  
  ActiveNotRel : ∀{A}{c : Cast A} (a1 : Active c) (a2 : Active c) → a1 ≡ a2
  ActiveNotRel A-id★ A-id★ = refl
  ActiveNotRel A-proj A-proj = refl 
  ActiveNotRel A-proj-inj A-proj-inj = refl 
  ActiveNotRel A-fail A-fail = refl
  ActiveNotRel (A-mid m1) (A-mid m2)
      with ActiveMiddleNotRel m1 m2
  ... | refl = refl

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{B G}{m : Middle (B ⇒ G)}{g : Ground G}
          → Inert (𝜖 ↷ m , !! {G}{g})
    I-mid : ∀{A B}{m : Middle (A ⇒ B)}
          → InertMiddle m
          → Inert (𝜖 ↷ m , 𝜖)

  InertMiddleNotRel : ∀{A}{c : Middle A} (i1 : InertMiddle c)(i2 : InertMiddle c) → i1 ≡ i2
  InertMiddleNotRel I-cfun I-cfun = refl
  
  InertNotRel : ∀{A}{c : Cast A} (i1 : Inert c)(i2 : Inert c) → i1 ≡ i2
  InertNotRel I-inj I-inj = refl
  InertNotRel (I-mid m1) (I-mid m2)
      with InertMiddleNotRel m1 m2
  ... | refl = refl

  ActiveOrInertMiddle : ∀{A} → (c : Middle A) → ActiveMiddle c ⊎ InertMiddle c
  ActiveOrInertMiddle {.(` _ ⇒ ` _)} (id ι) = inj₁ A-idι
  ActiveOrInertMiddle {.((_ ⇒ _) ⇒ (_ ⇒ _))} (c ↣ d) = inj₂ I-cfun
  ActiveOrInertMiddle {.(_ `× _ ⇒ _ `× _)} (c ×' d) = inj₁ A-cpair
  ActiveOrInertMiddle {.(_ `⊎ _ ⇒ _ `⊎ _)} (c +' d) = inj₁ A-csum

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert {.(⋆ ⇒ ⋆)} id★ = inj₁ A-id★
  ActiveOrInert {A ⇒ D} (𝜖 ↷ m , 𝜖)
      with ActiveOrInertMiddle m
  ... | inj₁ a = inj₁ (A-mid a)
  ... | inj₂ i = inj₂ (I-mid i)
  ActiveOrInert {A ⇒ .⋆} (𝜖 ↷ m , !!) = inj₂ I-inj
  ActiveOrInert {A ⇒ D} (𝜖 ↷ m , (cfail ℓ)) = inj₁ A-fail
  ActiveOrInert {.⋆ ⇒ D} (?? x ↷ m , 𝜖) = inj₁ A-proj
  ActiveOrInert {.⋆ ⇒ .⋆} (?? x ↷ m , !!) = inj₁ A-proj-inj
  ActiveOrInert {.⋆ ⇒ D} (?? x ↷ m , cfail x₁) = inj₁ A-fail

  ActiveNotInertMiddle : ∀ {A} {c : Middle A} → ActiveMiddle c → InertMiddle c → Bot
  ActiveNotInertMiddle A-cpair ()
  ActiveNotInertMiddle A-csum ()
  ActiveNotInertMiddle A-idι ()

  ActiveNotInert : ∀ {A} {c : Cast A} → Active c → ¬ Inert c
  ActiveNotInert (A-mid a) (I-mid i) = ActiveNotInertMiddle a i

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B A' B'}{c : Cast (B ⇒ A)}{d : Cast (A' ⇒ B')}
          → Cross (𝜖 ↷ (c ↣ d) , 𝜖)
    C-pair : ∀{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
          → Cross (𝜖 ↷ (c ×' d) , 𝜖)
    C-sum : ∀{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
          → Cross (𝜖 ↷ (c +' d) , 𝜖)

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         → Cast (A' ⇒ A₁)
  dom (𝜖 ↷ c ↣ d , 𝜖) x = c

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  cod (𝜖 ↷ c ↣ d , 𝜖) x = d

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  fstC (𝜖 ↷ c ×' d , 𝜖) x = c

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  sndC (𝜖 ↷ c ×' d , 𝜖) x = d

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         → Cast (A₁ ⇒ A')
  inlC (𝜖 ↷ c +' d , 𝜖) x = c

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → .(Cross c)
         →  Cast (A₂ ⇒ B')
  inrC (𝜖 ↷ c +' d , 𝜖) x = d

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert {A} {ι} .(𝜖 ↷ _ , 𝜖) (I-mid ())

  idNotInert : ∀ {A} → Atomic A → (c : Cast (A ⇒ A)) → ¬ Inert c
  idNotInert () .(𝜖 ↷ _ ↣ _ , 𝜖) (I-mid I-cfun)

  projNotInert : ∀ {B} → B ≢ ⋆ → (c : Cast (⋆ ⇒ B)) → ¬ Inert c
  projNotInert j id★ = contradiction refl j
  projNotInert j (_ ↷ _ , _) (I-mid ())

  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ (𝜖 ↷ (c ↣ d) , 𝜖) (I-mid (I-cfun{A}{B}{A'}{B'})) =
      ⟨ C-fun , ⟨ A , ⟨ A' , refl ⟩ ⟩ ⟩

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× .(𝜖 ↷ _ , 𝜖) (I-mid ())

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ .(𝜖 ↷ _ , 𝜖) (I-mid ())

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


  import EfficientParamCastAux
  open EfficientParamCastAux pcs

  _⨟_ : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
      → Cast (A ⇒ C)

  _`⨟_ : ∀{A B C} → (c : Middle (A ⇒ B)) → (d : Middle (B ⇒ C))
       → Middle (A ⇒ C)
  (id ι `⨟ id ι) = id ι
  ((c ↣ d) `⨟ (c' ↣ d')) = (c' ⨟ c) ↣ (d ⨟ d')
  ((c ×' d) `⨟ (c' ×' d')) = (c ⨟ c') ×' (d ⨟ d')
  ((c +' d) `⨟ (c' +' d')) = (c ⨟ c') +' (d ⨟ d')

  {-

   The following compares two middle coercions to determine whether
   the target and source types are shallowly consistent.

    Ditch this. -Jeremy

  -}

  _⌣'_ : ∀{A B C D} → Middle (A ⇒ B) → Middle (C ⇒ D)
       → Dec (B ⌣ C)
  id ι ⌣' id ι'
      with base-eq? ι ι'
  ... | yes refl = yes base⌣
  ... | no neq = no (¬⌣ii neq)
  id ι ⌣' (c ↣ d) = no ¬⌣if
  id ι ⌣' (c ×' d) = no ¬⌣ip
  id ι ⌣' (c +' d) = no ¬⌣is
  (c ↣ d₁) ⌣' id ι = no ¬⌣fi
  (c ↣ d₁) ⌣' (c₁ ↣ d) = yes fun⌣
  (c ↣ d₁) ⌣' (c₁ ×' d) = no λ ()
  (c ↣ d₁) ⌣' (c₁ +' d) = no λ ()
  (c ×' d₁) ⌣' id ι = no λ ()
  (c ×' d₁) ⌣' (c₁ ↣ d) = no (λ ())
  (c ×' d₁) ⌣' (c₁ ×' d) = yes pair⌣
  (c ×' d₁) ⌣' (c₁ +' d) = no (λ ())
  (c +' d₁) ⌣' id ι = no (λ ())
  (c +' d₁) ⌣' (c₁ ↣ d) = no (λ ())
  (c +' d₁) ⌣' (c₁ ×' d) = no (λ ())
  (c +' d₁) ⌣' (c₁ +' d) = yes sum⌣

  c ⨟ id★ = c
  id★ ⨟ (p₂ ↷ m₂ , i₂) = (p₂ ↷ m₂ , i₂)
  (p₁ ↷ m₁ , 𝜖) ⨟ (𝜖 ↷ m₂ , i₂) = p₁ ↷ (m₁ `⨟ m₂) , i₂
  (p₁ ↷ m₁ , (!! {G = C}{g = gC})) ⨟ ((?? ℓ) {H = D}{g = gD} ↷ m₂ , i₂)
      with gnd-eq? C D {gC}{gD}
  ... | no C≢D = p₁ ↷ m₁ , cfail ℓ
  ... | yes C≡D rewrite C≡D = p₁ ↷ (m₁ `⨟ m₂) , i₂
  (p₁ ↷ m₁ , cfail ℓ) ⨟ (p₂ ↷ m₂ , i₂) = p₁ ↷ m₁ , cfail ℓ

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (SimpleValue M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id★ {A-id★} =
      M
  applyCast M v (p ↷ m , cfail ℓ) {A-fail} = blame ℓ
  applyCast (cons V W) v (𝜖 ↷ s ×' t , 𝜖) {A-mid A-cpair} =
      cons (V ⟨ s ⟩) (W ⟨ t ⟩)  
  applyCast (inl V) v (𝜖 ↷ s +' t , 𝜖) {A-mid A-csum} = inl (V ⟨ s ⟩)
  applyCast (inr V) v (𝜖 ↷ s +' t , 𝜖) {A-mid A-csum} = inr (V ⟨ t ⟩)
  applyCast ($_ k {f}) (V-const) (𝜖 ↷ id ι , 𝜖) {A-mid A-idι} = $_ k {f}
  applyCast (M ⟨ s ⟩) () ((?? ℓ) {g = g} ↷ m , i) {A-proj} 

  funCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
          → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M v (𝜖 ↷ (c ↣ d) , 𝜖) {I-mid I-cfun} N = (M · N ⟨ c ⟩) ⟨ d ⟩

  compose-height : ∀ {A B C} → (s : Cast (A ⇒ B)) (t : Cast (B ⇒ C))
     → height (s ⨟ t) ≤ (height s) ⊔ (height t)

  compose-height-m : ∀ {A B C} → (m₁ : Middle (A ⇒ B)) (m₂ : Middle (B ⇒ C))
          → height-m (m₁ `⨟ m₂) ≤ height-m m₁ ⊔ height-m m₂

  compose-height s id★ rewrite ⊔-identityʳ (height s) = ≤-refl
  compose-height id★ (p ↷ m , i) = ≤-refl
  compose-height (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , i₂) = compose-height-m m₁ m₂
  compose-height (p₁ ↷ m₁ , !!{G = C}{g = gC})
                 ((?? ℓ){H = D}{g = gD} ↷ m₂ , i₂)
      with gnd-eq? C D {gC}{gD}
  ... | no C≢D = m≤m⊔n (height-m m₁) _
  ... | yes C≡D rewrite C≡D = compose-height-m m₁ m₂
  compose-height (p₁ ↷ m₁ , cfail ℓ) (p₂ ↷ m₂ , i₂) = m≤m⊔n (height-m m₁) _

  compose-height-⊔ : ∀{A B C D E F}(c : Cast (A ⇒ B))(c₁ : Cast (B ⇒ C))
      (d : Cast (D ⇒ E))(d₁ : Cast (E ⇒ F))
    → (IH1 : height (c ⨟ c₁) ≤ height c ⊔ height c₁)
    → (IH2 : height (d ⨟ d₁) ≤ height d ⊔ height d₁)
    → height (c ⨟ c₁) ⊔ height (d ⨟ d₁) ≤
               (height c ⊔ height d) ⊔ (height c₁ ⊔ height d₁)
  compose-height-⊔ c c₁ d d₁ IH1 IH2 =
     begin
          height (c ⨟ c₁) ⊔ height (d ⨟ d₁)             ≤⟨ ⊔-mono-≤ IH1 IH2 ⟩
          (height c ⊔ height c₁) ⊔ (height d ⊔ height d₁) ≤⟨ ≤-reflexive (⊔-assoc (height c) (height c₁) (height d ⊔ height d₁)) ⟩
          height c ⊔ (height c₁ ⊔ (height d ⊔ height d₁)) ≤⟨ ⊔-monoʳ-≤ (height c) (≤-reflexive (sym (⊔-assoc (height c₁) _ _))) ⟩
          height c ⊔ ((height c₁ ⊔ height d) ⊔ height d₁) ≤⟨ ⊔-monoʳ-≤ (height c) (⊔-mono-≤ (≤-reflexive (⊔-comm (height c₁) (height d))) ≤-refl) ⟩
          height c ⊔ ((height d ⊔ height c₁) ⊔ height d₁) ≤⟨ ⊔-monoʳ-≤ (height c) (≤-reflexive (⊔-assoc (height d) _ _)) ⟩
          height c ⊔ (height d ⊔ (height c₁ ⊔ height d₁)) ≤⟨ ≤-reflexive (sym (⊔-assoc (height c) _ _)) ⟩
          (height c ⊔ height d) ⊔ (height c₁ ⊔ height d₁)
     ∎

  compose-height-m (id ι) (id .ι) = ≤-refl
  compose-height-m (c ↣ d) (c₁ ↣ d₁) =
      s≤s G
      where
      IH1 : height (c₁ ⨟ c) ≤ height c₁ ⊔ height c
      IH1 = compose-height c₁ c

      IH2 : height (d ⨟ d₁) ≤ height d ⊔ height d₁
      IH2 = compose-height d d₁

      G : height (c₁ ⨟ c) ⊔ height (d ⨟ d₁) ≤
                (height c ⊔ height d) ⊔ (height c₁ ⊔ height d₁)
      G =
        begin
          height (c₁ ⨟ c) ⊔ height (d ⨟ d₁)             ≤⟨ ⊔-mono-≤ IH1 IH2 ⟩
          (height c₁ ⊔ height c) ⊔ (height d ⊔ height d₁) ≤⟨ ⊔-mono-≤ (≤-reflexive (⊔-comm (height c₁) (height c))) ≤-refl ⟩
          (height c ⊔ height c₁) ⊔ (height d ⊔ height d₁) ≤⟨ ≤-reflexive (⊔-assoc (height c) (height c₁) (height d ⊔ height d₁)) ⟩
          height c ⊔ (height c₁ ⊔ (height d ⊔ height d₁)) ≤⟨ ⊔-monoʳ-≤ (height c) (≤-reflexive (sym (⊔-assoc (height c₁) _ _))) ⟩
          height c ⊔ ((height c₁ ⊔ height d) ⊔ height d₁) ≤⟨ ⊔-monoʳ-≤ (height c) (⊔-mono-≤ (≤-reflexive (⊔-comm (height c₁) (height d))) ≤-refl) ⟩
          height c ⊔ ((height d ⊔ height c₁) ⊔ height d₁) ≤⟨ ⊔-monoʳ-≤ (height c) (≤-reflexive (⊔-assoc (height d) _ _)) ⟩
          height c ⊔ (height d ⊔ (height c₁ ⊔ height d₁)) ≤⟨ ≤-reflexive (sym (⊔-assoc (height c) _ _)) ⟩
          (height c ⊔ height d) ⊔ (height c₁ ⊔ height d₁)
          ∎

  compose-height-m (c ×' d) (c₁ ×' d₁) =
      s≤s (compose-height-⊔ c c₁ d d₁ IH1 IH2)
      where
      IH1 : height (c ⨟ c₁) ≤ height c ⊔ height c₁
      IH1 = compose-height c c₁

      IH2 : height (d ⨟ d₁) ≤ height d ⊔ height d₁
      IH2 = compose-height d d₁
  compose-height-m (c +' d) (c₁ +' d₁) =
      s≤s (compose-height-⊔ c c₁ d d₁ IH1 IH2)
      where
      IH1 : height (c ⨟ c₁) ≤ height c ⊔ height c₁
      IH1 = compose-height c c₁

      IH2 : height (d ⨟ d₁) ≤ height d ⊔ height d₁
      IH2 = compose-height d d₁

  open import CastStructure

  applyCastOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}{a}
          → n ∣ false ⊢ M ok → (v : SimpleValue M)
          → Σ[ m ∈ ℕ ] m ∣ false ⊢ applyCast M v c {a} ok × m ≤ 2 + n
  applyCastOK {c = id★} {n} {A-id★} Mok v =
      ⟨ n , ⟨ Mok , ≤-step (≤-step ≤-refl) ⟩ ⟩
  applyCastOK {M = M}{c = .(?? _) ↷ m , inj} {n} {A-proj} Mok v =
      ⊥-elim (simple⋆ M v refl)
  applyCastOK {M = M}{c = .(?? _) ↷ m , !!{g = gB}} {n} {A-proj-inj} Mok v =
      ⊥-elim (simple⋆ M v refl)
  applyCastOK {c = pr ↷ m , cfail ℓ} {n} {A-fail} Mok v =
      ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩
  applyCastOK {M = cons V W} {c = .𝜖 ↷ .(_ ×' _) , .𝜖} {.0} {A-mid A-cpair}
      (consOK Mok Nok) (V-pair vV vW) =
      let n≤1 = value→ok1 vV Mok in
      let m≤1 = value→ok1 vW Nok in
      ⟨ zero ,
      ⟨ (consOK (castOK Mok (≤-trans n≤1 (s≤s z≤n)))
                (castOK Nok (≤-trans m≤1 (s≤s z≤n)))) ,
        z≤n ⟩ ⟩
  applyCastOK {c = .𝜖 ↷ .(_ +' _) , .𝜖} {n} {A-mid A-csum} (inlOK Mok) (V-inl x)=
      let n≤1 = value→ok1 x Mok in
      ⟨ zero ,
      ⟨ (inlOK (castOK Mok (≤-trans n≤1 (s≤s z≤n)))) ,
        z≤n ⟩ ⟩
  applyCastOK {c = .𝜖 ↷ .(_ +' _) , .𝜖} {n} {A-mid A-csum} (inrOK Mok) (V-inr x)=
      let n≤1 = value→ok1 x Mok in
      ⟨ zero ,
      ⟨ (inrOK (castOK Mok (≤-trans n≤1 (s≤s z≤n)))) ,
        z≤n ⟩ ⟩
  applyCastOK {c = .𝜖 ↷ .(id _) , .𝜖} {n} {A-mid A-idι} Mok V-const =
      ⟨ n , ⟨ Mok , (≤-step (≤-step ≤-refl)) ⟩ ⟩

  ecs : EfficientCastStruct
  ecs = record
             { precast = pcs
             ; applyCast = applyCast
             ; compose = _⨟_
             ; height = height
             ; compose-height = compose-height
             ; applyCastOK = λ{Γ}{A}{B}{M}{c}{n}{a} → applyCastOK{Γ}{A}{B}{M}{c}{n}{a}
             }
  open EfficientCastStruct ecs using (c-height)
  import EfficientParamCasts
  open EfficientParamCasts ecs public

  applyCast-height : ∀{Γ}{A B}{V}{v : SimpleValue {Γ} V}{c : Cast (A ⇒ B)}
        {a : Active c}
      → c-height (applyCast V v c {a}) ≤ c-height V ⊔ height c
  applyCast-height {v = v} {id★} {A-id★} = m≤m⊔n _ _
  applyCast-height {V = V}{v} {(?? ℓ {g = g} ↷ m , inj)} {A-proj} =
      ⊥-elim (simple⋆ V v refl)
  applyCast-height {V = V}{v} {(?? ℓ {g = g} ↷ m , !!{g = g'})} {A-proj-inj} =
      ⊥-elim (simple⋆ V v refl)
  applyCast-height {v = v} {x ↷ x₁ , .(cfail _)} {A-fail} = z≤n
  applyCast-height {V = cons V W} {V-pair vV vW} {.𝜖 ↷ c ×' d , .𝜖}
      {A-mid A-cpair} =
    begin
        (c-height V ⊔ height c) ⊔ (c-height W ⊔ height d)
      ≤⟨ ≤-reflexive (⊔-assoc (c-height V) _ _) ⟩
        c-height V ⊔ (height c ⊔ (c-height W ⊔ height d))
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-reflexive (sym (⊔-assoc (height c) _ _))) ⟩
        c-height V ⊔ ((height c ⊔ c-height W) ⊔ height d)
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoˡ-≤ (height d) (≤-reflexive (⊔-comm (height c) _))) ⟩
        c-height V ⊔ ((c-height W ⊔ height c) ⊔ height d)
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-reflexive (⊔-assoc (c-height W) _ _)) ⟩
        c-height V ⊔ (c-height W ⊔ (height c ⊔ height d))
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height V) _ _)) ⟩
        (c-height V ⊔ c-height W) ⊔ (height c ⊔ height d)
      ≤⟨ ⊔-monoʳ-≤ (c-height V ⊔ c-height W) (≤-step ≤-refl) ⟩ 
        (c-height V ⊔ c-height W) ⊔ suc (height c ⊔ height d)
    ∎ 
  applyCast-height {V = inl V} {V-inl x} {.𝜖 ↷ c +' d , .𝜖} {A-mid A-csum} =
    begin
      c-height V ⊔ height c
    ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-step (m≤m⊔n _ _)) ⟩
      c-height V ⊔ suc (height c ⊔ height d)
    ∎ 
  applyCast-height {V = inr V} {V-inr x} {.𝜖 ↷ c +' d , .𝜖} {A-mid A-csum} =
    begin
      c-height V ⊔ height d
    ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-step (m≤n⊔m _ _)) ⟩
      c-height V ⊔ suc (height c ⊔ height d)
    ∎ 
  applyCast-height {V = $_ x {f}} {v = V-const} {𝜖 ↷ id ι , 𝜖} {A-mid A-idι} =
    ≤-refl


  dom-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))} .{x : Cross c}
       → height (dom c x) ≤ height c
  dom-height {c = 𝜖 ↷ c ↣ d , 𝜖} {x} = ≤-step (m≤m⊔n _ _)

  cod-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))} .{x : Cross c}
       → height (cod c x) ≤ height c
  cod-height {c = 𝜖 ↷ c ↣ d , 𝜖} {x} = ≤-step (m≤n⊔m _ _)

  fst-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)} .{x : Cross c}
       → height (fstC c x) ≤ height c
  fst-height {c = 𝜖 ↷ c ×' d , 𝜖}{x} = ≤-step (m≤m⊔n _ _)

  snd-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)} .{x : Cross c}
       → height (sndC c x) ≤ height c
  snd-height {c = 𝜖 ↷ c ×' d , 𝜖}{x} = ≤-step (m≤n⊔m _ _)

  inlC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)} .{x : Cross c}
       → height (inlC c x) ≤ height c
  inlC-height {c = 𝜖 ↷ c +' d , 𝜖}{x} = ≤-step (m≤m⊔n _ _)

  inrC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)} .{x : Cross c}
       → height (inrC c x) ≤ height c
  inrC-height {c = 𝜖 ↷ c +' d , 𝜖}{x} = ≤-step (m≤n⊔m _ _)

  msize : ∀{A B} (c : Middle (A ⇒ B)) → ℕ
  psize : ∀{A B} (c : Proj (A ⇒ B)) → ℕ
  isize : ∀{A B} (c : Inj (A ⇒ B)) → ℕ
  
  csize : ∀{A B} (c : Cast (A ⇒ B)) → ℕ
  csize id★ = 0
  csize (p ↷ m , i) = 2 + psize p + msize m + isize i
  msize (id ι) = 0
  msize (c ↣ d) = 1 + csize c + csize d
  msize (c ×' d) = 1 + csize c + csize d
  msize (c +' d) = 1 + csize c + csize d
  psize 𝜖 = 0
  psize (?? ℓ) = 1
  isize 𝜖 = 0
  isize !! = 1
  isize (cfail ℓ) = 0

  psize-height : ∀{A B} (c : Proj (A ⇒ B)) →  psize c ≤ 1
  psize-height 𝜖 = z≤n
  psize-height (?? ℓ) = s≤s z≤n
  
  isize-height : ∀{A B} (c : Inj (A ⇒ B)) → isize c ≤ 1
  isize-height 𝜖 = z≤n
  isize-height !! = s≤s z≤n
  isize-height (cfail ℓ) = z≤n
  
  msize-height : ∀{A B} (c : Middle (A ⇒ B)) → 9 + msize c ≤ 9 * pow2 (height-m c)
  csize-height : ∀{A B} (c : Cast (A ⇒ B)) → 5 + csize c ≤ 9 * pow2 (height c)
  
  csize-height id★ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  csize-height (p ↷ m , i) =
    let IH = msize-height m in
    begin
      5 + csize (p ↷ m , i)
    ≤⟨ ≤-reflexive refl ⟩
      ((7 + psize p) + msize m) + isize i
    ≤⟨ +-mono-≤ (+-mono-≤ {u = msize m} (+-mono-≤ ≤-refl (psize-height p)) ≤-refl) (isize-height i)  ⟩
      (8 + msize m) + 1
    ≤⟨ ≤-reflexive (+-comm _ 1) ⟩
      9 + msize m
    ≤⟨ msize-height m ⟩
      9 * pow2 (height-m m)
    ≤⟨ ≤-reflexive refl ⟩
      9 * pow2 (height (p ↷ m , i))
    ∎
  msize-height (id ι) = ≤-refl
  msize-height (c ↣ d) =
    let IH1 = csize-height c in
    let IH2 = csize-height d in
    begin
        (10 + csize c) + csize d
      ≤⟨ ≤-reflexive (solve 2 (λ x y → ((con 10 :+ x) :+ y) := (con 5 :+ x) :+ (con 5 :+ y)) refl (csize c) (csize d))  ⟩
        (5 + csize c) + (5 + csize d)
      ≤⟨ +-mono-≤ IH1 IH2 ⟩
        9 * pow2 (height c) + 9 * pow2 (height d)
      ≤⟨ +-mono-≤ (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤m⊔n (height c) (height d))))
                  (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤n⊔m (height c) (height d)))) ⟩
        9 * pow2 (height c ⊔ height d) + 9 * pow2 (height c ⊔ height d)
      ≤⟨ ≤-reflexive (solve 1 (λ x → con 9 :* x :+ con 9 :* x := con 9 :* (con 2 :* x)) refl (pow2 (height c ⊔ height d)) ) ⟩
        9 * (2 * pow2 (height c ⊔ height d))
      ≤⟨ ≤-reflexive refl ⟩
        9 * pow2 (suc ((height c) ⊔ (height d)))
    ∎
    where
    open +-*-Solver
  msize-height (c ×' d) =
    let IH1 = csize-height c in
    let IH2 = csize-height d in
    begin
        (10 + csize c) + csize d
      ≤⟨ ≤-reflexive (solve 2 (λ x y → ((con 10 :+ x) :+ y) := (con 5 :+ x) :+ (con 5 :+ y)) refl (csize c) (csize d))  ⟩
        (5 + csize c) + (5 + csize d)
      ≤⟨ +-mono-≤ IH1 IH2 ⟩
        9 * pow2 (height c) + 9 * pow2 (height d)
      ≤⟨ +-mono-≤ (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤m⊔n (height c) (height d))))
                  (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤n⊔m (height c) (height d)))) ⟩
        9 * pow2 (height c ⊔ height d) + 9 * pow2 (height c ⊔ height d)
      ≤⟨ ≤-reflexive (solve 1 (λ x → con 9 :* x :+ con 9 :* x := con 9 :* (con 2 :* x)) refl (pow2 (height c ⊔ height d)) ) ⟩
        9 * (2 * pow2 (height c ⊔ height d))
      ≤⟨ ≤-reflexive refl ⟩
        9 * pow2 (suc ((height c) ⊔ (height d)))
    ∎
    where
    open +-*-Solver
  msize-height (c +' d) =
    let IH1 = csize-height c in
    let IH2 = csize-height d in
    begin
        (10 + csize c) + csize d
      ≤⟨ ≤-reflexive (solve 2 (λ x y → ((con 10 :+ x) :+ y) := (con 5 :+ x) :+ (con 5 :+ y)) refl (csize c) (csize d))  ⟩
        (5 + csize c) + (5 + csize d)
      ≤⟨ +-mono-≤ IH1 IH2 ⟩
        9 * pow2 (height c) + 9 * pow2 (height d)
      ≤⟨ +-mono-≤ (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤m⊔n (height c) (height d))))
                  (*-monoʳ-≤ 9 (pow2-mono-≤ (m≤n⊔m (height c) (height d)))) ⟩
        9 * pow2 (height c ⊔ height d) + 9 * pow2 (height c ⊔ height d)
      ≤⟨ ≤-reflexive (solve 1 (λ x → con 9 :* x :+ con 9 :* x := con 9 :* (con 2 :* x)) refl (pow2 (height c ⊔ height d)) ) ⟩
        9 * (2 * pow2 (height c ⊔ height d))
      ≤⟨ ≤-reflexive refl ⟩
        9 * pow2 (suc ((height c) ⊔ (height d)))
    ∎
    where
    open +-*-Solver

  ecsh : EfficientCastStructHeight
  ecsh = record
              { effcast = ecs
              ; applyCast-height = (λ {Γ}{A}{B}{V}{v}{c}{a} → applyCast-height{Γ}{A}{B}{V}{v}{c}{a})
              ; dom-height = (λ {A}{B}{C}{D}{c}{x} → dom-height{A}{B}{C}{D}{c}{x})
              ; cod-height = (λ {A}{B}{C}{D}{c}{x} → cod-height{A}{B}{C}{D}{c}{x})
              ; fst-height = (λ {A}{B}{C}{D}{c}{x} → fst-height{A}{B}{C}{D}{c}{x})
              ; snd-height = (λ {A}{B}{C}{D}{c}{x} → snd-height{A}{B}{C}{D}{c}{x})
              ; inlC-height = (λ {A}{B}{C}{D}{c}{x} → inlC-height{A}{B}{C}{D}{c}{x})
              ; inrC-height = (λ {A}{B}{C}{D}{c}{x} → inrC-height{A}{B}{C}{D}{c}{x})
              ; size = csize
              ; size-height = ⟨ 5 , ⟨ 9 , ⟨ s≤s z≤n , (λ {A}{B} c → csize-height c) ⟩ ⟩ ⟩
              }

  import PreserveHeight
  module PH = PreserveHeight ecsh

  preserve-height : ∀ {Γ A} {M M′ : Γ ⊢ A} {ctx : ReductionCtx}
       → ctx / M —→ M′ → c-height M′ ≤ c-height M
  preserve-height M—→M′ = PH.preserve-height M—→M′


  import SpaceEfficient
  module SE = SpaceEfficient ecs

  preserve-ok : ∀{Γ A}{M M′ : Γ ⊢ A}{ctx : ReductionCtx}{n}
          → n ∣ false ⊢ M ok  →  ctx / M —→ M′
          → Σ[ m ∈ ℕ ] m ∣ false ⊢ M′ ok × m ≤ 2 + n
  preserve-ok Mok M—→M′ = SE.preserve-ok Mok M—→M′

  module EC = SE.EfficientCompile mkcast

  open import GTLC

  compile-efficient : ∀{Γ A} (M : Term) (d : Γ ⊢G M ⦂ A) (ul : Bool)
      → Σ[ k ∈ ℕ ] k ∣ ul ⊢ (Compile.compile M d) ok × k ≤ 1
  compile-efficient d ul = EC.compile-efficient d ul

  module ST = PH.SpaceTheorem mkcast
  open PH using (real-size)
  open GTLC2CCOrig Cast mkcast using (compile)

  space-consumption : ∀{Γ M A}  (d : Γ ⊢G M ⦂ A)
    → Σ[ c1 ∈ ℕ ] Σ[ c2 ∈ ℕ ] ∀ (M' : Γ ⊢ A) {ctx}
    → (ctx / (compile M d) —↠ M')
    → real-size M' ≤ c1 + c2 * ideal-size M'
  space-consumption {Γ}{M}{A} d = ST.space-consumption d

  data PreType : Type → Set where
    P-Base : ∀{ι} → PreType (` ι)
    P-Fun : ∀{A B} → PreType (A ⇒ B)
    P-Pair : ∀{A B} → PreType (A `× B)
    P-Sum : ∀{A B} → PreType (A `⊎ B)

  pre? : (A : Type) → Dec (PreType A)
  pre? ⋆ = no (λ ())
  pre? (` ι) = yes P-Base
  pre? (A ⇒ B) = yes P-Fun
  pre? (A `× B) = yes P-Pair
  pre? (A `⊎ B) = yes P-Sum

  not-pre-unk : ∀{A} {np : ¬ PreType A} → A ≡ ⋆
  not-pre-unk {⋆} {np} = refl
  not-pre-unk {` ι} {np} = ⊥-elim (contradiction P-Base np)
  not-pre-unk {A ⇒ B} {np} = ⊥-elim (contradiction P-Fun np)
  not-pre-unk {A `× B} {np} = ⊥-elim (contradiction P-Pair np)
  not-pre-unk {A `⊎ B} {np} = ⊥-elim (contradiction P-Sum np)

  make-id : (A : Type) → Cast (A ⇒ A)

  make-id-p : (A : Type) → {p : PreType A} → Middle (A ⇒ A)
  make-id-p (` ι) {P-Base} = id ι
  make-id-p (A ⇒ B) {P-Fun} = make-id A ↣ make-id B
  make-id-p (A `× B) {P-Pair} = make-id A ×' make-id B
  make-id-p (A `⊎ B) {P-Sum} = make-id A +' make-id B

  make-id A
      with pre? A
  ... | yes p = 𝜖 ↷ make-id-p A {p} , 𝜖
  ... | no np rewrite not-pre-unk {A}{np} = id★

  right-id : ∀{A B : Type}{c : Cast (A ⇒ B)}
           → c ⨟ make-id B ≡ c
  left-id : ∀{A B : Type}{c : Cast (A ⇒ B)}
           → make-id A ⨟ c ≡ c

  right-id-m-p : ∀{A B : Type}{m : Middle (A ⇒ B)} {p : PreType B}
           → m `⨟ make-id-p B {p} ≡ m
  right-id-m-p {.(` ι)} {` ι} {id .ι} {P-Base} = refl
  right-id-m-p {A ⇒ A'} {B ⇒ C} {c ↣ d} {P-Fun}
      rewrite left-id {B}{A} {c} | right-id {A'}{C}{d} = refl
  right-id-m-p {A `× A'} {B `× C} {c ×' d} {P-Pair}
      rewrite right-id {A}{B} {c} | right-id {A'}{C}{d} = refl
  right-id-m-p {A `⊎ A'} {B `⊎ C} {c +' d} {P-Sum}
      rewrite right-id {A}{B} {c} | right-id {A'}{C}{d} = refl

  right-id-p : ∀{A B : Type}{c : Cast (A ⇒ B)} {p : PreType B}
           → c ⨟ (𝜖 ↷ make-id-p B {p} , 𝜖) ≡ c
  right-id-p {A} {` ι} {_↷_,_ {B = B} p₁ m₁ 𝜖} {P-Base}
      rewrite right-id-m-p {B}{` ι}{m₁}{P-Base} = refl
  right-id-p {A} {` ι} {p₁ ↷ m₁ , cfail ℓ} {P-Base} = refl
  right-id-p {A} {B ⇒ C} {_↷_,_ {B = B₁ ⇒ B₂} p₁ (c ↣ d) 𝜖} {P-Fun}
      rewrite left-id {B}{B₁}{c} | right-id {B₂}{C}{d} = refl
  right-id-p {A} {B ⇒ C} {p₁ ↷ m , cfail ℓ} {P-Fun} = refl
  right-id-p {A} {B `× C} {_↷_,_ {B = B₁ `× B₂} p₁ (c ×' d) 𝜖} {P-Pair}
      rewrite right-id {B₁}{B}{c} | right-id {B₂}{C}{d} = refl
  right-id-p {A} {B `× C} {p₁ ↷ m₁ , cfail ℓ} {P-Pair} = refl
  right-id-p {A} {B `⊎ C} {_↷_,_ {B = B₁ `⊎ B₂} p₁ (c +' d) 𝜖} {P-Sum}
      rewrite right-id {B₁}{B}{c} | right-id {B₂}{C}{d} = refl
  right-id-p {A} {B `⊎ C} {p₁ ↷ m₁ , cfail ℓ} {P-Sum} = refl

  right-id {A} {⋆} {c} = refl
  right-id {A} {` ι} {c} = right-id-p
  right-id {A} {B ⇒ C} {c} = right-id-p
  right-id {A} {B `× C} {c} = right-id-p
  right-id {A} {B `⊎ C} {c} = right-id-p
{-
      with pre? B
  ... | yes p = right-id-p {A}{B}{c}{p}
  ... | no np =
        let x = not-pre-unk {B}{np}  in
        {!!}
-}

  left-id-m-p : ∀{A B : Type}{m : Middle (A ⇒ B)} {p : PreType A}
           → make-id-p A {p} `⨟ m ≡ m
  left-id-m-p {.(` ι)} {` ι} {id .ι} {P-Base} = refl
  left-id-m-p {A ⇒ A'} {B ⇒ C} {c ↣ d} {P-Fun}
      rewrite right-id {B}{A} {c} | left-id {A'}{C}{d} = refl
  left-id-m-p {A `× A'} {B `× C} {c ×' d} {P-Pair}
      rewrite left-id {A}{B} {c} | left-id {A'}{C}{d} = refl
  left-id-m-p {A `⊎ A'} {B `⊎ C} {c +' d} {P-Sum}
      rewrite left-id {A}{B} {c} | left-id {A'}{C}{d} = refl

  left-id-p : ∀{A B : Type}{c : Cast (A ⇒ B)} {p : PreType A}
           → (𝜖 ↷ make-id-p A {p} , 𝜖) ⨟ c ≡ c
  left-id-p {` ι} {B} {_↷_,_ {C = C} 𝜖 m₁ i₁} {P-Base}
     rewrite left-id-m-p {` ι}{C}{m₁}{P-Base} = refl
  left-id-p {A ⇒ C} {B} {_↷_,_ {C = D ⇒ E} 𝜖 (c ↣ d) i₁} {P-Fun}
     rewrite right-id {D}{A}{c} | left-id {C}{E}{d} = refl
  left-id-p {A `× C} {B} {_↷_,_ {C = D `× E} 𝜖 (c ×' d) i₁} {P-Pair}
     rewrite left-id {A}{D}{c} | left-id {C}{E}{d} = refl
  left-id-p {A `⊎ C} {B} {_↷_,_ {C = D `⊎ E} 𝜖 (c +' d) i₁} {P-Sum}
     rewrite left-id {A}{D}{c} | left-id {C}{E}{d} = refl

  left-id {⋆} {.⋆} {id★}
      with pre? ⋆
  ... | yes p = refl
  ... | no np = refl
  left-id {⋆} {B} {x ↷ x₁ , x₂} = refl
  left-id {` ι} {B} {c} = left-id-p
  left-id {A ⇒ C} {B} {c} = left-id-p
  left-id {A `× C} {B} {c} = left-id-p
  left-id {A `⊎ C} {B} {c} = left-id-p

  left-id★ : ∀{B} (c : Cast (⋆ ⇒ B))
           → id★ ⨟ c ≡ c
  left-id★ {B} c = left-id {⋆}{B}{c}

{-
  todo: update me to match new definition using ground equality -Jeremy

  assoc : ∀{A B C D} (c₁ : Cast (A ⇒ B)) → (c₂ : Cast (B ⇒ C))
        → (c₃ : Cast (C ⇒ D))
        → (c₁ ⨟ c₂) ⨟ c₃ ≡ c₁ ⨟ (c₂ ⨟ c₃)


  `assoc : ∀{A B C D} (m₁ : Middle (A ⇒ B)) → (m₂ : Middle (B ⇒ C))
         → (m₃ : Middle (C ⇒ D))
         → (m₁ `⨟ m₂) `⨟ m₃ ≡ m₁ `⨟ (m₂ `⨟ m₃)
  `assoc (id .ι) (id ι) (id .ι) = refl
  `assoc (c₁ ↣ d₁) (c ↣ d) (c₂ ↣ d₂)
      rewrite assoc c₂ c c₁ | assoc d₁ d d₂ = refl
  `assoc (c₁ ×' d₁) (c ×' d) (c₂ ×' d₂)
      rewrite assoc c₁ c c₂ | assoc d₁ d d₂ = refl
  `assoc (c₁ +' d₁) (c +' d) (c₂ +' d₂)
      rewrite assoc c₁ c c₂ | assoc d₁ d d₂ = refl

  assoc c₁ id★ c₃ rewrite left-id★ c₃ = refl
  assoc (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃)
      rewrite `assoc m₁ m₂ m₃ = refl
  assoc (p₁ ↷ m₁ , cfail ℓ) (𝜖 ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃) = refl
  assoc (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , !!) id★ = refl
  assoc {A} {B} {.⋆} {D} (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , !!{G = G}{g = g1}) ((?? ℓ){H = H}{g = g2} ↷ m₃ , i₃)
      with (m₁ `⨟ m₂) ⌣' m₃
  ... | no m123
      with gnd-eq? G H {g1}{g2}
  ... | no G≢H = refl
  ... | yes refl = ⊥-elim (contradiction refl m123)
  assoc {A} {B} {.⋆} {D} (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , !!{g = g1}) ((?? ℓ){g = g2} ↷ m₃ , i₃)
      | yes m123
      with consis-ground-eq m123 g1 g2
  ... | refl
      with m₂ ⌣' m₃
  ... | no m23 = ⊥-elim (contradiction m123 m23)
  ... | yes m23
      with consis-ground-eq m23 g1 g2
  ... | refl rewrite `assoc m₁ m₂ m₃ = refl
  assoc (p₁ ↷ m₁ , cfail ℓ) (𝜖 ↷ m₂ , !!) id★ = refl
  assoc (p₁ ↷ m₁ , cfail ℓ) (𝜖 ↷ m₂ , (!!{g = g1})) ((?? ℓ'){g = g2} ↷ m₃ , i₃)
      with m₂ ⌣' m₃
  ... | no m23 = refl
  ... | yes m23
      with consis-ground-eq m23 g1 g2
  ... | refl = refl
  assoc c₁ (𝜖 ↷ m₂ , cfail ℓ) id★ = refl
  assoc (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , cfail ℓ) (p₃ ↷ m₃ , i₃) = refl
  assoc (p₁ ↷ m₁ , cfail ℓ') (𝜖 ↷ m₂ , cfail ℓ) (p₃ ↷ m₃ , i₃) = refl
  assoc {.⋆} {.⋆} {C} {D} id★ ((?? ℓ){g = g} ↷ m₂ , i₂) c₃
      rewrite left-id★ (((?? ℓ){g = g} ↷ m₂ , i₂) ⨟ c₃) = refl
  assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , i₂) id★ = refl
  assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃)
      with m₁ ⌣' m₂
  ... | no m12
         with m₁ ⌣' (m₂ `⨟ m₃)
  ...    | no m123 = refl
  ...    | yes m123
         with consis-ground-eq m123 g1 g2
  ...    | refl = ⊥-elim (contradiction m123 m12)
  assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃)
      | yes m12
      with consis-ground-eq m12 g1 g2
  ... | refl
       with m₁ ⌣' (m₂ `⨟ m₃)
  ...    | no m123 = ⊥-elim (contradiction m12 m123)
  ...    | yes m123
         with consis-ground-eq m123 g1 g2
  ...    | refl rewrite `assoc m₁ m₂ m₃ = refl
  assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , cfail ℓ') (𝜖 ↷ m₃ , i₃)
      with m₁ ⌣' m₂
  ... | no m12 = refl
  ... | yes m12
      with consis-ground-eq m12 g1 g2
  ... | refl = refl
  assoc (p₁ ↷ m₁ , !! {g = g1})
        (?? ℓ {g = g2} ↷ m₂ , !! {g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
      with m₁ ⌣' m₂
  ... | no m12
         with m₂ ⌣' m₃
  ...    | no m23
           with m₁ ⌣' m₂ {- need to repeat the with, weird! -}
  ...      | no m12' = refl
  ...      | yes m12'
           with consis-ground-eq m12' g1 g2
  ...      | refl = ⊥-elim (contradiction m12' m12)

  assoc (p₁ ↷ m₁ , !! {g = g1})
        (?? ℓ {g = g2} ↷ m₂ , !! {g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
      | no m12 | yes m23
            with consis-ground-eq m23 g3 g4
  ...       | refl
               with m₁ ⌣' (m₂ `⨟ m₃)
  ...          | no m123 = refl
  ...          | yes m123
                  with consis-ground-eq m123 g1 g2
  ...             | refl = ⊥-elim (contradiction m123 m12)
  assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , !!{g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
      | yes m12
      with consis-ground-eq m12 g1 g2
  ... | refl
      with (m₁ `⨟ m₂) ⌣' m₃
  ... | no m123
      with m₂ ⌣' m₃
  ... | no m23
      with m₁ ⌣' m₂ {- weird repetition needed -}
  ... | no m12' = ⊥-elim (contradiction m12 m12')
  ... | yes m12'
      with consis-ground-eq m12' g1 g2
  ... | refl = refl
  assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , !!{g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
      | yes m12 | refl | no m123 | yes m23
      with consis-ground-eq m23 g3 g4
  ... | refl
      with m₁ ⌣' (m₂ `⨟ m₃)
  ... | no m123' = ⊥-elim (contradiction m23 m123)
  ... | yes m123'
      with consis-ground-eq m123' g1 g2
  ... | refl = ⊥-elim (contradiction m23 m123)
  assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , !!{g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
      | yes m12 | refl | yes m123
      with consis-ground-eq m123 g3 g4
  ... | refl
      with m₂ ⌣' m₃
  ... | no m23 = ⊥-elim (contradiction m123 m23)
  ... | yes m23
      with consis-ground-eq m23 g3 g4
  ... | refl
      with m₁ ⌣' (m₂ `⨟ m₃)
  ... | no m123' = ⊥-elim (contradiction m12 m123')
  ... | yes m123'
      with consis-ground-eq m123' g1 g2
  ... | refl rewrite `assoc m₁ m₂ m₃ = refl
  assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , cfail ℓ'') (?? ℓ' ↷ m₃ , i₃)
      with m₁ ⌣' m₂
  ... | no m12 = refl
  ... | yes m12
      with consis-ground-eq m12 g1 g2
  ... | refl = refl
  assoc (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , i₂) id★ = refl
  assoc (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃) = refl
  assoc (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , cfail x) (𝜖 ↷ m₃ , i₃) = refl
  assoc (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , !!{g = g2}) ((?? ℓ''){g = g3} ↷ m₃ , i₃)
      with m₂ ⌣' m₃
  ... | no m23 = refl
  ... | yes m23
      with consis-ground-eq m23 g2 g3
  ... | refl = refl
  assoc {A} {.⋆} {.⋆} {D} (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , cfail ℓ''') (?? ℓ'' ↷ m₃ , i₃) = refl
-}

  cast-id : ∀ (A : Type) → (l : Label)  → (c : A ~ A)
          → coerce A A {c} l ≡ make-id A
  cast-id ⋆ l unk~L = refl
  cast-id ⋆ l unk~R = refl
  cast-id (` ι) l base~ = refl
  cast-id (A ⇒ B) l (fun~ c d)
      rewrite (cast-id A l c) | cast-id B l d = refl
  cast-id (A `× B) l (pair~ c d)
      rewrite (cast-id A l c) | cast-id B l d = refl
  cast-id (A `⊎ B) l (sum~ c d)
      rewrite (cast-id A l c) | cast-id B l d = refl
