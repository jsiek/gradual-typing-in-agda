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
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
      renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
     
  open import Types
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


  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
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
     𝜖 ↷ (coerce C A {Sym~ c} ℓ ↣ coerce B D {d} ℓ) , 𝜖
  coerce (A `× B) (C `× D) {pair~ c d} ℓ =
     𝜖 ↷ (coerce A C {c} ℓ ×' coerce B D {d} ℓ) , 𝜖
  coerce (A `⊎ B) (C `⊎ D) {sum~ c d} ℓ =
     𝜖 ↷ (coerce A C {c} ℓ +' coerce B D {d} ℓ) , 𝜖

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → coerce A B {c} ℓ)

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
    A-proj : ∀{A B C}{ℓ}{g : Ground A}{m : Middle (A ⇒ B)}{i : Inj (B ⇒ C)}
           → Active ((?? ℓ) {A}{g} ↷ m , i)  
    A-fail : ∀{A B C D}{ℓ}{p : Proj (A ⇒ B)}{m : Middle (B ⇒ C)}
           → Active (p ↷ m , cfail {C} {D} ℓ)  
    A-mid : ∀{A B}{m : Middle (A ⇒ B)}
          → ActiveMiddle m
          → Active (𝜖 ↷ m , 𝜖)
          
  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{B G}{m : Middle (B ⇒ G)}{g : Ground G}
          → Inert (𝜖 ↷ m , !! {G}{g})  
    I-mid : ∀{A B}{m : Middle (A ⇒ B)}
          → InertMiddle m
          → Inert (𝜖 ↷ m , 𝜖)  

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
  ActiveOrInert {.⋆ ⇒ D} ((?? x) ↷ m , i) = inj₁ A-proj

  import EfficientParamCasts
  module EPCR = EfficientParamCasts Cast Inert Active ActiveOrInert
  open EPCR

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
  (p₁ ↷ m₁ , (!! {g = gC})) ⨟ ((?? ℓ) {g = gD} ↷ m₂ , i₂)
      with m₁ ⌣' m₂
  ... | no C⌣̸D = p₁ ↷ m₁ , cfail ℓ
  ... | yes C⌣D rewrite (consis-ground-eq C⌣D gC gD) =
        p₁ ↷ (m₁ `⨟ m₂) , i₂
  (p₁ ↷ m₁ , cfail ℓ) ⨟ (p₂ ↷ m₂ , i₂) = p₁ ↷ m₁ , cfail ℓ

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id★ {a} =
      M
  applyCast M v (𝜖 ↷ m , cfail ℓ) {A-fail} =
      blame ℓ
  applyCast M v (𝜖 ↷ (c ×' d) , 𝜖) {A-mid A-cpair} =
      cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast M v (𝜖 ↷ (c +' d) , 𝜖) {A-mid A-csum} =
    let l = inl ((` Z) ⟨ c ⟩) in let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ l) (ƛ r)
  applyCast M v (𝜖 ↷ id ι , 𝜖) {A-mid A-idι} = M
  applyCast M v ((?? ℓ) {g = g} ↷ m , i) {a}
      with EPCR.canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ i' , ⟨ meq , _ ⟩ ⟩ ⟩ ⟩ ⟩ rewrite meq =
        M' ⟨ c ⨟ ((?? ℓ) {g = g} ↷ m , i) ⟩

  funCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
          → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M v (𝜖 ↷ (c ↣ d) , 𝜖) {I-mid I-cfun} N = (M · N ⟨ c ⟩) ⟨ d ⟩
  
  funSrc : ∀{A A' B' Γ}
         → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → (M : Γ ⊢ A) → SimpleValue M
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc (𝜖 ↷ (_↣_ {A}{B}{A'}{B'} c d) , 𝜖) (I-mid I-cfun) M v =
      ⟨ A , ⟨ A' , refl ⟩ ⟩

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁)
  dom (𝜖 ↷ c ↣ d , 𝜖) (I-mid I-cfun) = c
  
  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  cod (𝜖 ↷ c ↣ d , 𝜖) (I-mid I-cfun) = d
  
  fstCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
          → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M vM (𝜖 ↷ _ , 𝜖) {I-mid ()}
  
  sndCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
          → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M vM (𝜖 ↷ _ , 𝜖) {I-mid ()}

  caseCast : ∀ {Γ A A' B' C} → (L : Γ ⊢ A) → SimpleValue L
             → (c : Cast (A ⇒ (A' `⊎ B')))
             → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L vL (𝜖 ↷ _ , 𝜖) {I-mid ()} M N
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → A ≢ ⋆ → ¬ Inert c
  baseNotInert {A} {ι} .(𝜖 ↷ _ , 𝜖) nd (I-mid ())

  module Red = EPCR.Reduction applyCast funSrc dom cod fstCast sndCast caseCast
                  baseNotInert (_⨟_)
  open Red

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
  assoc {A} {B} {.⋆} {D} (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , !!{g = g1}) ((?? ℓ){g = g2} ↷ m₃ , i₃)
      with (m₁ `⨟ m₂) ⌣' m₃
  ... | no m123
      with m₂ ⌣' m₃
  ... | no m23 = refl
  ... | yes m23
      with consis-ground-eq m23 g1 g2
  ... | refl = ⊥-elim (contradiction m23 m123)
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


  cast-id : ∀ (A : Type) → (l : Label)  → (c : A ~ A)
          → coerce A A {c} l ≡ make-id A
  cast-id ⋆ l unk~L = refl
  cast-id ⋆ l unk~R = refl
  cast-id (` ι) l base~ = refl
  cast-id (A ⇒ B) l (fun~ c d)
      rewrite (cast-id A l (Sym~ c)) | cast-id B l d = refl
  cast-id (A `× B) l (pair~ c d)
      rewrite (cast-id A l c) | cast-id B l d = refl
  cast-id (A `⊎ B) l (sum~ c d)
      rewrite (cast-id A l c) | cast-id B l d = refl
