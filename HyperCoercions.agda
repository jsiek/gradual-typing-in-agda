{-

  

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
    ??_ : ∀{H : Type} {g : Ground H} → Label → Proj (⋆ ⇒ H)

  data Middle where
    idι : ∀ {ι : Base} → Middle ((` ι) ⇒ (` ι))
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
  ...     | yes g = (??_ {B}{g} ℓ) ↷ (coerce-from-gnd B B {g}{Refl~}{neq} ℓ) , 𝜖
  ...     | no ng with ground B {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ =
               (??_ {G}{g} ℓ) ↷ (coerce-from-gnd G B {g}{Sym~ c}{neq} ℓ) , 𝜖

  coerce-to-gnd .⋆ B {g} {unk~L} {neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd .(` _) .(` _) {g} {base~} {neq} ℓ = idι
  coerce-to-gnd (A ⇒ B) (⋆ ⇒ ⋆) {G-Fun} {fun~ c d} {neq} ℓ =
     (coerce-from⋆ A ℓ) ↣ (coerce-to⋆ B ℓ)
  coerce-to-gnd (A `× B) (⋆ `× ⋆) {G-Pair} {pair~ c d} {neq} ℓ =
     (coerce-to⋆ A ℓ) ×' (coerce-to⋆ B ℓ)
  coerce-to-gnd (A `⊎ B) (⋆ `⊎ ⋆) {G-Sum} {sum~ c d} {neq} ℓ =
     (coerce-to⋆ A ℓ) +' (coerce-to⋆ B ℓ)

  coerce-from-gnd A .⋆ {g} {unk~R} {neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .(` _) .(` _) {g} {base~} {neq} ℓ = idι
  coerce-from-gnd (⋆ ⇒ ⋆) (A ⇒ B) {G-Fun} {fun~ c d} {neq} ℓ =
     (coerce-to⋆ A ℓ) ↣ (coerce-from⋆ B ℓ)
  coerce-from-gnd (⋆ `× ⋆) (A `× B) {G-Pair} {pair~ c d} {neq} ℓ =
     (coerce-from⋆ A ℓ) ×' (coerce-from⋆ B ℓ)
  coerce-from-gnd (⋆ `⊎ ⋆) (A `⊎ B) {G-Sum} {sum~ c d} {neq} ℓ =
     (coerce-from⋆ A ℓ) +' (coerce-from⋆ B ℓ)

  coerce .⋆ B {unk~L} ℓ = coerce-from⋆ B ℓ
  coerce A .⋆ {unk~R} ℓ = coerce-to⋆ A ℓ
  coerce (` ι) (` ι) {base~} ℓ = 𝜖 ↷ idι , 𝜖
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
    A-idι : ∀{B}
          → ActiveMiddle (idι {B})

  data Active : ∀ {A} → Cast A → Set where
    A-id★ : Active id★
    A-proj : ∀{A B C}{ℓ}{g : Ground A}{m : Middle (A ⇒ B)}{i : Inj (B ⇒ C)}
           → Active ((??_ {A}{g} ℓ) ↷ m , i)  
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
  ActiveOrInertMiddle {.(` _ ⇒ ` _)} idι = inj₁ A-idι
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
  (idι `⨟ idι) = idι
  ((c ↣ d) `⨟ (c' ↣ d')) = (c' ⨟ c) ↣ (d ⨟ d')
  ((c ×' d) `⨟ (c' ×' d')) = (c ⨟ c') ×' (d ⨟ d')
  ((c +' d) `⨟ (c' +' d')) = (c ⨟ c') +' (d ⨟ d')

  c ⨟ id★ = c
  id★ ⨟ (p₂ ↷ m₂ , i₂) = (p₂ ↷ m₂ , i₂)
  (p₁ ↷ m₁ , 𝜖) ⨟ (𝜖 ↷ m₂ , i₂) = p₁ ↷ (m₁ `⨟ m₂) , i₂
  (p₁ ↷ m₁ , cfail ℓ) ⨟ (𝜖 ↷ m₂ , i₂) = p₁ ↷ m₁ , cfail ℓ
  (_↷_,_ {A}{B}{C}{⋆} p₁ m₁ (!! {C}{gC}))
    ⨟ (_↷_,_ {⋆}{D}{E}{F} (??_ {D}{gD} ℓ) m₂ i₂)
      with gnd-eq? C D {gC}{gD}
  ... | yes C≡D rewrite C≡D = p₁ ↷ (m₁ `⨟ m₂) , i₂
  ... | no C≢D = p₁ ↷ m₁ , cfail ℓ
  (p₁ ↷ m₁ , cfail ℓ) ⨟ ((?? ℓ₂) ↷ m₂ , i₂) = p₁ ↷ m₁ , cfail ℓ

