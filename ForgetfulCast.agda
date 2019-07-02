module ForgetfulCast where

  open import Data.Nat
  open import Data.Bool
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)

  data Cast : Type → Set where
    _⇒_ : (A : Type) → (B : Type) → {c : A ~ B } → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  {-

    Not sure about the inert/active categorization. -Jeremy

  -}

  data Inert : ∀ {A} → Cast A → Set where
    inert : ∀{A} → A ≢ ⋆ → (c : Cast (A ⇒ ⋆)) → Inert c

  data Active : ∀ {A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c
    activeFun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c    

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert ((.⋆ ⇒ B) {unk~L}) with eq-unk B
  ... | yes eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (⋆ ⇒ ⋆))
  ... | no neq = inj₁ (activeProj (⋆ ⇒ B) neq)
  ActiveOrInert ((A ⇒ .⋆) {unk~R}) with eq-unk A
  ... | yes eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (⋆ ⇒ ⋆))
  ... | no neq = inj₂ (inert neq (A ⇒ ⋆))
  ActiveOrInert (((` ι)  ⇒ (` ι)) {base~}) =
      inj₁ (activeId{` ι}{A-Base} ((` ι) ⇒ (` ι)))
  ActiveOrInert (((A₁ ⇒ A₂) ⇒ (B₁ ⇒ B₂)) {fun~ c d}) =
      inj₁ (activeFun ((A₁ ⇒ A₂) ⇒ (B₁ ⇒ B₂)))
  ActiveOrInert (((A₁ `× A₂) ⇒ (B₁ `× B₂)) {pair~ c d}) =
      inj₁ (activePair ((A₁ `× A₂) ⇒ (B₁ `× B₂)))
  ActiveOrInert (((A₁ `⊎ A₂) ⇒ (B₁ `⊎ B₂)) {sum~ c d}) =
      inj₁ (activeSum ((A₁ `⊎ A₂) ⇒ (B₁ `⊎ B₂)))

  import EfficientParamCasts
  module PCR = EfficientParamCasts Cast Inert Active ActiveOrInert
  open PCR
  
{-
  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR
-}

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  {- Id -}
  applyCast {Γ} {A} {.A} M v ((A ⇒ .A) {c}) {activeId .(A ⇒ A)} = M
  {- Collapse and Conflict -}
  applyCast {Γ} {.⋆} {B} M v ((.⋆ ⇒ B) {c}) {activeProj .(⋆ ⇒ B) x} = {!!}
{-
         with PCR.canonical⋆ M v
  ...  | ⟨ A' , ⟨ M' , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | yes ap-b = M' ⟨ (A' ⇒ B) {ap-b} ⟩
  ...    | no ap-b = blame (pos 0)
-}
  {- CastFun -}
  applyCast {Γ} {A₁ ⇒ A₂} {B₁ ⇒ B₂} M v ((.(_ ⇒ _) ⇒ .(_ ⇒ _)) {c})
      {activeFun .((_ ⇒ _) ⇒ (_ ⇒ _))} = {!!}
      
  {- Cast Pair -}                   
  applyCast{Γ}{A₁ `× A₂}{B₁ `× B₂}M v ((_ ⇒ _){c}){activePair(_ ⇒ _)}=
      cons (fst M ⟨ (A₁ ⇒ B₁) {~×L c} ⟩) (snd M ⟨ (A₂ ⇒ B₂) {~×R c}⟩)
  {- Cast Sum -}
  applyCast{Γ}{A₁ `⊎ A₂}{B₁ `⊎ B₂}M v((_ ⇒ _){c}){activeSum .(_ ⇒ _)}=
    let l = inl ((` Z) ⟨ (A₁ ⇒ B₁) {~⊎L c}⟩) in
    let r = inr ((` Z) ⟨ (A₂ ⇒ B₂) {~⊎R c}⟩) in
    case M (ƛ l) (ƛ r)
     
{-
  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B')))
            → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M c {()} N
-}

  funSrc : ∀{A A' B' Γ}
         → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → (M : Γ ⊢ A) → SimpleValue M
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc c i M V = {!!}

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁)
  dom c ()

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  cod c ()

  fstCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
          → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M v c {i} = {!!}

  sndCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
          → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M v c {i} = {!!}
  
  caseCast : ∀ {Γ A A' B' C} → (L : Γ ⊢ A) → SimpleValue L
             → (c : Cast (A ⇒ (A' `⊎ B')))
             → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L v c {i} M N = {!!}
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → A ≢ ⋆ → ¬ Inert c
  baseNotInert c ne = {!!}

  compose : ∀{A B C} → Cast (A ⇒ B) → Cast (B ⇒ C) → Cast (A ⇒ C)
  compose = {!!}

  module Red = PCR.Reduction applyCast funSrc dom cod fstCast sndCast caseCast
                 baseNotInert compose
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → (A ⇒ B) {c})

