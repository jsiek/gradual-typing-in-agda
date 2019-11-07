module SimpleCast where

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
    _⇒⟨_⟩_ : (A : Type) → Label → (B : Type) → {c : A ~ B } → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  data Inert : ∀ {A} → Cast A → Set where
    inert : ∀{A} → A ≢ ⋆ → (c : Cast (A ⇒ ⋆)) → Inert c

  data Active : ∀ {A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c
    activeFun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c    

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert ((.⋆ ⇒⟨ ℓ ⟩ B) {unk~L}) with eq-unk B
  ... | yes eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (⋆ ⇒⟨ ℓ ⟩ ⋆))
  ... | no neq = inj₁ (activeProj (⋆ ⇒⟨ ℓ ⟩ B) neq)
  ActiveOrInert ((A ⇒⟨ ℓ ⟩ .⋆) {unk~R}) with eq-unk A
  ... | yes eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (⋆ ⇒⟨ ℓ ⟩ ⋆))
  ... | no neq = inj₂ (inert neq (A ⇒⟨ ℓ ⟩ ⋆))
  ActiveOrInert (((` ι)  ⇒⟨ ℓ ⟩ (` ι)) {base~}) =
      inj₁ (activeId{` ι}{A-Base} ((` ι) ⇒⟨ ℓ ⟩ (` ι)))
  ActiveOrInert (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {fun~ c d}) =
      inj₁ (activeFun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)))
  ActiveOrInert (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {pair~ c d}) =
      inj₁ (activePair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))
  ActiveOrInert (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {sum~ c d}) =
      inj₁ (activeSum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))

  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  {- Id -}
  applyCast {Γ} {A} {.A} M v ((A ⇒⟨ ℓ ⟩ .A) {c}) {activeId .(A ⇒⟨ ℓ ⟩ A)} = M
  {- Collapse and Conflict -}
  applyCast {Γ} {.⋆} {B} M v ((.⋆ ⇒⟨ ℓ ⟩ B) {c}) {activeProj .(⋆ ⇒⟨ ℓ ⟩ B) x}
         with PCR.canonical⋆ M v
  ...  | ⟨ A' , ⟨ M' , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | yes ap-b = M' ⟨ (A' ⇒⟨ ℓ ⟩ B) {ap-b} ⟩
  ...    | no ap-b = blame ℓ  
  {- Wrap -}
  applyCast {Γ} {A₁ ⇒ A₂} {B₁ ⇒ B₂} M v ((.(_ ⇒ _) ⇒⟨ ℓ ⟩ .(_ ⇒ _)) {c})
      {activeFun .((_ ⇒ _) ⇒⟨ ℓ ⟩ (_ ⇒ _))} =
      ƛ ((rename (λ {A} → S_) M · (` Z ⟨ (B₁ ⇒⟨ flip ℓ ⟩ A₁) {Sym~(~⇒L c)} ⟩))
           ⟨ (A₂ ⇒⟨ ℓ ⟩ B₂) {~⇒R c} ⟩)
  {- Cast Pair -}                   
  applyCast{Γ}{A₁ `× A₂}{B₁ `× B₂}M v ((_ ⇒⟨ ℓ ⟩ _){c}){activePair(_ ⇒⟨ ℓ ⟩ _)}=
      cons (fst M ⟨ (A₁ ⇒⟨ ℓ ⟩ B₁) {~×L c} ⟩) (snd M ⟨ (A₂ ⇒⟨ ℓ ⟩ B₂) {~×R c}⟩)
  {- Cast Sum -}
  applyCast{Γ}{A₁ `⊎ A₂}{B₁ `⊎ B₂}M v((_ ⇒⟨ ℓ ⟩ _){c}){activeSum .(_ ⇒⟨ ℓ ⟩ _)}=
    let l = inl ((` Z) ⟨ (A₁ ⇒⟨ ℓ ⟩ B₁) {~⊎L c}⟩) in
    let r = inr ((` Z) ⟨ (A₂ ⇒⟨ ℓ ⟩ B₂) {~⊎R c}⟩) in
    case M (ƛ l) (ƛ r)
     
  funSrc : ∀{A A' B'}
         → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc c ()

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁)
  dom c ()

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  cod c ()

  pairSrc : ∀{A A' B'}
         → (c : Cast (A ⇒ (A' `× B'))) → (i : Inert c)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  pairSrc c ()

  sumSrc : ∀{A A' B'}
         → (c : Cast (A ⇒ (A' `⊎ B'))) → (i : Inert c)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  sumSrc c ()

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         → Cast (A₁ ⇒ A')
  fstC c ()

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  sndC c ()

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Inert c
         → Cast (A₁ ⇒ A')
  inlC c ()

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  inrC c ()
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  module Red = PCR.Reduction applyCast funSrc pairSrc sumSrc
                 dom cod fstC sndC inlC inrC
                 baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → (A ⇒⟨ ℓ ⟩ B) {c})

