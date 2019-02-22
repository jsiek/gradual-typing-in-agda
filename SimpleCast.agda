module SimpleCast where

  open import Data.Nat
  open import Data.Bool
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)

  data Cast : Type → Set where
    cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B)

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
  ActiveOrInert (cast .⋆ B ℓ {unk~L}) with eq-unk B
  ... | inj₁ eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (cast ⋆ ⋆ ℓ))
  ... | inj₂ neq = inj₁ (activeProj (cast ⋆ B ℓ) neq)
  ActiveOrInert (cast A .⋆ ℓ {unk~R}) with eq-unk A
  ... | inj₁ eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (cast ⋆ ⋆ ℓ))
  ... | inj₂ neq = inj₂ (inert neq (cast A ⋆ ℓ))
  ActiveOrInert (cast .Nat .Nat ℓ {nat~}) =
      inj₁ (activeId{Nat}{A-Nat} (cast Nat Nat ℓ))
  ActiveOrInert (cast .𝔹 .𝔹 ℓ {bool~}) =
      inj₁ (activeId{𝔹}{A-Bool} (cast 𝔹 𝔹 ℓ))
  ActiveOrInert (cast (A₁ ⇒ A₂) (B₁ ⇒ B₂) ℓ {fun~ c d}) =
      inj₁ (activeFun (cast (A₁ ⇒ A₂) (B₁ ⇒ B₂) ℓ))
  ActiveOrInert (cast (A₁ `× A₂) (B₁ `× B₂) ℓ {pair~ c d}) =
      inj₁ (activePair (cast (A₁ `× A₂) (B₁ `× B₂) ℓ))
  ActiveOrInert (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ {sum~ c d}) =
      inj₁ (activeSum (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ))

  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B)) → ∀ {a : Active c} → Γ ⊢ B
  applyCast {Γ} {A} {.A} M v (cast A .A ℓ {c}) {activeId .(cast A A ℓ)} = M
  applyCast {Γ} {.⋆} {B} M v (cast .⋆ B ℓ {c}) {activeProj .(cast ⋆ B ℓ) x} with PCR.canonical⋆ M v
  ...  | ⟨ A' , ⟨ M' , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | inj₁ ap-b = M' ⟨ cast A' B ℓ {ap-b} ⟩
  ...    | inj₂ ap-b = blame ℓ  
  applyCast {Γ} {A₁ ⇒ A₂} {B₁ ⇒ B₂} M v (cast .(_ ⇒ _) .(_ ⇒ _) ℓ {c}) {activeFun .(cast (_ ⇒ _) (_ ⇒ _) ℓ)} =
      ƛ B₁ , ((rename (λ {A} → S_) M · ((` Z) ⟨ cast B₁ A₁ (flip ℓ) {Sym~(~⇒L c)} ⟩)) ⟨ cast A₂ B₂ ℓ {~⇒R c} ⟩)
  applyCast{Γ}{A₁ `× A₂}{B₁ `× B₂}M v (cast .(_ `× _) .(_ `× _) ℓ {c}){activePair .(cast (_ `× _)(_ `× _) ℓ)} =
      cons (fst M ⟨ cast A₁ B₁ ℓ {~×L c} ⟩) (snd M ⟨ cast A₂ B₂ ℓ {~×R c}⟩)
  applyCast{Γ}{A₁ `⊎ A₂}{B₁ `⊎ B₂}M v(cast .(_ `⊎ _) .(_ `⊎ _) ℓ {c}){activeSum .(cast (_ `⊎ _) (_ `⊎ _) ℓ)} =
    let l = inl ((` Z) ⟨ cast A₁ B₁ ℓ {~⊎L c}⟩) in
    let r = inr ((` Z) ⟨ cast A₂ B₂ ℓ {~⊎R c}⟩) in
    case M (ƛ A₁ , l) (ƛ A₂ , r)
     
  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M c {()} N

  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M c {()}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M c {()}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B'))) → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L c {()} M N
  
  baseNotInert : ∀ {A B} → (c : Cast (A ⇒ B)) → Base B → ¬ Inert c
  baseNotInert c () (inert x .c)

  module Red = PCR.Reduction applyCast funCast fstCast sndCast caseCast baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast cast

