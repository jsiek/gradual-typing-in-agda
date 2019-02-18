module GroundCast where

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
    inert : ∀{A} → Ground A → (c : Cast (A ⇒ ⋆)) → Inert c

  data Active : ∀ {A} → Cast A → Set where
    activeIdUnk : (c : Cast (⋆ ⇒ ⋆)) → Active c
    activeInj : ∀ {A} → (c : Cast (A ⇒ ⋆)) → (g : ¬ Ground A) → Active c
    activeOther : ∀ {A B} → (c : Cast (A ⇒ B)) → (B ≢ ⋆) → Active c

  inert-ground : ∀{A B} → (c : Cast (A ⇒ B)) → Inert c → Ground A
  inert-ground c (inert ga .c) = ga

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert (cast A B ℓ {c}) with eq-unk A | eq-unk B
  ... | inj₁ eqa | inj₁ eqb rewrite eqa | eqb = inj₁ (activeIdUnk (cast ⋆ ⋆ ℓ)) 
  ... | inj₁ eqa | inj₂ neqb = inj₁ (activeOther (cast A B ℓ) neqb)
  ... | inj₂ neqa | inj₂ neqb = inj₁ (activeOther (cast A B ℓ) neqb)
  ... | inj₂ neqa | inj₁ eqb rewrite eqb with ground? A
  ...    | inj₁ g = inj₂ (inert g (cast A ⋆ ℓ))
  ...    | inj₂ ng = inj₁ (activeInj (cast A ⋆ ℓ) ng)

  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
     → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v (cast .⋆ .⋆ ℓ {unk~R}) {activeIdUnk .(cast ⋆ ⋆ ℓ)} = M
  applyCast {Γ}{A}{B} M v (cast .⋆ B ℓ {unk~L}) {a} with eq-unk B
  ... | inj₁ eq rewrite eq = M
  ... | inj₂ neq with ground? B
  ...    | inj₁ gb with PCR.canonical⋆ M v
  ...       | ⟨ A' , ⟨ M' , ⟨ c , ⟨ i , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with gnd-eq? A' B {inert-ground c i} {gb}
  ...          | inj₁ ap-b rewrite ap-b = M'
  ...          | inj₂ ap-b = blame ℓ  
  applyCast {Γ}{A}{B} M v (cast .⋆ B ℓ {unk~L}) {a} | inj₂ neq | inj₂ ngb with ground B {neq}
  ...       | ⟨ H , ⟨ gh , hb ⟩ ⟩ =
              (M ⟨ cast ⋆ H ℓ {unk~L} ⟩) ⟨ cast H B ℓ {Sym~ hb} ⟩
  applyCast M v (cast A ⋆ ℓ {unk~R}) {activeInj .(cast A ⋆ ℓ) x} with eq-unk A
  ... | inj₁ eq rewrite eq = M
  ... | inj₂ neq with ground A {neq}
  ...    | ⟨ G , c ⟩ = ((M ⟨ cast A G ℓ {proj₂ c} ⟩) ⟨ cast G ⋆ ℓ {unk~R} ⟩)
  applyCast M v (cast A ⋆ ℓ {unk~R}) {activeOther .(cast A ⋆ ℓ) x} =
      ⊥-elim (x refl)
  applyCast M v (cast Nat Nat ℓ {nat~}) {a} = M
  applyCast M v (cast 𝔹 𝔹 ℓ {bool~}) {a} = M
  applyCast{Γ} M v (cast (A₁ ⇒ A₂) (B₁ ⇒ B₂) ℓ {fun~ c c₁}) {a} =
    ƛ B₁ , ((rename (λ {A} → S_) M · ((` Z) ⟨ cast B₁ A₁ (flip ℓ) {Sym~ c} ⟩)) ⟨ cast A₂ B₂ ℓ {c₁} ⟩)
  applyCast M v (cast (A₁ `× A₂) (B₁ `× B₂) ℓ {pair~ c c₁}) {a} =
    cons (fst M ⟨ cast A₁ B₁ ℓ {c} ⟩) (snd M ⟨ cast A₂ B₂ ℓ {c₁}⟩)
  applyCast M v (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ {sum~ c c₁}) {a} =
    let l = inl ((` Z) ⟨ cast A₁ B₁ ℓ {c}⟩) in
    let r = inr ((` Z) ⟨ cast A₂ B₂ ℓ {c₁}⟩) in
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
