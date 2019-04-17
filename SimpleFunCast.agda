module SimpleFunCast where

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
  import ParamCastReduction

  data Cast :  Type → Set where
    cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  data Inert : ∀{A} → Cast A → Set where
    inert-inj : ∀{A} → A ≢ ⋆ → (c : Cast (A ⇒ ⋆)) → Inert c
    inert-fun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Inert c

  data Active : ∀{A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c    

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert (cast .⋆ B ℓ {unk~L}) with eq-unk B
  ... | yes eqb rewrite eqb = inj₁ (activeId {⋆}{A-Unk} (cast ⋆ ⋆ ℓ))
  ... | no neqb = inj₁ (activeProj (cast ⋆ B ℓ) neqb)
  
  ActiveOrInert (cast A .⋆ ℓ {unk~R}) with eq-unk A
  ... | yes eqa rewrite eqa = inj₁ (activeId{⋆}{A-Unk} (cast ⋆ ⋆ ℓ))
  ... | no neqa = inj₂ (inert-inj neqa (cast A ⋆ ℓ))
  
  ActiveOrInert (cast (` ι) (` ι) ℓ {base~}) =
     inj₁ (activeId {` ι}{A-Base} (cast (` ι) (` ι) ℓ))
  ActiveOrInert (cast (A ⇒ B) (A' ⇒ B') ℓ {fun~ c c₁}) =
     inj₂ (inert-fun (cast (A ⇒ B) (A' ⇒ B') ℓ))
  ActiveOrInert (cast (A `× B) (A' `× B') ℓ {pair~ c c₁}) =
     inj₁ (activePair (cast (A `× B) (A' `× B') ℓ))
  ActiveOrInert (cast (A `⊎ B) (A' `⊎ B') ℓ {sum~ c c₁}) =
     inj₁ (activeSum (cast (A `⊎ B) (A' `⊎ B') ℓ))

  funNotActive : ∀{A₁ A₂ B₁ B₂ ℓ c} → ¬ Active (cast (A₁ ⇒ A₂) (B₁ ⇒ B₂) ℓ {c})
  funNotActive (activeId {a = ()} .(cast (_ ⇒ _) (_ ⇒ _) _))

  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  applyCast {Γ}{A}{B} M v (cast .⋆ B ℓ {unk~L}) {a} with PCR.canonical⋆ M v
  ...  | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | yes ap-b = M' ⟨ cast A' B ℓ {ap-b} ⟩
  ...    | no ap-b = blame ℓ  
  applyCast M v (cast .⋆ ⋆ ℓ {unk~R}) {activeId .(cast ⋆ ⋆ ℓ)} = M
  applyCast M v (cast A ⋆ ℓ {unk~R}) {activeProj .(cast A ⋆ ℓ) x} =
     ⊥-elim (x refl)
  applyCast M v (cast (` ι) (` ι) ℓ {base~}) {a} = M
  
  applyCast{Γ} M v (cast (A₁ ⇒ A₂) (B₁ ⇒ B₂) ℓ {fun~ c c₁}) {a} =
     contradiction a funNotActive
  
  applyCast M v (cast (A₁ `× A₂) (B₁ `× B₂) ℓ {pair~ c c₁}) {a} =
    cons (fst M ⟨ cast A₁ B₁ ℓ {c} ⟩) (snd M ⟨ cast A₂ B₂ ℓ {c₁}⟩)
  
  applyCast M v (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ {sum~ c c₁}) {a} =
    let l = inl ((` Z) ⟨ cast A₁ B₁ ℓ {c}⟩) in
    let r = inr ((` Z) ⟨ cast A₂ B₂ ℓ {c₁}⟩) in
    case M (ƛ l) (ƛ r)

{-
  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B')))
          → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ {cns}) {inert-fun {A₁} {A₂}
            (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ)} N =
     (M · (N ⟨ cast A' A₁ (flip ℓ) {Sym~ (~⇒L cns)} ⟩))
         ⟨ cast A₂ B' ℓ {~⇒R cns} ⟩
-}

  funSrc : ∀{A A' B'}
         → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc c (inert-fun {A}{B}{A'}{B'} .c) = ⟨ A , ⟨ B , refl ⟩ ⟩

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁)
  dom (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ {c}) (inert-fun _) =
     cast A' A₁ ℓ {Sym~ (~⇒L c)}

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  cod (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ {c}) (inert-fun _) = cast A₂ B' ℓ {~⇒R c}

  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B')))
          → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M c {()}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B')))
          → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M c {()}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B')))
           → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L c {()} M N
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  module Red = PCR.Reduction applyCast funSrc dom cod fstCast sndCast caseCast
                  baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast cast
