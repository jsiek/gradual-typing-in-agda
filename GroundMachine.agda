module GroundMachine where

  open import Data.Nat
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)

  open import Labels
  open import Types
  open import EfficientGroundCoercions

  import AbstractMachine
  module AbsMach = AbstractMachine Cast Inert Active ActiveOrInert
  open AbsMach

  cast : ∀{A B} → Value A → (c : Cast (A ⇒ B)) → Value B ⊎ Label

  scast : ∀{A B} → SimpleValue A → (c : Cast (A ⇒ B)) → Active c
      → Value B ⊎ Label
  scast U .id★ A-id★ = ⊥-elim (contradiction refl (simple⋆ U))
  scast U .(_ ?? _ ⨟ _) A-proj = ⊥-elim (contradiction refl (simple⋆ U))
  scast (V-const k {()}) .(` (` (_ ×' _))) (A-intmd (A-gnd A-cpair))
  scast (V-pair V₁ V₂) (` (` (c ×' d))) (A-intmd (A-gnd A-cpair))
      with cast V₁ c | cast V₂ d
  ... | inj₁ V₁' | inj₁ V₂' = inj₁ (S-val (V-pair V₁' V₂'))
  ... | inj₁ V₁' | inj₂ ℓ = inj₂ ℓ
  ... | inj₂ ℓ | _ = inj₂ ℓ
  scast (V-const k {()}) _ (A-intmd (A-gnd A-csum))
  scast (V-inl V) (` (` (c +' d))) (A-intmd (A-gnd A-csum))
      with cast V c
  ... | inj₁ V' = inj₁ (S-val (V-inl V'))
  ... | inj₂ ℓ = inj₂ ℓ
  scast (V-inr V) (` (` (c +' d))) (A-intmd (A-gnd A-csum))
      with cast V d
  ... | inj₁ V' = inj₁ (S-val (V-inr V'))
  ... | inj₂ ℓ = inj₂ ℓ
  scast U (` (` idι)) (A-intmd (A-gnd A-idι)) = inj₁ (S-val U)
  scast U (` cfail _ _ ℓ) (A-intmd A-cfail) = inj₂ ℓ

  scast' : ∀{A B} → SimpleValue A → (c : Cast (A ⇒ B)) → Value B ⊎ Label
  scast' U c
      with ActiveOrInert c
  ... | inj₁ a = scast U c a
  ... | inj₂ i = inj₁ (V-cast U c {i})
  
  cast (S-val U) c = scast' U c
  cast (V-cast U c) d = scast' U (compose c d)

  funSrc' : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → SimpleValue A
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  funSrc' (G ?? x ⨟ x₁) () V
  funSrc' (` (` (c ↣ d))) (I-intmd (I-gnd (I-cfun{A}{B}{A'}{B'}))) V =
      ⟨ A , ⟨ A' , refl ⟩ ⟩
  funSrc' (` cfail G H x) (I-intmd ()) V

  prodSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' `× B'))) → (i : Inert c)
            → SimpleValue A
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  prodSrc .(` (` _)) (I-intmd (I-gnd ())) v
  
  cfst : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         → Cast (A₁ ⇒ A')
  cfst .(` (` _)) (I-intmd (I-gnd ()))
  
  csnd : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  csnd .(` (` _)) (I-intmd (I-gnd ()))
  
  sumSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' `⊎ B'))) → (i : Inert c)
            → SimpleValue A
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  sumSrc .(` (` _)) (I-intmd (I-gnd ()))
  
  cinl : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Inert c
         → Cast (A₁ ⇒ A')
  cinl .(` (` _)) (I-intmd (I-gnd ()))
  
  cinr : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Inert c
         →  Cast (A₂ ⇒ B')
  cinr .(` (` _)) (I-intmd (I-gnd ()))

  module Mach = AbsMach.Machine cast
                  funSrc' dom cod
                  prodSrc cfst csnd
                  sumSrc cinl cinr
                  compose baseNotInert

