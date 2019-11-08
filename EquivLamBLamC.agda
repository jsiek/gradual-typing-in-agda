open import Types
open import CastStructure
open import Labels
import EquivCast

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥; ⊥-elim)

module EquivLamBLamC where

open import GroundCast renaming (struct to sB)
module LamB = CastStructure.CastCalc sB
open CastStruct sB renaming (Cast to CastB)

open import GroundCoercions renaming (struct to sC)
module LamC = CastStructure.CastCalc sC
open CastStruct sC renaming (Cast to CastC)

module EquivBC = EquivCast sB sC

data _≈_ : ∀{A B} → CastB (A ⇒ B) → CastC (A ⇒ B) → Set where

   ≈-id : ∀{A}{a : Atomic A}{ℓ : Label}{c : A ~ A}
        → cast A A ℓ c ≈ id {A}{a}

   ≈-inj : ∀{A}{ℓ : Label}{c : A ~ ⋆}{g : Ground A}
         → cast A ⋆ ℓ c ≈ inj A {g}
         
   ≈-proj : ∀{A}{ℓ : Label}{c : ⋆ ~ A}{g : Ground A}
         → cast ⋆ A ℓ c ≈ proj A ℓ {g}

   ≈-fun : ∀{A B C D}{ℓ : Label}{cn : A ⇒ B ~ C ⇒ D}{ca : C ~ A}{bd : B ~ D}{c : CastC (C ⇒ A)}{d : CastC (B ⇒ D)}
          → cast C A ℓ ca ≈ c
          → cast B D ℓ bd ≈ d
          → cast (A ⇒ B) (C ⇒ D) ℓ (fun~ ca bd) ≈ cfun c d

   ≈-pair : ∀{A B C D}{ℓ : Label}{cn : A `× B ~ C `× D}{ac : A ~ C}{bd : B ~ D}{c : CastC (A ⇒ C)}{d : CastC (B ⇒ D)}
          → cast A C ℓ ac ≈ c
          → cast B D ℓ bd ≈ d
          → cast (A `× B) (C `× D) ℓ (pair~ ac bd) ≈ cpair c d

   ≈-sum : ∀{A B C D}{ℓ : Label}{cn : A `⊎ B ~ C `⊎ D}{ac : A ~ C}{bd : B ~ D}{c : CastC (A ⇒ C)}{d : CastC (B ⇒ D)}
          → cast A C ℓ ac ≈ c
          → cast B D ℓ bd ≈ d
          → cast (A `⊎ B) (C `⊎ D) ℓ (sum~ ac bd) ≈ csum c d

   ≈-inj-seq : ∀{A G}{g : Ground G}{¬gA : ¬ Ground A}{ag : A ~ G}{gs : G ~ ⋆}{ℓ : Label}{c : CastC (A ⇒ G)}{d : CastC (G ⇒ ⋆)}{as : A ~ ⋆}
          → cast A G ℓ ag ≈ c
          → cast G ⋆ ℓ gs ≈ d
          → cast A ⋆ ℓ as ≈ cseq c d

   ≈-proj-seq : ∀{A G}{g : Ground G}{¬gA : ¬ Ground A}{sg : ⋆ ~ G}{ga : G ~ A}{ℓ : Label}{c : CastC (⋆ ⇒ G)}{d : CastC (G ⇒ A)}{sa : ⋆ ~ A}
          → cast ⋆ G ℓ sg ≈ c
          → cast G A ℓ ga ≈ d
          → cast ⋆ A ℓ sa ≈ cseq c d

inert-equiv : ∀{A B : Type}{c₁ : CastB (A ⇒ B)}{c₂ : CastC (A ⇒ B)}
            → CastStruct.Inert sB c₁ → c₁ ≈ c₂ → CastStruct.Inert sC c₂
inert-equiv {A} {⋆} (I-inj gA (cast A ⋆ ℓ as)) ≈-inj = I-inj
inert-equiv {A} {⋆} (I-inj gA (cast A ⋆ ℓ as)) (≈-inj-seq {¬gA = ¬gA} c₁≈c₂ c₁≈c₃) = ⊥-elim (contradiction gA ¬gA)
inert-equiv (I-fun _) (≈-fun c₁≈c₂ c₁≈c₃) = I-fun

active-equiv : ∀{A B : Type}{c₁ : CastB (A ⇒ B)}{c₂ : CastC (A ⇒ B)}
            → CastStruct.Active sB c₁ → c₁ ≈ c₂ → CastStruct.Active sC c₂
active-equiv {A} {.A} (A-id .(cast A A _ _)) ≈-id = A-id
active-equiv {.⋆} {.⋆} (A-id .(cast ⋆ ⋆ _ _)) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-id .(cast ⋆ ⋆ _ _)) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-inj .(cast ⋆ ⋆ _ _) x x₁) ≈-id = A-id
active-equiv {A} {.⋆} (A-inj .(cast A ⋆ _ _) ¬gA x₁) (≈-inj{g = gA}) = ⊥-elim (contradiction gA ¬gA)
active-equiv {A} {.⋆} (A-inj .(cast A ⋆ _ _) x x₁) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-inj .(cast ⋆ ⋆ _ _) x x₁) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-proj .(cast ⋆ ⋆ _ _) x) ≈-id = A-id
active-equiv {.⋆} {B} (A-proj .(cast ⋆ B _ _) x) ≈-proj = A-proj
active-equiv {.⋆} {.⋆} (A-proj .(cast ⋆ ⋆ _ _) x) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {B} (A-proj .(cast ⋆ B _ _) x) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.(_ `× _)} {.(_ `× _)} (A-pair .(cast (_ `× _) (_ `× _) _ _)) (≈-pair c₁≈c₂ c₁≈c₃) = A-pair
active-equiv {.(_ `⊎ _)} {.(_ `⊎ _)} (A-sum .(cast (_ `⊎ _) (_ `⊎ _) _ _)) (≈-sum c₁≈c₂ c₁≈c₃) = A-sum

dom-equiv : ∀{A B C D : Type}{c₁ : CastB ((A ⇒ B) ⇒ (C ⇒ D))}{i₁ : CastStruct.Inert sB c₁}
                             {c₂ : CastC ((A ⇒ B) ⇒ (C ⇒ D))}{i₂ : CastStruct.Inert sC c₂}
          → c₁ ≈ c₂ 
          → (CastStruct.dom sB c₁ i₁) ≈ (CastStruct.dom sC c₂ i₂)
dom-equiv {c₁ = cast .(_ ⇒ _) .(_ ⇒ _) ℓ (fun~ ca bd)} {I-fun _} {cfun c₂ d₂} {I-fun} (≈-fun c₁≈c₂ c₁≈c₃) = c₁≈c₂

cod-equiv : ∀{A B C D : Type}{c₁ : CastB ((A ⇒ B) ⇒ (C ⇒ D))}{i₁ : CastStruct.Inert sB c₁}
                             {c₂ : CastC ((A ⇒ B) ⇒ (C ⇒ D))}{i₂ : CastStruct.Inert sC c₂}
          → c₁ ≈ c₂ 
          → (CastStruct.cod sB c₁ i₁) ≈ (CastStruct.cod sC c₂ i₂)
cod-equiv {c₁ = cast .(_ ⇒ _) .(_ ⇒ _) ℓ (fun~ ca bd)} {I-fun _} {cfun c₂ d₂} {I-fun} (≈-fun c₁≈c₂ c₁≈c₃) = c₁≈c₃
