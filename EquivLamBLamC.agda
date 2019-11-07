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
        → cast A A ℓ {c} ≈ id {A}{a}

   ≈-inj : ∀{A}{ℓ : Label}{c : A ~ ⋆}{g : Ground A}
         → cast A ⋆ ℓ {c} ≈ inj A {g}
         
   ≈-proj : ∀{A}{ℓ : Label}{c : ⋆ ~ A}{g : Ground A}
         → cast ⋆ A ℓ {c} ≈ proj A ℓ {g}

   ≈-fun : ∀{A B C D}{ℓ : Label}{cn : A ⇒ B ~ C ⇒ D}{cd : C ~ A}{cc : B ~ D}{c : CastC (C ⇒ A)}{d : CastC (B ⇒ D)}
          → cast C A ℓ {cd} ≈ c
          → cast B D ℓ {cc} ≈ d
          → cast (A ⇒ B) (C ⇒ D) ℓ {cn} ≈ cfun c d

   ≈-pair : ∀{A B C D}{ℓ : Label}{cn : A `× B ~ C `× D}{cd : A ~ C}{cc : B ~ D}{c : CastC (A ⇒ C)}{d : CastC (B ⇒ D)}
          → cast A C ℓ {cd} ≈ c
          → cast B D ℓ {cc} ≈ d
          → cast (A `× B) (C `× D) ℓ {cn} ≈ cpair c d

   ≈-sum : ∀{A B C D}{ℓ : Label}{cn : A `⊎ B ~ C `⊎ D}{cd : A ~ C}{cc : B ~ D}{c : CastC (A ⇒ C)}{d : CastC (B ⇒ D)}
          → cast A C ℓ {cd} ≈ c
          → cast B D ℓ {cc} ≈ d
          → cast (A `⊎ B) (C `⊎ D) ℓ {cn} ≈ csum c d

   ≈-inj-seq : ∀{A G}{g : Ground G}{¬gA : ¬ Ground A}{ag : A ~ G}{gs : G ~ ⋆}{ℓ : Label}{c : CastC (A ⇒ G)}{d : CastC (G ⇒ ⋆)}{as : A ~ ⋆}
          → cast A G ℓ {ag} ≈ c
          → cast G ⋆ ℓ {gs} ≈ d
          → cast A ⋆ ℓ {as} ≈ cseq c d

   ≈-proj-seq : ∀{A G}{g : Ground G}{¬gA : ¬ Ground A}{sg : ⋆ ~ G}{ga : G ~ A}{ℓ : Label}{c : CastC (⋆ ⇒ G)}{d : CastC (G ⇒ A)}{sa : ⋆ ~ A}
          → cast ⋆ G ℓ {sg} ≈ c
          → cast G A ℓ {ga} ≈ d
          → cast ⋆ A ℓ {sa} ≈ cseq c d

inert-equiv : ∀{A B : Type}{c₁ : CastB (A ⇒ B)}{c₂ : CastC (A ⇒ B)}
            → CastStruct.Inert sB c₁ → c₁ ≈ c₂ → CastStruct.Inert sC c₂
inert-equiv {A} {⋆} (I-inj gA (cast A ⋆ ℓ)) ≈-inj = I-inj
inert-equiv {A} {⋆} (I-inj gA (cast A ⋆ ℓ)) (≈-inj-seq {¬gA = ¬gA} c₁≈c₂ c₁≈c₃) = ⊥-elim (contradiction gA ¬gA)
inert-equiv (I-fun _) (≈-fun c₁≈c₂ c₁≈c₃) = I-fun

active-equiv : ∀{A B : Type}{c₁ : CastB (A ⇒ B)}{c₂ : CastC (A ⇒ B)}
            → CastStruct.Active sB c₁ → c₁ ≈ c₂ → CastStruct.Active sC c₂
active-equiv {A} {.A} (A-id .(cast A A _)) ≈-id = A-id
active-equiv {.⋆} {.⋆} (A-id .(cast ⋆ ⋆ _)) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-id .(cast ⋆ ⋆ _)) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-inj .(cast ⋆ ⋆ _) x x₁) ≈-id = A-id
active-equiv {A} {.⋆} (A-inj .(cast A ⋆ _) ¬gA x₁) (≈-inj{g = gA}) = ⊥-elim (contradiction gA ¬gA)
active-equiv {A} {.⋆} (A-inj .(cast A ⋆ _) x x₁) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-inj .(cast ⋆ ⋆ _) x x₁) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-proj .(cast ⋆ ⋆ _) x) ≈-id = A-id
active-equiv {.⋆} {B} (A-proj .(cast ⋆ B _) x) ≈-proj = A-proj
active-equiv {.⋆} {.⋆} (A-proj .(cast ⋆ ⋆ _) x) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {B} (A-proj .(cast ⋆ B _) x) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.(_ `× _)} {.(_ `× _)} (A-pair .(cast (_ `× _) (_ `× _) _)) (≈-pair c₁≈c₂ c₁≈c₃) = A-pair
active-equiv {.(_ `⊎ _)} {.(_ `⊎ _)} (A-sum .(cast (_ `⊎ _) (_ `⊎ _) _)) (≈-sum c₁≈c₂ c₁≈c₃) = A-sum
