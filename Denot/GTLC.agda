open import GTLC
open import Denot.Value
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import NewDenotProperties

open import Data.Bool using (true; false)
open import Data.Empty renaming (⊥ to False)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic renaming (⊤ to p⊤; tt to ptt)
open import Relation.Nullary using (¬_)


module Denot.GTLC where



{-
sig : Op → List Sig
sig (op-lam A) = (ν ■) ∷ []
sig (op-app ℓ) = ■ ∷ ■ ∷ []
sig (op-lit r p) = []
sig (op-if ℓ) = ■ ∷ ■ ∷ ■ ∷ []
sig op-cons = ■ ∷ ■ ∷ []
sig (op-fst ℓ) = ■ ∷ []
sig (op-snd ℓ) = ■ ∷ []
sig (op-inl B) = ■ ∷ []
sig (op-inr A) = ■ ∷ []
sig (op-case ℓ A B) = ■ ∷ (ν ■) ∷ (ν ■) ∷ []
-- mutable references not included 
-- op-ref (■ ∷ []) , (op-deref ℓ) (■ ∷ []) , (op-assign ℓ) (■ ∷ ■ ∷ [])
-}

  open import Fold2 Op sig
  open import NewSemantics Op sig public

  𝕆-GTLC : DOpSig (𝒫 Val) sig
  𝕆-GTLC (op-lam x) ⟨ F , ptt ⟩ = Λ F
  𝕆-GTLC (op-app x) ⟨ D , ⟨ E , ptt ⟩ ⟩ = D ∗ E
  𝕆-GTLC (op-lit f P) ptt = ℘ P f
  𝕆-GTLC (op-if x) ⟨ D , ⟨ E₁ , ⟨ E₂ , ptt ⟩ ⟩ ⟩ = If D E₁ E₂
  𝕆-GTLC op-cons ⟨ D , ⟨ E , ptt ⟩ ⟩ = pair D E
  𝕆-GTLC (op-fst x) ⟨ D , ptt ⟩ = car D
  𝕆-GTLC (op-snd x) ⟨ D , ptt ⟩ = cdr D
  𝕆-GTLC (op-inl x) ⟨ D , ptt ⟩ = inleft D
  𝕆-GTLC (op-inr x) ⟨ D , ptt ⟩ = inright D
  𝕆-GTLC (op-case x x₁ x₂) ⟨ D , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩ = cond D F₁ F₂

  𝕆-GTLC-mono : 𝕆-monotone sig 𝕆-GTLC
  𝕆-GTLC-mono = {!   !}

  instance
    GTLC-Semantics : Semantics
    GTLC-Semantics = record { interp-op = 𝕆-GTLC ;
                               mono-op = 𝕆-GTLC-mono ;
                               error = ERR }
  open Semantics {{...}} public


