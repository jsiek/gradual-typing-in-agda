{-# OPTIONS --rewriting #-}
module LogRel.CastGradualGuarantee where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import LogRel.Cast
open import LogRel.CastDeterministic
open import StepIndexedLogic
open import LogRel.CastLogRel

ℰ-preserve-diamond : ∀{c : Prec}{k}
  → (M M′ N′ : Term)
  → (M′→N′ : M′ —↠ N′)
  → #(ℰ⟦ c ⟧ M M′) (suc (len M′→N′ + k))
  → ∃[ N ] (M —↠ N) × #(ℰ⟦ c ⟧ N N′) (suc k)
ℰ-preserve-diamond{c}{k} M M′ N′ (.M′ END) ℰMM′ = M , ((M END) , ℰMM′)
ℰ-preserve-diamond{c}{k} M M′ N′ (.M′ —→⟨ M′→M′₁ ⟩ M′₁→N′) ℰMM′ = {!!}

