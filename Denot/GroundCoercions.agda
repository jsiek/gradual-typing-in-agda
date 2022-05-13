

open import Data.Nat
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

module Denot.GroundCoercions where

  open import Types
  open import Variables
  open import Labels
  open import CastStructureABT
  open import GroundCoercions
  open import Denot.Value



  infix 4 _↝⟨_⟩↝_
  infix 4 _↝⟪_⟫↝_

  𝐺⟦_⟧ : (G : Type) → (g : Ground G) → Val → Set
  𝐺⟦ ` b ⟧ G-Base (const {b'} k) with base-eq? b b'
  ... | yes refl = True
  ... | no neq = False
  𝐺⟦ ` b ⟧ G-Base v = False
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun ν = True
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun (v ↦ w) = True
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun v = False
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair (fst v) = True
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair (snd v) = True
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair v = False
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum (inl v) = True
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum (inr v) = True
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum v = False

  data _↝⟨_⟩↝_ : ∀ {A B} → Val → Cast (A ⇒ B) → Val → Set
  data _↝⟪_⟫↝_ : ∀ {A B} → (V : List Val) → (c : Cast (A ⇒ B)) → (V' : List Val) → Set where
    [] : ∀ {A B}{c : Cast (A ⇒ B)} → [] ↝⟪ c ⟫↝ []
    _∷_ : ∀ {A B}{c : Cast (A ⇒ B)}{v v' V V'} → v ↝⟨ c ⟩↝ v' → V ↝⟪ c ⟫↝ V' → (v ∷ V) ↝⟪ c ⟫↝ (v' ∷ V')
  data _↝⟨_⟩↝_ where
    ⟦id⟧ : ∀{v : Val}{A : Type}{a : Atomic A}
      → v ↝⟨ id{A}{a} ⟩↝ v
    ⟦inj⟧ : ∀{v : Val}{G : Type}{g : Ground G}
      → v ↝⟨ inj G {g} ⟩↝ v
    ⟦proj⟧-ok : ∀{v : Val}{G : Type}{g : Ground G}{ℓ : Labels.Label}
      → 𝐺⟦ G ⟧ g v
      → v ↝⟨ proj G ℓ {g} ⟩↝ v
    ⟦proj⟧-fail : ∀{v : Val}{G : Type}{g : Ground G}{ℓ : Labels.Label}
      → ¬ 𝐺⟦ G ⟧ g v
      → v ↝⟨ proj G ℓ {g} ⟩↝ blame ℓ
    ⟦cfun⟧ : ∀{V w V′ w′}{A B A′ B′ : Type}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}
      → V′ ↝⟪ c ⟫↝ V   →   w ↝⟨ d ⟩↝ w′
      → (V ↦ w) ↝⟨ cfun c d ⟩↝ (V′ ↦ w′)
    ⟦cseq⟧ : ∀{u v w : Val}{A B C : Type}{c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}
      →   u ↝⟨ c ⟩↝ v    →   v ↝⟨ d ⟩↝ w
      → u ↝⟨ cseq c d ⟩↝ w


  open import Denot.CastStructure

-- This won't typecheck; LazyCoercions and GroundCoercions are written
-- using CastStructureOrig instead of CasStructureABT
 {-  
  instance 
    dcs : DenotCastStruct
    dcs = record 
            { cast = cs
            ; _↝⟨_⟩↝_ = _↝⟨_⟩↝_ }
  -}



{-
  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Val M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  {-
    V⟨id⟩    —→    V
   -}
  applyCast M v id {a} = M
  {-
    V⟨G!⟩⟨G?⟩    —→    V
    V⟨G!⟩⟨H?p⟩   —→   blame p  if G ≠ H
   -}
  applyCast M v (proj B ℓ {gb}) {a} with canonical⋆ M v
  ... | ⟨ G , ⟨ V , ⟨ c , ⟨ I-inj {G}{ga} , meq ⟩ ⟩ ⟩ ⟩
         rewrite meq
         with gnd-eq? G B {ga} {gb}
  ...    | no neq = blame ℓ
  ...    | yes eq
            with eq
  ...       | refl = V
  {-
   V⟨c ; d⟩     —→    V⟨c⟩⟨d⟩
   -}
  applyCast M v (cseq c d) = (M ⟨ c ⟩) ⟨ d ⟩
  applyCast M v (cpair c d) {a} = eta× M (cpair c d) C-pair
  applyCast M v (csum c d) {a} = eta⊎ M (csum c d) C-sum
  applyCast M v (cfun c d) {()}
  applyCast M v (inj A) {()}

-}