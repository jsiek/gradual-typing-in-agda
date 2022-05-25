{-# OPTIONS --allow-unsolved-metas #-}

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
  open import Labels
  open import CastStructureABT
  open import GroundCoercionsABT
  open import Denot.Value
  open import SetsAsPredicates



  infix 4 _↝⟨_⟩↝_
  infix 4 _↝⟨_⟩₊↝_

  𝐺⟦_⟧ : (G : Type) → (g : Ground G) → Val → Set
  𝐺⟦ τ ⟧ g (blame ℓ) = True
  𝐺⟦ ` b ⟧ G-Base (const {b'} k) with base-eq? b b'
  ... | yes refl = True
  ... | no neq = False
  𝐺⟦ ` b ⟧ G-Base v = False
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun ν = True
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun (V ↦ w) = True
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun v = False
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair (fst v) = True
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair (snd v) = True
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair v = False
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum (inl V) = True
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum (inr V) = True
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum v = False

  𝐺-sound : ∀ τ g v → v ∈ 𝐺⟦ τ ⟧ g → ⟦ v ∶ τ ⟧
  𝐺-sound τ g (blame ℓ) v∈𝐺⟦τ⟧ = ⟦blame∶τ⟧ τ
  𝐺-sound (` b) G-Base (const {b'} x) v∈𝐺⟦τ⟧ with base-eq? b b'
  ... | yes refl = tt
  ... | no neq = v∈𝐺⟦τ⟧
  𝐺-sound .(⋆ ⇒ ⋆) G-Fun (x ↦ v) v∈𝐺⟦τ⟧ = λ _ → tt
  𝐺-sound .(⋆ ⇒ ⋆) G-Fun ν v∈𝐺⟦τ⟧ = tt
  𝐺-sound .(⋆ `× ⋆) G-Pair (fst v) v∈𝐺⟦τ⟧ = tt
  𝐺-sound .(⋆ `× ⋆) G-Pair (snd v) v∈𝐺⟦τ⟧ = tt
  𝐺-sound .(⋆ `⊎ ⋆) G-Sum (inl x) v∈𝐺⟦τ⟧ = ⟦V∶⋆⟧₊
  𝐺-sound .(⋆ `⊎ ⋆) G-Sum (inr x) v∈𝐺⟦τ⟧ = ⟦V∶⋆⟧₊

  𝐺-adequate : ∀ τ (g : Ground τ) v → ⟦ v ∶ τ ⟧ → v ∈ 𝐺⟦ τ ⟧ g
  𝐺-adequate τ g (blame ℓ) v∶τ = tt
  𝐺-adequate (` b) G-Base (const {b'} x) v∶τ with base-eq? b b'
  ... | yes refl = tt
  ... | no neq = v∶τ
  𝐺-adequate .(⋆ ⇒ ⋆) G-Fun (x ↦ v) v∶τ = tt
  𝐺-adequate .(⋆ ⇒ ⋆) G-Fun ν v∶τ = tt
  𝐺-adequate .(⋆ `× ⋆) G-Pair (fst v) v∶τ = tt
  𝐺-adequate .(⋆ `× ⋆) G-Pair (snd v) v∶τ = tt
  𝐺-adequate .(⋆ `⊎ ⋆) G-Sum (inl x) v∶τ = tt
  𝐺-adequate .(⋆ `⊎ ⋆) G-Sum (inr x) v∶τ = tt

  data _↝⟨_⟩↝_ : ∀ {A B} → Val → Cast (A ⇒ B) → Val → Set
  data _↝⟨_⟩₊↝_ : ∀ {A B} → (V : List Val) → (c : Cast (A ⇒ B)) → (V' : List Val) → Set where
    [] : ∀ {A B}{c : Cast (A ⇒ B)} → [] ↝⟨ c ⟩₊↝ []
    _∷_ : ∀ {A B}{c : Cast (A ⇒ B)}{v v' V V'} → v ↝⟨ c ⟩↝ v' → V ↝⟨ c ⟩₊↝ V' → (v ∷ V) ↝⟨ c ⟩₊↝ (v' ∷ V')
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
      → v ↝⟨ proj G ℓ {g} ⟩↝ (blame ℓ)
    ⟦cfun⟧ : ∀{V w V′ w′}{A B A′ B′ : Type}{c : Cast (A′ ⇒ A)}{d : Cast (B ⇒ B′)}
      → V′ ↝⟨ c ⟩₊↝ V   →   w ↝⟨ d ⟩↝ w′
      → (V ↦ w) ↝⟨ cfun c d ⟩↝ (V′ ↦ w′)
    ⟦cpair⟧-fst-ok : ∀{u v}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → ¬ (isBlame v) → u ↝⟨ c ⟩↝ v 
      → fst u ↝⟨ cpair c d ⟩↝ fst v
    ⟦cpair⟧-fst-fail : ∀{u ℓ}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → u ↝⟨ c ⟩↝ blame ℓ
      → fst u ↝⟨ cpair c d ⟩↝ blame ℓ
    ⟦cpair⟧-snd-ok : ∀{u v}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → ¬ (isBlame v) → u ↝⟨ d ⟩↝ v
      → snd u ↝⟨ cpair c d ⟩↝ snd v
    ⟦cpair⟧-snd-fail : ∀{u ℓ}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → u ↝⟨ d ⟩↝ blame ℓ
      → snd u ↝⟨ cpair c d ⟩↝ blame ℓ
    ⟦csum⟧-inl-ok : ∀{V V'}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → ¬ (hasBlame V') → V ↝⟨ c ⟩₊↝ V'
      → inl V ↝⟨ csum c d ⟩↝ inl V'
    ⟦csum⟧-inl-fail : ∀{V V'}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → hasBlame V' → V ↝⟨ c ⟩₊↝ V'
      → ∀ {ℓ} → blame ℓ ∈ mem V' → inl V ↝⟨ csum c d ⟩↝ blame ℓ
    ⟦csum⟧-inr-ok : ∀{V V'}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → ¬ (hasBlame V') → V ↝⟨ d ⟩₊↝ V'
      → inr V ↝⟨ csum c d ⟩↝ inr V'
    ⟦csum⟧-inr-fail : ∀{V V'}{A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}
      → hasBlame V' → V ↝⟨ d ⟩₊↝ V'
      → ∀ {ℓ} → blame ℓ  ∈ mem V' → inr V ↝⟨ csum c d ⟩↝ blame ℓ
    ⟦cseq⟧ : ∀{u v w : Val}{A B C : Type}{c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}
      →   u ↝⟨ c ⟩↝ v    →   v ↝⟨ d ⟩↝ w
      → u ↝⟨ cseq c d ⟩↝ w

  𝒞⟨_⟩ : ∀ {A B} → (c : Cast (A ⇒ B)) → 𝒫 Val → 𝒫 Val
  𝒞⟨ c ⟩ D v = Σ[ u ∈ Val ] u ∈ D × u ↝⟨ c ⟩↝ v


  coerce-preserves-type : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ u v → u ↝⟨ c ⟩↝ v → ⟦ u ∶ A ⟧ → ⟦ v ∶ B ⟧
  coerce-preserves-type₊ : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ U V → U ↝⟨ c ⟩₊↝ V → ⟦ U ∶ A ⟧₊ → ⟦ V ∶ B ⟧₊
  coerce-preserves-type₊ c .[] .[] [] V∶A = tt
  coerce-preserves-type₊ c (u ∷ U) (v ∷ V) (x ∷ U↝V) ⟨ u∶A , U∶A ⟩ = 
    ⟨ coerce-preserves-type c u v x u∶A , coerce-preserves-type₊ c U V U↝V U∶A ⟩
  coerce-preserves-type id u .u ⟦id⟧ u∶A = u∶A
  coerce-preserves-type (inj _) u .u  ⟦inj⟧ u∶A = tt
  coerce-preserves-type {B = B} (proj _ x {g = g}) u .u (⟦proj⟧-ok x₁) u∶A = 𝐺-sound B g u x₁
  coerce-preserves-type {B = B} (proj _ x) u .(blame x) (⟦proj⟧-fail x₁) u∶A = ⟦blame∶τ⟧ B
  coerce-preserves-type {A = A ⇒ B} {B = A' ⇒ B'} (cfun c d) (V ↦ w) (V' ↦ w') 
    (⟦cfun⟧ x u↝v) V∶A→w∶B V'∶A' = coerce-preserves-type d w w' u↝v 
         (V∶A→w∶B (coerce-preserves-type₊ c V' V x V'∶A'))
  coerce-preserves-type (cpair c c₁) (fst u) (fst v) (⟦cpair⟧-fst-ok ¬b u↝v) u∶A = 
    coerce-preserves-type c u v u↝v u∶A
  coerce-preserves-type (cpair c c₁) (snd u) (snd v) (⟦cpair⟧-snd-ok ¬b u↝v) u∶A = 
    coerce-preserves-type c₁ u v u↝v u∶A
  coerce-preserves-type {B = B} (cpair c c₁) (fst u) (blame ℓ) (⟦cpair⟧-fst-fail u↝v) u∶A = tt
  coerce-preserves-type {B = B} (cpair c c₁) (snd u) (blame ℓ) (⟦cpair⟧-snd-fail u↝v) u∶A = tt
  coerce-preserves-type (csum c c₁) (inl x) (inl x₁) (⟦csum⟧-inl-ok ¬b x₂) u∶A = 
    coerce-preserves-type₊ c x x₁ x₂ u∶A
  coerce-preserves-type (csum c c₁) (inr x) (inr x₁) (⟦csum⟧-inr-ok ¬b x₂) u∶A = 
    coerce-preserves-type₊ c₁ x x₁ x₂ u∶A
  coerce-preserves-type (csum c c₁) (inl x) (blame ℓ) (⟦csum⟧-inl-fail hasb x₂ ℓ∈) u∶A = tt
  coerce-preserves-type (csum c c₁) (inr x) (blame ℓ) (⟦csum⟧-inr-fail hasb x₂ ℓ∈) u∶A = tt
  coerce-preserves-type (cseq c d) u w (⟦cseq⟧ {v = v} u↝v v↝w) u∶A =
     coerce-preserves-type d v w v↝w (coerce-preserves-type c u v u↝v u∶A) 


  open import Denot.CastStructure

  instance 
    dcs : DenotCastStruct
    dcs = record 
            { cast = cs
            ; _↝⟨_⟩↝_ = _↝⟨_⟩↝_ }