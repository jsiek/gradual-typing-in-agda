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
  𝐺⟦ τ ⟧ g ERR = True
  𝐺⟦ τ ⟧ g (Val.blame ℓ) = True
  𝐺⟦ ` b ⟧ G-Base (const {b'} k) with base-eq? b b'
  ... | yes refl = True
  ... | no neq = False
  𝐺⟦ ` b ⟧ G-Base v = False
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun ν = True
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun (V ↦ w) = True
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun v = False
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair (Val.fst v) = True
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair (Val.snd v) = True
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair v = False
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum (inl V) = True
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum (inr V) = True
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum v = False

  𝐺-sound : ∀ τ g v → v ∈ 𝐺⟦ τ ⟧ g → ⟦ v ∶ τ ⟧
  𝐺-sound τ g ERR v∈𝐺⟦τ⟧ = ⟦ERR∶τ⟧ τ
  𝐺-sound τ g (Val.blame ℓ) v∈𝐺⟦τ⟧ = ⟦blame∶τ⟧ τ
  𝐺-sound (` b) G-Base (const {b'} x) v∈𝐺⟦τ⟧ with base-eq? b b'
  ... | yes refl = tt
  ... | no neq = v∈𝐺⟦τ⟧
  𝐺-sound .(⋆ ⇒ ⋆) G-Fun (x ↦ v) v∈𝐺⟦τ⟧ = λ _ → tt
  𝐺-sound .(⋆ ⇒ ⋆) G-Fun ν v∈𝐺⟦τ⟧ = tt
  𝐺-sound .(⋆ `× ⋆) G-Pair (Val.fst v) v∈𝐺⟦τ⟧ = tt
  𝐺-sound .(⋆ `× ⋆) G-Pair (Val.snd v) v∈𝐺⟦τ⟧ = tt
  𝐺-sound .(⋆ `⊎ ⋆) G-Sum (inl x) v∈𝐺⟦τ⟧ = ⟦V∶⋆⟧₊
  𝐺-sound .(⋆ `⊎ ⋆) G-Sum (inr x) v∈𝐺⟦τ⟧ = ⟦V∶⋆⟧₊

  𝐺-adequate : ∀ τ (g : Ground τ) v → ⟦ v ∶ τ ⟧ → v ∈ 𝐺⟦ τ ⟧ g
  𝐺-adequate τ g ERR v∶τ = tt
  𝐺-adequate τ g (Val.blame ℓ) v∶τ = tt
  𝐺-adequate (` b) G-Base (const {b'} x) v∶τ with base-eq? b b'
  ... | yes refl = tt
  ... | no neq = v∶τ
  𝐺-adequate .(⋆ ⇒ ⋆) G-Fun (x ↦ v) v∶τ = tt
  𝐺-adequate .(⋆ ⇒ ⋆) G-Fun ν v∶τ = tt
  𝐺-adequate .(⋆ `× ⋆) G-Pair (Val.fst v) v∶τ = tt
  𝐺-adequate .(⋆ `× ⋆) G-Pair (Val.snd v) v∶τ = tt
  𝐺-adequate .(⋆ `⊎ ⋆) G-Sum (inl x) v∶τ = tt
  𝐺-adequate .(⋆ `⊎ ⋆) G-Sum (inr x) v∶τ = tt

  data _↝⟨_⟩↝_ : ∀ {A B} → Val → Cast (A ⇒ B) → Val → Set
  data _↝⟨_⟩₊↝_ : ∀ {A B} → (V : List Val) → (c : Cast (A ⇒ B)) → (V' : List Val) → Set where
    [] : ∀ {A B}{c : Cast (A ⇒ B)} → [] ↝⟨ c ⟩₊↝ []
    _∷_ : ∀ {A B}{c : Cast (A ⇒ B)}{v v' V V'} → v ↝⟨ c ⟩↝ v' → V ↝⟨ c ⟩₊↝ V' → (v ∷ V) ↝⟨ c ⟩₊↝ (v' ∷ V')
  data _↝⟨_⟩↝_ where
    ⟦id⟧ : ∀{v : Val}{A : Type}{a : Atomic A}
      → ⟦ v ∶ A ⟧ → v ↝⟨ id{A}{a} ⟩↝ v
    ⟦inj⟧ : ∀{v : Val}{G : Type}{g : Ground G}
      → 𝐺⟦ G ⟧ g v → v ↝⟨ inj G {g} ⟩↝ v
    ⟦proj⟧-ok : ∀{v : Val}{G : Type}{g : Ground G}{ℓ : Labels.Label}
      → 𝐺⟦ G ⟧ g v
      → v ↝⟨ proj G ℓ {g} ⟩↝ v
    ⟦proj⟧-fail : ∀{v : Val}{G : Type}{g : Ground G}{ℓ : Labels.Label}
      → ¬ 𝐺⟦ G ⟧ g v
      → v ↝⟨ proj G ℓ {g} ⟩↝ (Val.blame ℓ)
    ⟦cfun⟧ : ∀{V w V′ w′}{A B A′ B′ : Type}{c : Cast (A′ ⇒ A)}{d : Cast (B ⇒ B′)}
      → (⟦ V ∶ A ⟧₊ → ⟦ w ∶ B ⟧)
      → V′ ↝⟨ c ⟩₊↝ V   →   w ↝⟨ d ⟩↝ w′
      → (V ↦ w) ↝⟨ cfun c d ⟩↝ (V′ ↦ w′)
    ⟦cseq⟧ : ∀{u v w : Val}{A B C : Type}{c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}
      →   u ↝⟨ c ⟩↝ v    →   v ↝⟨ d ⟩↝ w
      → u ↝⟨ cseq c d ⟩↝ w


  coerce-preserves-type : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ u v → u ↝⟨ c ⟩↝ v → ⟦ u ∶ A ⟧ → ⟦ v ∶ B ⟧
  coerce-preserves-type₊ : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ U V → U ↝⟨ c ⟩₊↝ V → ⟦ U ∶ A ⟧₊ → ⟦ V ∶ B ⟧₊
  coerce-preserves-type₊ c .[] .[] [] V∶A = tt
  coerce-preserves-type₊ c (u ∷ U) (v ∷ V) (x ∷ U↝V) ⟨ u∶A , U∶A ⟩ = 
    ⟨ coerce-preserves-type c u v x u∶A , coerce-preserves-type₊ c U V U↝V U∶A ⟩
  coerce-preserves-type id u .u (⟦id⟧ x) u∶A = u∶A
  coerce-preserves-type (inj _) u .u  (⟦inj⟧ x) u∶A = tt
  coerce-preserves-type {B = B} (proj _ x {g = g}) u .u (⟦proj⟧-ok x₁) u∶A = 𝐺-sound B g u x₁
  coerce-preserves-type {B = B} (proj _ x) u .(Val.blame x) (⟦proj⟧-fail x₁) u∶A = ⟦blame∶τ⟧ B
  coerce-preserves-type {A = A ⇒ B} {B = A' ⇒ B'} (cfun c d) (V ↦ w) (V' ↦ w') 
    (⟦cfun⟧ wt x u↝v) V∶A→w∶B V'∶A' = coerce-preserves-type d w w' u↝v 
         (V∶A→w∶B (coerce-preserves-type₊ c V' V x V'∶A'))
  coerce-preserves-type (cseq c d) u w (⟦cseq⟧ {v = v} u↝v v↝w) u∶A =
     coerce-preserves-type d v w v↝w (coerce-preserves-type c u v u↝v u∶A) 


  coerce-wt-in : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ u v → u ↝⟨ c ⟩↝ v → ⟦ u ∶ A ⟧
  coerce-wt-in₊ : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ U V → U ↝⟨ c ⟩₊↝ V → ⟦ U ∶ A ⟧₊         
  coerce-wt-in₊ {A} {B} c .[] .[] [] = tt
  coerce-wt-in₊ {A} {B} c (u ∷ U) (v ∷ V) (u↝v ∷ U↝V) = 
    ⟨ coerce-wt-in c u v u↝v , coerce-wt-in₊ c U V U↝V ⟩
  coerce-wt-in {A} {.A} .id u .u (⟦id⟧ x) = x
  coerce-wt-in {A} {.⋆} .(inj A) u .u (⟦inj⟧ {g = g} x) = 𝐺-sound A g u x
  coerce-wt-in {.⋆} {B} .(proj B _) u .u (⟦proj⟧-ok {g = g} x) = tt
  coerce-wt-in {.⋆} {B} .(proj B _) u .(Val.blame _) (⟦proj⟧-fail x) = tt
  coerce-wt-in {.(_ ⇒ _)} {.(_ ⇒ _)} .(cfun _ _) .(_ ↦ _) .(_ ↦ _) 
    (⟦cfun⟧ wt x u↝v) = wt
  coerce-wt-in {A} {B} (cseq c d) u w (⟦cseq⟧ {v = v} u↝v v↝w) = 
    coerce-wt-in c u v u↝v


  coerce-wt-out : ∀ {A B} (c : Cast (A ⇒ B))
            →  ∀ u v → u ↝⟨ c ⟩↝ v → ⟦ v ∶ B ⟧
  coerce-wt-out c u v u↝v = 
    coerce-preserves-type c u v u↝v (coerce-wt-in c u v u↝v)

  coerce-wt-out₊ : ∀ {A B} (c : Cast (A ⇒ B))
            →  ∀ U V → U ↝⟨ c ⟩₊↝ V → ⟦ V ∶ B ⟧₊
  coerce-wt-out₊ c .[] .[] [] = tt
  coerce-wt-out₊ c (u ∷ U) (v ∷ V) (u↝v ∷ U↝V) = 
    ⟨ coerce-wt-out c u v u↝v , coerce-wt-out₊ c U V U↝V ⟩

  open import Denot.CastStructure

  instance 
    dcs : DenotCastStruct
    dcs = record 
            { cast = cs
            ; _↝⟨_⟩↝_ = _↝⟨_⟩↝_ }