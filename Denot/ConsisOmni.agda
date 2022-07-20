{-# OPTIONS --allow-unsolved-metas #-}

module Denot.ConsisOmni where

open import Data.Empty using (⊥-elim; ⊥)
open import Data.List using (List ; _∷_ ; []; _++_; length)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Labels
open import PrimitiveTypes using (Base)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Implication using (_→-dec_)
open import SetsAsPredicates
open import Types
open import Denot.Value

infix 5 _∼_
infix 5 _∼₊_

_∼_ : (u : Val) → (v : Val) → Set
_∼₊_ : (u : Val) → (V : List Val) → Set
_≈₊_ : (U : List Val) → (V : List Val) → Set
const {ι} k ∼ const {ι'} k' = Σ[ ι≡ ∈ ι ≡ ι' ] subst base-rep ι≡ k ≡ k'
const k ∼ blame ℓ = ⊤
const k ∼ v = ⊥
(V ↦ w) ∼ ν = ⊤
(V ↦ w) ∼ blame ℓ = ⊤
(V ↦ w) ∼ V' ↦ w' = V ≈₊ V' × w ∼ w' ⊎ ¬ (V ≈₊ V')
(V ↦ w) ∼ v = ⊥
ν ∼ ν = ⊤
ν ∼ blame ℓ = ⊤
ν ∼ (V' ↦ w') = ⊤
ν ∼ v = ⊥
fst u ∼ fst v = u ∼ v
fst u ∼ snd v = ⊤
fst u ∼ blame ℓ = ⊤
fst u ∼ v = ⊥
snd u ∼ snd v = u ∼ v
snd u ∼ fst v = ⊤
snd u ∼ blame ℓ = ⊤
snd u ∼ v = ⊥
inl U ∼ inl V = U ≈₊ V
inl U ∼ (blame ℓ) = ⊤
inl U ∼ v = ⊥
inr U ∼ inr V = U ≈₊ V
inr U ∼ blame ℓ = ⊤
inr U ∼ v = ⊥
blame ℓ ∼ v = ⊤
u ∼₊ [] = ⊤
u ∼₊ (v ∷ V) = u ∼ v × u ∼₊ V
U ≈₊ V = All (_∼₊ V) U



scD : 𝒫 Val → Set
scD D = ∀ u v → u ∈ D → v ∈ D → u ∼ v

scD-1 : (𝒫 Val → 𝒫 Val) → Set₁
scD-1 F = ∀ D → scD D → scD (F D)

monoD-1 : (F F' : 𝒫 Val → 𝒫 Val) → Set₁
monoD-1 F F' = ∀ D D' → scD D' → D ⊆ D' → F D ⊆ F' D'

∼-Type : ∀ {u v A} → ⟦ u ∶ A ⟧ → u ∼ v → ⟦ v ∶ A ⟧
∼-Type₊ : ∀ {U V A} → ⟦ U ∶ A ⟧₊ → U ≈₊ V → ⟦ V ∶ A ⟧₊
∼-Type {const k} {v} {A} u∶A u∼v = {!   !}
∼-Type {V ↦ u} {v} {A} u∶A u∼v = {!   !}
∼-Type {ν} {v} {A} u∶A u∼v = {!   !}
∼-Type {fst u} {v} {A} u∶A u∼v = {!   !}
∼-Type {snd u} {v} {A} u∶A u∼v = {!   !}
∼-Type {inl V} {v} {A} u∶A u∼v = {!   !}
∼-Type {inr V} {v} {A} u∶A u∼v = {!   !}
∼-Type {blame ℓ} {v} {A} u∶A u∼v = {!   !}
∼-Type₊ {U}{V}{A} U∶A U∼V = {!   !}

data ∼-Class : Set where
  [bl_] : (ℓ : Label) → ∼-Class
  [const_] : ∀ {ι} (k : base-rep ι) → ∼-Class
  [_×_] : ([A] : ∼-Class) → ([B] : ∼-Class) → ∼-Class
  [_⊎_] : ([A] : ∼-Class) → ([B] : ∼-Class) → ∼-Class
  [_⇒_] : ([A] : ∼-Class) → ([B] : ∼-Class) → ∼-Class

_[∼]_ : (u : Val) → ([v] : ∼-Class) → Set
(blame ℓ) [∼] [bl ℓ' ] = ℓ ≡ ℓ'
u [∼] [bl ℓ' ] = ⊥
u [∼] [const_] {ι'} k' = {!   !}
u [∼] [ [v] × [v]₁ ] = {!   !}
u [∼] [ [v] ⊎ [v]₁ ] = {!   !}
u [∼] [ [v] ⇒ [v]₁ ] = {!   !}

