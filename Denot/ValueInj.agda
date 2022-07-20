{-# OPTIONS --allow-unsolved-metas #-}

module Denot.ValueInj where

open import Data.Empty using (⊥-elim; ⊥)
open import Data.List using (List ; _∷_ ; []; _++_; length)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; tabulate)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Labels
open import PrimitiveTypes using (Base)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Implication using (_→-dec_)
open import SetsAsPredicates
open import Types

data Val : Set where
  inj : (A : Type) → (v : Val) → Val
  const : {B : Base} → (k : rep-base B) → Val  {- A primitive constant of type B. -}
  _↦_ : (V : List Val) → (w : Val) → Val       {- one entry in a function's graph -}
  ν : Val                                      {- empty function -}
  fst : (u : Val) → Val                        {- first component of a pair -}
  snd : (v : Val) → Val                        {- second component of a pair -}
  inl : (V : List Val) → Val                   {- right injection of a sum -}
  inr : (V : List Val) → Val                   {- left injection of a sum -}
  blame : (ℓ : Label) → Val

{- =========================================================================
   Denotational Typing
  ========================================================================= -}

data InjType : Type → Set where
  I` : ∀ ι → InjType (` ι)
  I⋆ : ∀ (A : Type) → InjType ⋆
  _I⇒_ : ∀ {σ τ} → InjType σ → InjType τ → InjType (σ ⇒ τ)
  _I×_ : ∀ {σ τ} → InjType σ → InjType τ → InjType (σ `× τ)
  _I⊎_ : ∀ {σ τ} → InjType σ → InjType τ → InjType (σ `⊎ τ)

⟦_∶_⟧ : (v : Val) → (τ : Type) → Set
⟦_∶_⟧₊ : (V : List Val) → (τ : Type) → Set
⟦ [] ∶ τ ⟧₊ = ⊤
⟦ (v ∷ V) ∶ τ ⟧₊ = ⟦ v ∶ τ ⟧ × ⟦ V ∶ τ ⟧₊
⟦ inj A v ∶ ⋆ ⟧ = ⟦ v ∶ A ⟧
⟦ blame ℓ ∶ ⋆ ⟧ = ⊤
⟦ v ∶ ⋆ ⟧ = ⊥
⟦ (const {b'} k) ∶ ` b ⟧ with base-eq? b b'
... | yes refl = ⊤
... | no neq = ⊥
⟦ blame ℓ ∶ ` b ⟧ = ⊤
⟦ v ∶ ` b ⟧ = ⊥
⟦ ν ∶ σ ⇒ τ ⟧ = ⊤
⟦ V ↦ w ∶ σ ⇒ τ ⟧ = ⟦ V ∶ σ ⟧₊ → ⟦ w ∶ τ ⟧
⟦ blame ℓ ∶ σ ⇒ τ ⟧ = ⊤
⟦ v ∶ σ ⇒ τ ⟧ = ⊥
⟦ fst v ∶ σ `× τ ⟧ = ⟦ v ∶ σ ⟧
⟦ snd v ∶ σ `× τ ⟧ = ⟦ v ∶ τ ⟧
⟦ blame ℓ ∶ σ `× τ ⟧ = ⊤
⟦ v ∶ σ `× τ ⟧ = ⊥
⟦ inl V ∶ σ `⊎ τ ⟧ = ⟦ V ∶ σ ⟧₊
⟦ inr V ∶ σ `⊎ τ ⟧ = ⟦ V ∶ τ ⟧₊
⟦ blame ℓ ∶ σ `⊎ τ ⟧ = ⊤
⟦ v ∶ σ `⊎ τ ⟧ = ⊥

⟦_I∶_⟧ : (v : Val) → ∀ {τ} → (Iτ : InjType τ) → Set
⟦_I∶_⟧₊ : (V : List Val) → ∀ {τ} → (Iτ : InjType τ) → Set
⟦ [] I∶ τ ⟧₊ = ⊤
⟦ (v ∷ V) I∶ τ ⟧₊ = ⟦ v I∶ τ ⟧ × ⟦ V I∶ τ ⟧₊
⟦ inj A' v I∶ I⋆ A ⟧ = A' ≡ A × ⟦ v ∶ A ⟧
⟦ blame ℓ I∶ I⋆ A ⟧ = ⊤
⟦ v I∶ I⋆ A ⟧ = ⊥
⟦ (const {b'} k) I∶ I` b ⟧ with base-eq? b b'
... | yes refl = ⊤
... | no neq = ⊥
⟦ blame ℓ I∶ I` b ⟧ = ⊤
⟦ v I∶ I` b ⟧ = ⊥
⟦ ν I∶ σ I⇒ τ ⟧ = ⊤
⟦ V ↦ w I∶ σ I⇒ τ ⟧ = ⟦ V I∶ σ ⟧₊ → ⟦ w I∶ τ ⟧
⟦ blame ℓ I∶ σ I⇒ τ ⟧ = ⊤
⟦ v I∶ σ I⇒ τ ⟧ = ⊥
⟦ fst v I∶ σ I× τ ⟧ = ⟦ v I∶ σ ⟧
⟦ snd v I∶ σ I× τ ⟧ = ⟦ v I∶ τ ⟧
⟦ blame ℓ I∶ σ I× τ ⟧ = ⊤
⟦ v I∶ σ I× τ ⟧ = ⊥
⟦ inl V I∶ σ I⊎ τ ⟧ = ⟦ V I∶ σ ⟧₊
⟦ inr V I∶ σ I⊎ τ ⟧ = ⟦ V I∶ τ ⟧₊
⟦ blame ℓ I∶ σ I⊎ τ ⟧ = ⊤
⟦ v I∶ σ I⊎ τ ⟧ = ⊥

⟦blame∶τ⟧ : ∀ τ {ℓ} → ⟦ blame ℓ ∶ τ ⟧
⟦blame∶τ⟧ ⋆ = tt
⟦blame∶τ⟧ (` x) = tt
⟦blame∶τ⟧ (τ ⇒ τ₁) = tt
⟦blame∶τ⟧ (τ `× τ₁) = tt
⟦blame∶τ⟧ (τ `⊎ τ₁) = tt

⟦_∶_⟧? : ∀ v τ → Dec (⟦ v ∶ τ ⟧)
⟦_∶_⟧₊? : ∀ V τ → Dec (⟦ V ∶ τ ⟧₊)
⟦ [] ∶ τ ⟧₊? = yes tt
⟦ v ∷ V ∶ τ ⟧₊? = ⟦ v ∶ τ ⟧? ×-dec ⟦ V ∶ τ ⟧₊? 
⟦ inj A v ∶ ⋆ ⟧? = ⟦ v ∶ A ⟧?
⟦ blame ℓ ∶ τ ⟧? = yes (⟦blame∶τ⟧ τ)
⟦ const {b'} k ∶ ` b ⟧? with base-eq? b b'
... | yes refl = yes tt
... | no neq = no (λ z → z)
⟦ ν ∶ τ ⇒ τ₁ ⟧? = yes tt
⟦ V ↦ w ∶ τ ⇒ τ₁ ⟧? = ⟦ V ∶ τ ⟧₊? →-dec ⟦ w ∶ τ₁ ⟧?
⟦ fst v ∶ τ `× τ₁ ⟧? = ⟦ v ∶ τ ⟧?
⟦ snd v ∶ τ `× τ₁ ⟧? = ⟦ v ∶ τ₁ ⟧?
⟦ inl V ∶ τ `⊎ τ₁ ⟧? = ⟦ V ∶ τ ⟧₊?
⟦ inr V ∶ τ `⊎ τ₁ ⟧? = ⟦ V ∶ τ₁ ⟧₊?
⟦ x ↦ v ∶ ` b ⟧? = no (λ z → z)
⟦ ν ∶ ` b ⟧? = no (λ z → z)
⟦ fst v ∶ ` b ⟧? = no (λ z → z)
⟦ snd v ∶ ` b ⟧? = no (λ z → z)
⟦ inl x ∶ ` b ⟧? = no (λ z → z)
⟦ inr x ∶ ` b ⟧? = no (λ z → z)
⟦ inj A v ∶ ` b ⟧? = no (λ z → z)
⟦ const x ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ fst v ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ snd v ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ inl x ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ inr x ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ inj A v ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ const x ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ x ↦ v ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ ν ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ inl x ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ inr x ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ inj A v ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ const x ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ x ↦ v ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ ν ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ fst v ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ snd v ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ inj A v ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ const k ∶ ⋆ ⟧? = no (λ z → z)
⟦ V ↦ v ∶ ⋆ ⟧? = no (λ z → z)
⟦ ν ∶ ⋆ ⟧? = no (λ z → z)
⟦ fst v ∶ ⋆ ⟧? = no (λ z → z)
⟦ snd v ∶ ⋆ ⟧? = no (λ z → z)
⟦ inl V ∶ ⋆ ⟧? = no (λ z → z)
⟦ inr V ∶ ⋆ ⟧? = no (λ z → z)


∈⟦_∶_⟧ : ∀ (D : 𝒫 Val) (τ : Type) → Set
∈⟦ D ∶ τ ⟧ = ∀ d → d ∈ D → ⟦ d ∶ τ ⟧

⟦_`∶_⟧ : (ℕ → 𝒫 Val) → List Type → Set
⟦ ρ `∶ Γ ⟧ = ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧

⟦∶⟧₊→All : ∀ {A V} → ⟦ V ∶ A ⟧₊ → All (λ v → ⟦ v ∶ A ⟧) V
⟦∶⟧₊→All {V = []} tt = []
⟦∶⟧₊→All {V = (v ∷ V)} (v∶A , V∶A) = v∶A ∷ ⟦∶⟧₊→All V∶A

All→⟦∶⟧₊ : ∀ {A V} → All (λ v → ⟦ v ∶ A ⟧) V → ⟦ V ∶ A ⟧₊
All→⟦∶⟧₊ [] = tt
All→⟦∶⟧₊ (v∶A ∷ V∶A) = v∶A , All→⟦∶⟧₊ V∶A

⟦∶⟧₊→∈ : ∀ {A V} → ⟦ V ∶ A ⟧₊ → ∀ v → v ∈ mem V → ⟦ v ∶ A ⟧
⟦∶⟧₊→∈ V∶A v = lookup (⟦∶⟧₊→All V∶A) {v}

∈→⟦∶⟧₊ : ∀ {A V} → ∈⟦ mem V ∶ A ⟧ → ⟦ V ∶ A ⟧₊
∈→⟦∶⟧₊ ∈⟦memV∶A⟧ = All→⟦∶⟧₊ (tabulate λ {d} d∈ → ∈⟦memV∶A⟧ d d∈)

{- =========================================================================
   Single Value Operators and Blame Handling
  ========================================================================= -}


δb : Val → Val → Val
δb (blame ℓ) w = blame ℓ
δb v w = w

bl[_,_] : ∀ {B : Set} → (Val → B) → (Label → B) → Val → B
bl[ f , g ] (blame ℓ) = g ℓ
bl[ f , g ] v = f v

isBlame : Val → Set
isBlame (blame ℓ) = ⊤
isBlame v = ⊥

isBlame₊ : List Val → Set
isBlame₊ V = Any isBlame V

¬isBlame : Val → Set
¬isBlame v = ¬ (isBlame v)

¬isBlame₊ : List Val → Set
¬isBlame₊ V = All ¬isBlame V


¬isBlame-∈ : 𝒫 Val → Set
¬isBlame-∈ D = ∀ d → d ∈ D → ¬isBlame d

¬isBlame-⊆ : ∀ {D D' : 𝒫 Val} → D' ⊆ D → ¬isBlame-∈ D → ¬isBlame-∈ D'
¬isBlame-⊆ D'⊆D nbD d d∈ = nbD d (D'⊆D d d∈)

blame? : ∀ v → Dec (isBlame v)
blame? (blame ℓ) = yes tt
blame? (const x) = no (λ z → z)
blame? (x ↦ v) = no (λ z → z)
blame? ν = no (λ z → z)
blame? (fst v) = no (λ z → z)
blame? (snd v) = no (λ z → z)
blame? (inl x) = no (λ z → z)
blame? (inr x) = no (λ z → z)
blame? (inj A v) = no (λ z → z)

blame₊? : ∀ V → Dec (isBlame₊ V)
blame₊? V = any? blame? V

Blameless : Val → Set
Blameless₊ : List Val → Set
Blameless₊ [] = ⊤
Blameless₊ (x ∷ V) = Blameless x × Blameless₊ V
Blameless (const x) = ⊤
Blameless (x ↦ v) = Blameless v
Blameless ν = ⊤
Blameless (fst v) = Blameless v
Blameless (snd v) = Blameless v
Blameless (inl x) = Blameless₊ x
Blameless (inr x) = Blameless₊ x
Blameless (inj A v) = Blameless v
Blameless (blame x) = ⊥



{- =========================================================================
   Properties of Denotations and Operators
  ========================================================================= -}

pair-complete : ∀ (D : 𝒫 Val) → Set
pair-complete D = ((Σ[ u ∈ Val ] fst u ∈ D) → (Σ[ v ∈ Val ] snd v ∈ D))
                × ((Σ[ v ∈ Val ] snd v ∈ D) → (Σ[ u ∈ Val ] fst u ∈ D)) 

cbv-blameless-∈ : (D : 𝒫 Val) (d : Val) (d∈ : d ∈ D) → Set
cbv-blameless-∈ D (const k) d∈ = ⊤
cbv-blameless-∈ D (V ↦ d) d∈ = ⊤
cbv-blameless-∈ D ν d∈ = ⊤
cbv-blameless-∈ D (fst d) d∈ = ¬isBlame d
cbv-blameless-∈ D (snd d) d∈ = ¬isBlame d
cbv-blameless-∈ D (inl V) d∈ = ¬isBlame₊ V
cbv-blameless-∈ D (inr V) d∈ = ¬isBlame₊ V
cbv-blameless-∈ D (inj A v) d∈ = ¬isBlame v
cbv-blameless-∈ D (blame ℓ) d∈ = ⊤

cbv-blameless : (D : 𝒫 Val) → Set
cbv-blameless D = ∀ d d∈ → cbv-blameless-∈ D d d∈

infix 4 _d⊑_
infix 4 _d⊑₊_

data _d⊑_ : Val → Val → Set
data _d⊑₊_ : List Val → List Val → Set where
  [] : ∀ {V} → [] d⊑₊ V
  _∷_ : ∀ {u U v V} → v ∈ mem V → u d⊑ v → U d⊑₊ V → (u ∷ U) d⊑₊ V
data _d⊑_ where
  ⊑-const : ∀ {B k} → const {B} k d⊑ const {B} k
  ⊑-ν-ν : ν d⊑ ν
  ⊑-ν-↦ : ∀ {V w} → ν d⊑ V ↦ w
  ⊑-↦ : ∀ {U v V w} → V d⊑₊ U → v d⊑ w → U ↦ v d⊑ V ↦ w
  ⊑-fst : ∀ {u v} → u d⊑ v → fst u d⊑ fst v
  ⊑-snd : ∀ {u v} → u d⊑ v → snd u d⊑ snd v
  ⊑-inl : ∀ {U V} → U d⊑₊ V → inl U d⊑ inl V
  ⊑-blame : ∀ {ℓ} → blame ℓ d⊑ blame ℓ
    -- curious if there's a version of this last rule that works
    -- maybe with a condition like ¬(blame ℓ ∈ mem V)
  ⊑-blame-↦ : ∀ {ℓ V} → blame ℓ d⊑ V ↦ blame ℓ
