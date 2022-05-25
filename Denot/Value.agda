

module Denot.Value where

open import Data.Empty using (⊥-elim; ⊥)
open import Data.List using (List ; _∷_ ; []; _++_; length)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
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
  const : {B : Base} → rep-base B → Val  {- A primitive constant of type B. -}
  _↦_ : List Val → Val → Val             {- one entry in a function's graph -}
  ν : Val                                {- empty function -}
  fst : Val → Val                        {- first component of a pair -}
  snd : Val → Val                        {- second component of a pair -}
  inl : List Val → Val                   {- right injection of a sum -}
  inr : List Val → Val                   {- left injection of a sum -}
  blame : Label → Val



{- typing of denotational values -}
⟦_∶_⟧ : (v : Val) → (τ : Type) → Set
⟦_∶_⟧₊ : (V : List Val) → (τ : Type) → Set
⟦ [] ∶ τ ⟧₊ = ⊤
⟦ (v ∷ V) ∶ τ ⟧₊ = ⟦ v ∶ τ ⟧ × ⟦ V ∶ τ ⟧₊
⟦ v ∶ ⋆ ⟧ = ⊤
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


⟦blame∶τ⟧ : ∀ τ {ℓ} → ⟦ blame ℓ ∶ τ ⟧
⟦blame∶τ⟧ ⋆ = tt
⟦blame∶τ⟧ (` x) = tt
⟦blame∶τ⟧ (τ ⇒ τ₁) = tt
⟦blame∶τ⟧ (τ `× τ₁) = tt
⟦blame∶τ⟧ (τ `⊎ τ₁) = tt

⟦V∶⋆⟧₊ : ∀ {V} → ⟦ V ∶ ⋆ ⟧₊
⟦V∶⋆⟧₊ {[]} = tt
⟦V∶⋆⟧₊ {x ∷ V} = tt , ⟦V∶⋆⟧₊

⟦_∶_⟧? : ∀ v τ → Dec (⟦ v ∶ τ ⟧)
⟦_∶_⟧₊? : ∀ V τ → Dec (⟦ V ∶ τ ⟧₊)
⟦ [] ∶ τ ⟧₊? = yes tt
⟦ v ∷ V ∶ τ ⟧₊? = ⟦ v ∶ τ ⟧? ×-dec ⟦ V ∶ τ ⟧₊? 
⟦ v ∶ ⋆ ⟧? = yes tt
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
⟦ const x ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ fst v ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ snd v ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ inl x ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ inr x ∶ τ ⇒ τ₁ ⟧? = no (λ z → z)
⟦ const x ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ x ↦ v ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ ν ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ inl x ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ inr x ∶ τ `× τ₁ ⟧? = no (λ z → z)
⟦ const x ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ x ↦ v ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ ν ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ fst v ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)
⟦ snd v ∶ τ `⊎ τ₁ ⟧? = no (λ z → z)


{-
⟦ const {B} k ∶ ` B' ⟧ with base-eq? B B'
... | yes refl = ⊤
... | no neq = ⊥
⟦ const {B} k ∶ τ ⟧ = ⊥
⟦ blame ℓ ∶ τ ⟧ = ⊤   {- want types for this? -}
⟦ ν ∶ σ ⇒ τ ⟧ = ⊤
⟦ ν ∶ τ ⟧ = ⊥
⟦ V ↦ w ∶ σ ⇒ τ ⟧ = ⟦ V ∶ σ ⟧₊ → ⟦ w ∶ τ ⟧
⟦ V ↦ w ∶ τ ⟧ = ⊥
⟦ fst v ∶ σ `× τ ⟧ = ⟦ v ∶ σ ⟧
⟦ fst v ∶ τ ⟧ = ⊥
⟦ snd v ∶ σ `× τ ⟧ = ⟦ v ∶ τ ⟧
⟦ snd v ∶ τ ⟧ = ⊥
⟦ inl V ∶ σ `⊎ τ ⟧ = ⟦ V ∶ σ ⟧₊
⟦ inl V ∶ τ ⟧ = ⊥
⟦ inr V ∶ σ `⊎ τ ⟧ = ⟦ V ∶ τ ⟧₊
⟦ inr V ∶ τ ⟧ = ⊥ -}
{-

⟦_∶_⟧ : (v : Val) → (τ : Type) → Set
⟦_∶_⟧₊ : (V : List Val) → (τ : Type) → Set
⟦ [] ∶ τ ⟧₊ = ⊤
⟦ (v ∷ V) ∶ τ ⟧₊ = ⟦ v ∶ τ ⟧ × ⟦ V ∶ τ ⟧₊
⟦ const {B} k ∶ ` B' ⟧ with base-eq? B B'
... | yes refl = ⊤
... | no neq = ⊥
⟦ const {B} k ∶ τ ⟧ = ⊥
⟦ blame ℓ ∶ τ ⟧ = ⊤   {- want types for this? -}
⟦ ν ∶ σ ⇒ τ ⟧ = ⊤
⟦ ν ∶ τ ⟧ = ⊥
⟦ V ↦ w ∶ σ ⇒ τ ⟧ = ⟦ V ∶ σ ⟧₊ × ⟦ w ∶ τ ⟧
⟦ V ↦ w ∶ τ ⟧ = ⊥
⟦ fst v ∶ σ `× τ ⟧ = ⟦ v ∶ σ ⟧
⟦ fst v ∶ τ ⟧ = ⊥
⟦ snd v ∶ σ `× τ ⟧ = ⟦ v ∶ τ ⟧
⟦ snd v ∶ τ ⟧ = ⊥
⟦ inl V ∶ σ `⊎ τ ⟧ = ⟦ V ∶ σ ⟧₊
⟦ inl V ∶ τ ⟧ = ⊥
⟦ inr V ∶ σ `⊎ τ ⟧ = ⟦ V ∶ τ ⟧₊
⟦ inr V ∶ τ ⟧ = ⊥




data `⟦_∶_⟧ : (v : Val) → (τ : Type) → Set
data `⟦_∶_⟧₊ : (V : List Val) → (τ : Type) → Set where
   [] : ∀ {τ} → `⟦ [] ∶ τ ⟧₊
   _∷_ : ∀ {v}{V}{τ} → `⟦ v ∶ τ ⟧ → `⟦ V ∶ τ ⟧₊ → `⟦ (v ∷ V) ∶ τ ⟧₊
data `⟦_∶_⟧ where
  Const : ∀ {B} k → `⟦ const {B} k ∶ ` B ⟧
  Blame : ∀ ℓ → `⟦ blame ℓ ∶ ⋆ ⟧
  Fun : ∀ {V w σ τ} → `⟦ V ∶ σ ⟧₊ → `⟦ w ∶ τ ⟧ → `⟦ V ↦ w ∶ σ ⇒ τ ⟧
  Prod-fst : ∀ {v σ τ} → `⟦ v ∶ σ ⟧ → `⟦ fst v ∶ σ `× τ ⟧
  Prod-snd : ∀ {v σ τ} → `⟦ v ∶ τ ⟧ → `⟦ snd v ∶ σ `× τ ⟧
  Sum-inl : ∀ {V σ τ} → `⟦ V ∶ σ ⟧₊ → `⟦ inl V ∶ σ `⊎ τ ⟧
  Sum-inr : ∀ {V σ τ} → `⟦ V ∶ τ ⟧₊ → `⟦ inr V ∶ σ `⊎ τ ⟧

-}



⟦∶⟧₊→All : ∀ {A V} → ⟦ V ∶ A ⟧₊ → All (λ v → ⟦ v ∶ A ⟧) V
⟦∶⟧₊→All {V = []} tt = []
⟦∶⟧₊→All {V = (v ∷ V)} (v∶A , V∶A) = v∶A ∷ ⟦∶⟧₊→All V∶A

⟦∶⟧₊→∈ : ∀ {A V} → ⟦ V ∶ A ⟧₊ → ∀ v → v ∈ mem V → ⟦ v ∶ A ⟧
⟦∶⟧₊→∈ V∶A v = lookup (⟦∶⟧₊→All V∶A) {v}
  
{- Abstraction  ---------------------------------------------------------------}

data Λ : (𝒫 Val → 𝒫 Val) → 𝒫 Val where
  Λ-↦ : ∀{f V w}
     → w ∈ f (mem V)
     → V ≢ []  {- call by value -}
     → (V ↦ w) ∈ Λ f 
  Λ-ν : ∀{f} → ν ∈ Λ f


Λ-mono : ∀ {F F' : 𝒫 Val → 𝒫 Val} → 
    (∀ D D' → D ⊆ D' → F D ⊆ F' D') → Λ F ⊆ Λ F'
Λ-mono {F} {F'} F⊆ (V ↦ d) (Λ-↦ x₁ x₂) = 
  Λ-↦ (F⊆ (mem V) (mem V) (λ d z → z) d x₁) x₂
Λ-mono {F} {F'} F⊆ ν Λ-ν = Λ-ν

{- Application -----------------------------------------------------------------}

infix 6 _∗_
data _∗_ : 𝒫 Val → 𝒫 Val → 𝒫 Val where
   ∗-app : ∀ {D₁ D₂ V w}
      → (V ↦ w) ∈ D₁
      → mem V ⊆ D₂
      → w ∈ (D₁ ∗ D₂)
   ∗-blame-rator : ∀ {D₁ D₂ ℓ}
      → blame ℓ ∈ D₁
      → blame ℓ ∈ (D₁ ∗ D₂) 
   ∗-blame-rand : ∀ {D₁ D₂ ℓ}
      → blame ℓ ∈ D₂
      → blame ℓ ∈ (D₁ ∗ D₂) 

∗-mono : ∀ {D E D' E'} → D ⊆ D' → E ⊆ E' → (D ∗ E) ⊆ (D' ∗ E')
∗-mono {D}{E}{D'}{E'} D⊆ E⊆ d (∗-app {V = V} x x₁) = 
  ∗-app (D⊆ (V ↦ d) x) (λ d z → E⊆ d (x₁ d z))
∗-mono {D}{E}{D'}{E'} D⊆ E⊆ (blame ℓ) (∗-blame-rator x) = 
  ∗-blame-rator (D⊆ (blame ℓ) x)
∗-mono {D}{E}{D'}{E'} D⊆ E⊆ (blame ℓ) (∗-blame-rand x) = 
  ∗-blame-rand (E⊆ (blame ℓ) x)

{- Pairs -}

data pair : 𝒫 Val → 𝒫 Val → 𝒫 Val where
   pair-fst : ∀ {D E u v}
      → u ∈ D → v ∈ E
      → fst u ∈ pair D E
   pair-snd : ∀ {D E u v}
      → u ∈ D → v ∈ E
      → snd v ∈ pair D E
   pair-blame-fst : ∀ {D E ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ pair D E
   pair-blame-snd : ∀ {D E ℓ}
      → blame ℓ ∈ E
      → blame ℓ ∈ pair D E

pair-mono : ∀ {D E D' E'} → D ⊆ D' → E ⊆ E' → (pair D E) ⊆ (pair D' E')
pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (fst u) (pair-fst {v = v} x x₁) = 
  pair-fst (D⊆ u x) (E⊆ v x₁)
pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (snd v) (pair-snd {u = u} x x₁) = 
  pair-snd (D⊆ u x) (E⊆ v x₁)
pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (blame ℓ) (pair-blame-fst x) = 
  pair-blame-fst (D⊆ (blame ℓ) x)
pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (blame ℓ) (pair-blame-snd x) = 
  pair-blame-snd (E⊆ (blame ℓ) x)

data car : 𝒫 Val → 𝒫 Val where
   car-fst : ∀ {D u}
      → fst u ∈ D
      → u ∈ car D
   car-blame : ∀ {D ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ car D

car-mono : ∀ {D D'} → D ⊆ D' → car D ⊆ car D'
car-mono {D} {D'} D⊆ d (car-fst x) = car-fst (D⊆ (fst d) x)
car-mono {D} {D'} D⊆ (blame ℓ) (car-blame x) = car-blame (D⊆ (blame ℓ) x)

data cdr : 𝒫 Val → 𝒫 Val where
   cdr-snd : ∀ {D u}
      → snd u ∈ D
      → u ∈ cdr D
   cdr-blame : ∀ {D ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ cdr D

cdr-mono : ∀ {D D'} → D ⊆ D' → cdr D ⊆ cdr D'
cdr-mono {D} {D'} D⊆ d (cdr-snd x) = cdr-snd (D⊆ (snd d) x)
cdr-mono {D} {D'} D⊆ (blame ℓ) (cdr-blame x) = cdr-blame (D⊆ (blame ℓ) x)

{- Sums -}

data inleft : 𝒫 Val → 𝒫 Val where
  inleft-inl : ∀{V D} → mem V ⊆ D → inl V ∈ inleft D
  inleft-blame : ∀{ℓ D} → blame ℓ ∈ D → blame ℓ ∈ inleft D

inleft-mono : ∀ {D D'} → D ⊆ D' → inleft D ⊆ inleft D'
inleft-mono {D} {D'} D⊆ (inl x) (inleft-inl x₁) = inleft-inl (λ d z → D⊆ d (x₁ d z))
inleft-mono {D} {D'} D⊆ (blame x) (inleft-blame x₁) = inleft-blame (D⊆ (blame x) x₁)

data inright : 𝒫 Val → 𝒫 Val where
  inright-inr : ∀{V D} → mem V ⊆ D → inr V ∈ inright D
  inright-blame : ∀{ℓ D} → blame ℓ ∈ D → blame ℓ ∈ inright D

inright-mono : ∀ {D D'} → D ⊆ D' → inright D ⊆ inright D'
inright-mono {D} {D'} D⊆ (inr x) (inright-inr x₁) = inright-inr (λ d z → D⊆ d (x₁ d z))
inright-mono {D} {D'} D⊆ (blame x) (inright-blame x₁) = inright-blame (D⊆ (blame x) x₁)

data cond : 𝒫 Val → (𝒫 Val → 𝒫 Val) → (𝒫 Val → 𝒫 Val) → 𝒫 Val where
  cond-inl : ∀{D F₁ F₂ V w}
    → inl V ∈ D  → w ∈ F₁ (mem V) → w ∈ cond D F₁ F₂
  cond-inr : ∀{D F₁ F₂ V w}
    → inr V ∈ D  → w ∈ F₂ (mem V) → w ∈ cond D F₁ F₂
  cond-blame : ∀{D F₁ F₂ ℓ}
    → blame ℓ ∈ D  →  blame ℓ ∈ cond D F₁ F₂

cond-mono :  ∀ {T D E T' D' E'} → T ⊆ T' 
          → (∀ a a' → a ⊆ a' → D a ⊆ D' a') → (∀ b b' → b ⊆ b' → E b ⊆ E' b') 
          → cond T D E ⊆ cond T' D' E'
cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (cond-inl {V = V} x x₁) = 
  cond-inl (T⊆ (inl V) x) (D⊆ (mem V) (mem V) (λ d z → z) d x₁)
cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (cond-inr {V = V} x x₁) = 
  cond-inr (T⊆ (inr V) x) (E⊆ (mem V) (mem V) (λ d z → z) d x₁)
cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ (blame ℓ) (cond-blame x) = 
  cond-blame (T⊆ (blame ℓ) x)

{- Primitive operators ------------------------------------------------}

data ℘ : ∀{A} (P : Prim A) → rep A → 𝒫 Val where
  ℘-base : ∀{B k} → (const {B} k) ∈ ℘ (P-Base {B}) k 
  ℘-fun : ∀{A B P f k w}
       → w ∈ ℘ {A} P (f k)
       → (((const {B} k) ∷ []) ↦ w) ∈ ℘ (P-Fun {B} P) f
  ℘-ν : ∀{A B P f} → ν ∈ ℘ (P-Fun {A}{B} P) f

{- conditional operator for Bool -}
data If : 𝒫 Val → 𝒫 Val → 𝒫 Val → 𝒫 Val where
  If-then : ∀{D E₁ E₂ w}
    → (const true) ∈ D → w ∈ E₁ → w ∈ If D E₁ E₂
  If-else : ∀{D E₁ E₂ w}
    → (const false) ∈ D → w ∈ E₂ → w ∈ If D E₁ E₂
  If-blame : ∀{D E₁ E₂ ℓ}
    → blame ℓ ∈ D  →  blame ℓ ∈ If D E₁ E₂

If-mono : ∀ {T D E T' D' E'} → T ⊆ T' → D ⊆ D' → E ⊆ E' → If T D E ⊆ If T' D' E'
If-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (If-then x x₁) = 
  If-then (T⊆ (const true) x) (D⊆ d x₁)
If-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (If-else x x₁) = 
  If-else (T⊆ (const false) x) (E⊆ d x₁)
If-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ (blame ℓ) (If-blame x) = 
  If-blame (T⊆ (blame ℓ) x)

ℬ : (ℓ : Label) → 𝒫 Val
ℬ ℓ (blame ℓ') = ℓ' ≡ ℓ
ℬ ℓ v = ⊥




{- Single value operators, can be useful for abbreviated blame handling  ---- -}

δb : Val → Val → Val
δb (blame ℓ) w = blame ℓ
δb v w = w


fst-val : Val → Val
fst-val (blame ℓ) = blame ℓ
fst-val v = fst v

snd-val : Val → Val
snd-val (blame ℓ) = blame ℓ
snd-val v = snd v


isBlame : Val → Set
isBlame (blame ℓ) = ⊤
isBlame v = ⊥

hasBlame : List Val → Set
hasBlame V = Any isBlame V

blame? : ∀ v → Dec (isBlame v)
blame? (blame ℓ) = yes tt
blame? (const x) = no (λ z → z)
blame? (x ↦ v) = no (λ z → z)
blame? ν = no (λ z → z)
blame? (fst v) = no (λ z → z)
blame? (snd v) = no (λ z → z)
blame? (inl x) = no (λ z → z)
blame? (inr x) = no (λ z → z)

blame₊? : ∀ V → Dec (hasBlame V)
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
Blameless (blame x) = ⊥




{- -- cast, wrap, and blame for the cast calculus --------------------------- -}


{-

module Casts (cs : CastStruct) where
  open CastStruct cs

  infix 7 _⟨∣_∣⟩

{- initial implementation doesn't take into account "value" sidecondition,
   and assumes that the cast is Active -}
  _⟨∣_∣⟩ : ∀ {A B} (D : 𝒫 Val) → (c : Cast (A ⇒ B)) → 𝒫 Val
  D ⟨∣ c ∣⟩

{-
    applyCast : ∀ {Γ A B} → (V : Term) → Γ ⊢ V ⦂ A → Value V → (c : Cast (A ⇒ B))
                          → {a : Active c} → Term

     {- active might be helpful to restrict us to a subset of the casts 
      but the value sidecondition won't affect us denotationally -}
    ApplyCast c ⟦ V ⟧ typing (corresponding stuff)  =  ⟦ applyCast V c stuff ⟧                          
-}

{-
   cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
      → (v : Value V) → {a : Active c}
        ------------------------------
      → V ⟨ c ⟩ —→ applyCast V v c {a}
-}


{-  open import ParamCastCalculusABT precast
    open import ParamCastAuxABT precast -}


  --   ⊢cast : ∀ {Γ A B} {M}
  --     → Γ ⊢ M ⦂ A
  --     → (c : Cast (A ⇒ B))
  --       --------------------
  --     → Γ ⊢ M ⟨ c ⟩ ⦂ B

  --   ⊢wrap : ∀ {Γ A B} {M}
  --     → Γ ⊢ M ⦂ A
  --     → (c : Cast (A ⇒ B))
  --     → (i : Inert c)
  --       ---------------------
  --     → Γ ⊢ M ⟨ c ₍ i ₎⟩ ⦂ B


  --   ⊢blame : ∀ {Γ A} {ℓ}
  --       -----------------
  --     → Γ ⊢ blame ℓ ⦂ A

{-
   cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
      → (v : Value V) → {a : Active c}
        ------------------------------
      → V ⟨ c ⟩ —→ applyCast V v c {a}

    wrap : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
      → (v : Value V) → {i : Inert c}
        ------------------------------
      → V ⟨ c ⟩ —→ V ⟪ i ⟫

    -- Fire the following rules when the cast is both cross and inert.
    fun-cast : ∀ {Γ A' B' A₁ A₂} {V : Γ ⊢ A₁ ⇒ A₂} {W : Γ ⊢ A'}
                                 {c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))}
      → (v : Value V) → Value W
      → {x : Cross c} → {i : Inert c}
        --------------------------------------------------
      → (V ⟪ i ⟫) · W —→ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩

    fst-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
                               {c : Cast ((A `× B) ⇒ (A' `× B'))}
      → Value V
      → {x : Cross c} → {i : Inert c}
        -------------------------------------
      → fst (V ⟪ i ⟫) —→ (fst V) ⟨ fstC c x ⟩

    snd-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
                               {c : Cast ((A `× B) ⇒ (A' `× B'))}
      → Value V
      → {x : Cross c} → {i : Inert c}
        -------------------------------------
      → snd (V ⟪ i ⟫) —→ (snd V) ⟨ sndC c x ⟩

    case-cast : ∀ {Γ A B A' B' C} {V : Γ ⊢ A `⊎ B}
                                  {M : Γ , A' ⊢ C } {N : Γ , B' ⊢ C}
                                  {c : Cast (A `⊎ B ⇒ A' `⊎ B')}
      → Value V
      → {x : Cross c} → {i : Inert c}
        --------------------------------------------
      → case (V ⟪ i ⟫) M N —→
         case V (rename (ext S_) M [ ` Z ⟨ inlC c x ⟩ ]) (rename (ext S_) N [ ` Z ⟨ inrC c x ⟩ ])
         -- case V (ƛ ((rename S_ W₁) · ((` Z) ⟨ inlC c x ⟩ ))) (ƛ ((rename S_ W₂) · ((` Z) ⟨ inrC c x ⟩ )))
-}
-}