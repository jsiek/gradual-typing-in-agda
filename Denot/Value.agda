

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


∈⟦_∶_⟧ : ∀ (D : 𝒫 Val) (τ : Type) → Set
∈⟦ D ∶ τ ⟧ = ∀ d → d ∈ D → ⟦ d ∶ τ ⟧


⟦∶⟧₊→All : ∀ {A V} → ⟦ V ∶ A ⟧₊ → All (λ v → ⟦ v ∶ A ⟧) V
⟦∶⟧₊→All {V = []} tt = []
⟦∶⟧₊→All {V = (v ∷ V)} (v∶A , V∶A) = v∶A ∷ ⟦∶⟧₊→All V∶A

⟦∶⟧₊→∈ : ∀ {A V} → ⟦ V ∶ A ⟧₊ → ∀ v → v ∈ mem V → ⟦ v ∶ A ⟧
⟦∶⟧₊→∈ V∶A v = lookup (⟦∶⟧₊→All V∶A) {v}


{- =========================================================================
   Single Value Operators and Blame Handling
  ========================================================================= -}


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

isBlame₊ : List Val → Set
isBlame₊ V = Any isBlame V

¬isBlame : Val → Set
¬isBlame v = ¬ (isBlame v)

¬isBlame₊ : List Val → Set
¬isBlame₊ V = All ¬isBlame V


blame? : ∀ v → Dec (isBlame v)
blame? (blame ℓ) = yes tt
blame? (const x) = no (λ z → z)
blame? (x ↦ v) = no (λ z → z)
blame? ν = no (λ z → z)
blame? (fst v) = no (λ z → z)
blame? (snd v) = no (λ z → z)
blame? (inl x) = no (λ z → z)
blame? (inr x) = no (λ z → z)

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

{- =========================================================================
   Denotational Operators
  ========================================================================= -}

{- Abstraction  ---------------------------------------------------------------}

data Λ : (𝒫 Val → 𝒫 Val) → 𝒫 Val where
  Λ-↦ : ∀{f V w}
     → (w∈ : w ∈ f (mem V))
     → (neV : V ≢ [])  {- call by value -}
     → (V ↦ w) ∈ Λ f 
  Λ-ν : ∀{f} → ν ∈ Λ f


Λ-mono : ∀ {F F' : 𝒫 Val → 𝒫 Val} → 
    (∀ D D' → D ⊆ D' → F D ⊆ F' D') → Λ F ⊆ Λ F'
Λ-mono {F} {F'} F⊆ (V ↦ d) (Λ-↦ x₁ x₂) = 
  Λ-↦ (F⊆ (mem V) (mem V) (λ d z → z) d x₁) x₂
Λ-mono {F} {F'} F⊆ ν Λ-ν = Λ-ν

{- Application -----------------------------------------------------------------}

infix 6 _∗_   -- written \ast
data _∗_ : 𝒫 Val → 𝒫 Val → 𝒫 Val where
   ∗-app : ∀ {D₁ D₂ V w}
      → (V↦w∈ : (V ↦ w) ∈ D₁)
      → (V⊆ : mem V ⊆ D₂)
      → w ∈ (D₁ ∗ D₂)
   ∗-blame-rator : ∀ {D₁ D₂ ℓ}
      → (bl∈ : blame ℓ ∈ D₁)
      → blame ℓ ∈ (D₁ ∗ D₂) 
   ∗-blame-rand : ∀ {D₁ D₂ ℓ}
      → (bl∈ : blame ℓ ∈ D₂)
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
      → (u∈ : u ∈ D) → (v∈ : v ∈ E) → (nbu : ¬ (isBlame u))
      → fst u ∈ pair D E
   pair-snd : ∀ {D E u v}
      → (u∈ : u ∈ D) → (v∈ : v ∈ E) → (nbv : ¬ (isBlame v))
      → snd v ∈ pair D E
   pair-blame-fst : ∀ {D E ℓ}
      → (bl∈ : blame ℓ ∈ D)
      → blame ℓ ∈ pair D E
   pair-blame-snd : ∀ {D E ℓ}
      → (bl∈ : blame ℓ ∈ E)
      → blame ℓ ∈ pair D E

pair-mono : ∀ {D E D' E'} → D ⊆ D' → E ⊆ E' → (pair D E) ⊆ (pair D' E')
pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (fst u) (pair-fst {v = v} x x₁ x₂) = 
  pair-fst (D⊆ u x) (E⊆ v x₁) x₂
pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (snd v) (pair-snd {u = u} x x₁ x₂) = 
  pair-snd (D⊆ u x) (E⊆ v x₁) x₂
pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (blame ℓ) (pair-blame-fst x) = 
  pair-blame-fst (D⊆ (blame ℓ) x)
pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (blame ℓ) (pair-blame-snd x) = 
  pair-blame-snd (E⊆ (blame ℓ) x)


data car : 𝒫 Val → 𝒫 Val where
   car-fst : ∀ {D u}
      → (fstu∈ : fst u ∈ D) → (nbu : ¬isBlame u)
      → u ∈ car D
   car-blame : ∀ {D ℓ}
      → (bl∈ : blame ℓ ∈ D)
      → blame ℓ ∈ car D

car-mono : ∀ {D D'} → D ⊆ D' → car D ⊆ car D'
car-mono {D} {D'} D⊆ d (car-fst x nbu) = car-fst (D⊆ (fst d) x) nbu
car-mono {D} {D'} D⊆ (blame ℓ) (car-blame x) = car-blame (D⊆ (blame ℓ) x)

data cdr : 𝒫 Val → 𝒫 Val where
   cdr-snd : ∀ {D v}
      → (sndv∈ : snd v ∈ D) → (nbv : ¬isBlame v)
      → v ∈ cdr D
   cdr-blame : ∀ {D ℓ}
      → (bl∈ : blame ℓ ∈ D)
      → blame ℓ ∈ cdr D

cdr-mono : ∀ {D D'} → D ⊆ D' → cdr D ⊆ cdr D'
cdr-mono {D} {D'} D⊆ d (cdr-snd x nbv) = cdr-snd (D⊆ (snd d) x) nbv
cdr-mono {D} {D'} D⊆ (blame ℓ) (cdr-blame x) = cdr-blame (D⊆ (blame ℓ) x)

{- Sums -}

data inleft : 𝒫 Val → 𝒫 Val where
  inleft-inl : ∀{V D} → (V⊆ : mem V ⊆ D) → (nbV : ¬isBlame₊ V) → inl V ∈ inleft D
  inleft-blame : ∀{ℓ D} → (bl∈ : blame ℓ ∈ D) → blame ℓ ∈ inleft D

inleft-mono : ∀ {D D'} → D ⊆ D' → inleft D ⊆ inleft D'
inleft-mono {D} {D'} D⊆ (inl x) (inleft-inl V⊆ nbV) = inleft-inl (λ d z → D⊆ d (V⊆ d z)) nbV
inleft-mono {D} {D'} D⊆ (blame x) (inleft-blame x₁) = inleft-blame (D⊆ (blame x) x₁)

data inright : 𝒫 Val → 𝒫 Val where
  inright-inr : ∀{V D} → (V⊆ : mem V ⊆ D) → (nbV : ¬isBlame₊ V) → inr V ∈ inright D
  inright-blame : ∀{ℓ D} → (bl∈ : blame ℓ ∈ D) → blame ℓ ∈ inright D

inright-mono : ∀ {D D'} → D ⊆ D' → inright D ⊆ inright D'
inright-mono {D} {D'} D⊆ (inr x) (inright-inr V⊆ nbV) = inright-inr (λ d z → D⊆ d (V⊆ d z)) nbV
inright-mono {D} {D'} D⊆ (blame x) (inright-blame x₁) = inright-blame (D⊆ (blame x) x₁)

data cond : 𝒫 Val → (𝒫 Val → 𝒫 Val) → (𝒫 Val → 𝒫 Val) → 𝒫 Val where
  cond-inl : ∀{D F₁ F₂ V w}
    → (LV∈ : inl V ∈ D) → (nbV : ¬isBlame₊ V) → (w∈ : w ∈ F₁ (mem V)) → w ∈ cond D F₁ F₂
  cond-inr : ∀{D F₁ F₂ V w}
    → (RV∈ : inr V ∈ D) → (nbV : ¬isBlame₊ V) → (w∈ : w ∈ F₂ (mem V)) → w ∈ cond D F₁ F₂
  cond-blame : ∀{D F₁ F₂ ℓ}
    → blame ℓ ∈ D → blame ℓ ∈ cond D F₁ F₂

cond-mono :  ∀ {T D E T' D' E'} → T ⊆ T' 
          → (∀ a a' → a ⊆ a' → D a ⊆ D' a') → (∀ b b' → b ⊆ b' → E b ⊆ E' b') 
          → cond T D E ⊆ cond T' D' E'
cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (cond-inl {V = V} x nbV x₁) = 
  cond-inl (T⊆ (inl V) x) nbV (D⊆ (mem V) (mem V) (λ d z → z) d x₁)
cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (cond-inr {V = V} x nbV x₁) = 
  cond-inr (T⊆ (inr V) x) nbV (E⊆ (mem V) (mem V) (λ d z → z) d x₁)
cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ (blame ℓ) (cond-blame x) = 
  cond-blame (T⊆ (blame ℓ) x)

{- Primitive operators ------------------------------------------------}

 -- written \wp
data ℘ : ∀{A} (P : Prim A) → rep A → 𝒫 Val where
  ℘-base : ∀{B k} → (const {B} k) ∈ ℘ (P-Base {B}) k 
  ℘-fun : ∀{A B P f k w}
       → w ∈ ℘ {A} P (f k)
       → (((const {B} k) ∷ []) ↦ w) ∈ ℘ (P-Fun {B} P) f
  ℘-ν : ∀{A B P f} → ν ∈ ℘ (P-Fun {A}{B} P) f

℘-typing : ∀ A (P : Prim A) f → ∀ d → ℘ P f d → ⟦ d ∶ A ⟧
℘-typing .(` ι) (P-Base {ι = ι}) k .(const k) ℘-base with base-eq? ι ι
... | no neq = ⊥-elim (neq refl)
... | yes refl = tt
℘-typing .(` ι ⇒ B) (P-Fun {ι = ι} {B = B} P) f ((const k ∷ []) ↦ w) (℘-fun x) V∶`ι = 
  ℘-typing B P (f k) w x
℘-typing .(` ι ⇒ B) (P-Fun {ι = ι} {B = B} P) f .ν ℘-ν = tt

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







open SetsAsPredicates.≃-Reasoning

{- =========================================================================
   Equational reasoning on operators; (w/o casts)
  ========================================================================= -}
{-
  We have the following operators:
   Λ , _∗_                   functions
   pair , car , cdr          pairs/products
   inleft , inright , cond   eithers/sums
   ℘ P f , If                primitives
   ℬ ℓ                       constant blame
-}


{- --- eta rules --------------------------------- -}
  
infix 5 _≃𝑓_

_≃𝑓_ : ∀ (F F' : 𝒫 Val → 𝒫 Val) → Set₁
F ≃𝑓 F' = ∀ D → F D ≃ F' D  

-- syntactic Λ-η is  ƛ C ˙ ((rename ⇑ M) · (` 0)) ≃ M
-- or, simply,  λ x . (F x) = F
-- only true for blameless values
-- needs D closed-down for ↦ case
-- needs D is Fun for ν case
Λ-η-⊆ : ∀ D → Λ (λ X → D ∗ X) ⊆ D
Λ-η-⊆ D (V ↦ w) (Λ-↦ (∗-app V↦w∈ V⊆) neV) = {! V↦w∈  !}
Λ-η-⊆ D (V ↦ .(blame _)) (Λ-↦ (∗-blame-rator bl∈) neV) = {!  !}
Λ-η-⊆ D (V ↦ .(blame _)) (Λ-↦ (∗-blame-rand bl∈) neV) = {! bl∈  !}
Λ-η-⊆ D .ν Λ-ν = {!   !}

-- going to need D is functional
Λ-η-⊇ : ∀ D → D ⊆ Λ (λ X → D ∗ X)
Λ-η-⊇ D (blame ℓ) d∈ = {!  !}
Λ-η-⊇ D ν d∈ = {!   !}
Λ-η-⊇ D (V ↦ w) d∈ = {!   !}
Λ-η-⊇ D (const k) d∈ = {!   !}
Λ-η-⊇ D d d∈ = {!   !}

Λ-η : ∀ D → Λ (λ X → D ∗ X) ≃ D
Λ-η D = ({!   !} , {!   !})

pair-η-⊆ : ∀ {D} → pair (car D) (cdr D) ⊆ D
pair-η-⊆ .(fst _) (pair-fst (car-fst fstu∈ nbu₁) v∈ nbu) = fstu∈
pair-η-⊆ .(fst (blame _)) (pair-fst (car-blame bl∈) v∈ nbu) = ⊥-elim (nbu tt)
pair-η-⊆ .(snd _) (pair-snd u∈ (cdr-snd sndv∈ nbv₁) nbv) = sndv∈
pair-η-⊆ .(snd (blame _)) (pair-snd u∈ (cdr-blame bl∈) nbv) = ⊥-elim (nbv tt)
pair-η-⊆ .(blame _) (pair-blame-fst (car-fst fstu∈ nbu)) = ⊥-elim (nbu tt)
pair-η-⊆ .(blame _) (pair-blame-fst (car-blame bl∈)) = bl∈
pair-η-⊆ .(blame _) (pair-blame-snd (cdr-snd sndv∈ nbv)) = ⊥-elim (nbv tt)
pair-η-⊆ .(blame _) (pair-blame-snd (cdr-blame bl∈)) = bl∈

pair-η : ∀ {A B D} → ∈⟦ D ∶ A `× B ⟧ → pair-complete D → cbv-blameless D
       → pair (car D) (cdr D) ≃ D
pair-η {A}{B}{D} D∶A×B pcD cbvD = (pair-η-⊆ , pair-η-⊇)
   where
   pair-η-⊇ : D ⊆ pair (car D) (cdr D)
   pair-η-⊇ d d∈ with d | (D∶A×B d d∈) | d∈
   ... | blame x | d∶A×B | d∈ = pair-blame-fst (car-blame d∈)
   ... | fst u | d∶A×B | d∈ = 
     let nbu = cbvD (fst u) d∈ in
     let (v , sndv∈) = proj₁ pcD (u , d∈) in
     let nbv = cbvD (snd v) sndv∈ in
     pair-fst (car-fst d∈ nbu) (cdr-snd sndv∈ nbv) nbu
   ... | snd v | d∶A×B | d∈ = 
     let nbv = cbvD (snd v) d∈ in
     let (u , fstu∈) = proj₂ pcD (v , d∈) in
     let nbu = cbvD (fst u) fstu∈ in
    pair-snd (car-fst fstu∈ nbu) (cdr-snd d∈ nbv) nbv


-- need D closed-down
sum-η-⊆ : ∀ D → cond D inleft inright ⊆ D
sum-η-⊆ D .(inl _) (cond-inl LV∈ nbV (inleft-inl V⊆ nbV₁)) = {!   !}
sum-η-⊆ D .(blame _) (cond-inl LV∈ nbV (inleft-blame bl∈)) = ⊥-elim {!  !}
sum-η-⊆ D .(inr _) (cond-inr RV∈ nbV (inright-inr V⊆ nbV₁)) = {!  !}
sum-η-⊆ D .(blame _) (cond-inr RV∈ nbV (inright-blame bl∈)) = ⊥-elim {!   !}
sum-η-⊆ D .(blame _) (cond-blame x) = x

-- need D to be cbv-blameless
-- and need D to be sum-typed
sum-η-⊇ : ∀ D → D ⊆ cond D inleft inright
sum-η-⊇ D (blame ℓ) d∈ = cond-blame d∈
sum-η-⊇ D (inl V) d∈ = cond-inl d∈ {!   !} (inleft-inl (λ d z → z) {!   !})
sum-η-⊇ D (inr V) d∈ = cond-inr d∈ {!   !} (inright-inr (λ d z → z) {!   !})
sum-η-⊇ D d d∈ = {!   !}


sum-η : ∀ D → cond D inleft inright ≃ D
sum-η D = {!   !}

{- --- reduction rules --------------------------- -}

Λ-β : {!   !}
Λ-β = {!   !}

car-step : {!   !}
car-step = {!   !}

cdr-step : {!   !}
cdr-step = {!   !}



{- --- apply-cast rules -------------------------- -}


