{-

  P(ω) or Engeler style graph model
  
-}

module Denot.Value where

open import Data.Empty using (⊥-elim; ⊥)
open import Data.List using (List ; _∷_ ; []; _++_; length)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
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
  ERR : Val                              {- default value for environments -}



{- typing of denotational values -}
⟦_∶_⟧ : (v : Val) → (τ : Type) → Set
⟦_∶_⟧₊ : (V : List Val) → (τ : Type) → Set
⟦ [] ∶ τ ⟧₊ = ⊤
⟦ (v ∷ V) ∶ τ ⟧₊ = ⟦ v ∶ τ ⟧ × ⟦ V ∶ τ ⟧₊
⟦ v ∶ ⋆ ⟧ = ⊤
⟦ (const {b'} k) ∶ ` b ⟧ with base-eq? b b'
... | yes refl = ⊤
... | no neq = ⊥
⟦ ERR ∶ ` b ⟧ = ⊤
⟦ blame ℓ ∶ ` b ⟧ = ⊤
⟦ v ∶ ` b ⟧ = ⊥
⟦ ν ∶ σ ⇒ τ ⟧ = ⊤
⟦ V ↦ w ∶ σ ⇒ τ ⟧ = ⟦ V ∶ σ ⟧₊ → ⟦ w ∶ τ ⟧
⟦ ERR ∶ σ ⇒ τ ⟧ = ⊤
⟦ blame ℓ ∶ σ ⇒ τ ⟧ = ⊤
⟦ v ∶ σ ⇒ τ ⟧ = ⊥
⟦ fst v ∶ σ `× τ ⟧ = ⟦ v ∶ σ ⟧
⟦ snd v ∶ σ `× τ ⟧ = ⟦ v ∶ τ ⟧
⟦ ERR ∶ σ `× τ ⟧ = ⊤
⟦ blame ℓ ∶ σ `× τ ⟧ = ⊤
⟦ v ∶ σ `× τ ⟧ = ⊥
⟦ inl V ∶ σ `⊎ τ ⟧ = ⟦ V ∶ σ ⟧₊
⟦ inr V ∶ σ `⊎ τ ⟧ = ⟦ V ∶ τ ⟧₊
⟦ ERR ∶ σ `⊎ τ ⟧ = ⊤
⟦ blame ℓ ∶ σ `⊎ τ ⟧ = ⊤
⟦ v ∶ σ `⊎ τ ⟧ = ⊥

⟦ERR∶τ⟧ : ∀ τ → ⟦ ERR ∶ τ ⟧
⟦ERR∶τ⟧ ⋆ = tt
⟦ERR∶τ⟧ (` x) = tt
⟦ERR∶τ⟧ (τ ⇒ τ₁) = tt
⟦ERR∶τ⟧ (τ `× τ₁) = tt
⟦ERR∶τ⟧ (τ `⊎ τ₁) = tt

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
⟦ ERR ∶ τ ⟧? = yes (⟦ERR∶τ⟧ τ)
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
⟦ ERR ∶ τ ⟧ = ⊤  {- want types for this? -}
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
⟦ ERR ∶ τ ⟧ = ⊤  {- want types for this? -}
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
  Error : `⟦ ERR ∶ ⋆ ⟧
  Fun : ∀ {V w σ τ} → `⟦ V ∶ σ ⟧₊ → `⟦ w ∶ τ ⟧ → `⟦ V ↦ w ∶ σ ⇒ τ ⟧
  Prod-fst : ∀ {v σ τ} → `⟦ v ∶ σ ⟧ → `⟦ fst v ∶ σ `× τ ⟧
  Prod-snd : ∀ {v σ τ} → `⟦ v ∶ τ ⟧ → `⟦ snd v ∶ σ `× τ ⟧
  Sum-inl : ∀ {V σ τ} → `⟦ V ∶ σ ⟧₊ → `⟦ inl V ∶ σ `⊎ τ ⟧
  Sum-inr : ∀ {V σ τ} → `⟦ V ∶ τ ⟧₊ → `⟦ inr V ∶ σ `⊎ τ ⟧

-}



  
  
{- Abstraction  ---------------------------------------------------------------}

data Λ : (𝒫 Val → 𝒫 Val) → 𝒫 Val where
  Λ-↦ : ∀{f V w}
     → w ∈ f (mem V)
     → V ≢ []  {- call by value -}
     → (V ↦ w) ∈ Λ f 
  Λ-ν : ∀{f} → ν ∈ Λ f

{- Application -----------------------------------------------------------------}

infix 6 _∗_
data _∗_ : 𝒫 Val → 𝒫 Val → 𝒫 Val where
   ∗-app : ∀ D₁ D₂ {V w}
      → (V ↦ w) ∈ D₁
      → mem V ⊆ D₂
      → w ∈ (D₁ ∗ D₂) 
   ∗-blame-rator : ∀ D₁ D₂ {ℓ}
      → blame ℓ ∈ D₁
      → blame ℓ ∈ (D₁ ∗ D₂) 
   ∗-blame-rand : ∀ D₁ D₂ {ℓ}
      → blame ℓ ∈ D₂
      → blame ℓ ∈ (D₁ ∗ D₂) 

{- Pairs -}

data pair : 𝒫 Val → 𝒫 Val → 𝒫 Val where
   pair-fst : ∀ D E {u v}
      → u ∈ D → v ∈ E
      → fst u ∈ pair D E
   pair-snd : ∀ D E {u v}
      → u ∈ D → v ∈ E
      → snd v ∈ pair D E
   pair-blame-fst : ∀ D E {ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ pair D E
   pair-blame-snd : ∀ D E {ℓ}
      → blame ℓ ∈ E
      → blame ℓ ∈ pair D E

data car : 𝒫 Val → 𝒫 Val where
   car-fst : ∀ D {u}
      → fst u ∈ D
      → u ∈ car D
   car-blame : ∀ D {ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ car D

data cdr : 𝒫 Val → 𝒫 Val where
   cdr-snd : ∀ D {u}
      → snd u ∈ D
      → u ∈ cdr D
   cdr-blame : ∀ D {ℓ}
      → blame ℓ ∈ D
      → blame ℓ ∈ cdr D

{- Sums -}

data inleft : 𝒫 Val → 𝒫 Val where
  inleft-inl : ∀{V D} → mem V ⊆ D → inl V ∈ inleft D
  inleft-blame : ∀{ℓ D} → blame ℓ ∈ D → blame ℓ ∈ inleft D

data inright : 𝒫 Val → 𝒫 Val where
  inright-inr : ∀{V D} → mem V ⊆ D → inr V ∈ inright D
  inright-blame : ∀{ℓ D} → blame ℓ ∈ D → blame ℓ ∈ inright D

data cond : 𝒫 Val → (𝒫 Val → 𝒫 Val) → (𝒫 Val → 𝒫 Val) → 𝒫 Val where
  cond-inl : ∀{D F₁ F₂ V w}
    → inl V ∈ D  → w ∈ F₁ (mem V) → w ∈ cond D F₁ F₂
  cond-inr : ∀{D F₁ F₂ V w}
    → inr V ∈ D  → w ∈ F₂ (mem V) → w ∈ cond D F₁ F₂
  cond-blame : ∀{D F₁ F₂ ℓ}
    → blame ℓ ∈ D  →  blame ℓ ∈ cond D F₁ F₂

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

data ℬ : (ℓ : Label) → 𝒫 Val where
  blame : ∀ ℓ → blame ℓ ∈ ℬ ℓ 



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