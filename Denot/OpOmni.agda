{-# OPTIONS --allow-unsolved-metas #-}

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
open import Denot.Value
open import Denot.ConsisOmni


module Denot.OpOmni where

  {-
  We have the following operators:
  Λ , _∗_                   functions
  pair , car , cdr          pairs/products
  inleft , inright , cond   eithers/sums
  ℘ P f , If                primitives
  -}

  {- =========================================================================
  Denotational Operators
  ========================================================================= -}

  -------------------------------------------------------------------------
  -- Functions
    -- simply-typed lambda abstraction : Λ
    -- application : _∗_  , written `\ast'
  infix 6 _∗_

  data Λ : (A : Type) → (𝒫 Val → 𝒫 Val) → 𝒫 Val where
    Λ-↦ : ∀{A f V w}
        → (w∈ : w ∈ f (mem V))
        → (V∶A : ⟦ V ∶ A ⟧₊)  -- could omit; b/c checked at app
        → (scV : scD (mem V))
        → (nbV : ¬isBlame₊ V)  -- ditto
        → (neV : V ≢ [])  {- call by value -}
        → (V ↦ w) ∈ Λ A f
    Λ-ν : ∀{A f} → ν ∈ Λ A f

   -- an omniscient semantics could produce shallow blame for uncalled function bodies
   -- but I don't think we need that info to verify anything wrt Lazy vs Ground
    {-
    Λ-blame : ∀{A f V ℓ}
        → (w∈ : blame ℓ ∈ f (mem V))
        → (V∶A : ⟦ V ∶ A ⟧₊)
        → (nbV : ¬isBlame₊ V)
        → (neV : V ≢ [])  {- call by value -}
        → blame ℓ ∈ Λ A f
    -}
  {-
  why we want conditions on V:
  λ x∶Int.  ⟨Int ℓ⟩⟨⋆⟩x
  [true] -> blame ℓ
      blame ℓ
  -}

  data _∗_ : 𝒫 Val → 𝒫 Val → 𝒫 Val where
    ∗-app : ∀ {D₁ D₂ V w}
        → (V↦w∈ : (V ↦ w) ∈ D₁)
        → (V⊆ : mem V ⊆ D₂)
        → (nbV : ¬isBlame₊ V)   -- V only has good things
        → w ∈ (D₁ ∗ D₂)
    ∗-blame-rator : ∀ {D₁ D₂ ℓ}
        → (bl∈ : blame ℓ ∈ D₁)
        → blame ℓ ∈ (D₁ ∗ D₂) 
    ∗-blame-rand : ∀ {D₁ D₂ ℓ}
        → (bl∈ : blame ℓ ∈ D₂)
        → blame ℓ ∈ (D₁ ∗ D₂) 


  -------------------------------------------------------------------------
  -- Pairs
    -- pair
    -- car, cdr

  data pair : 𝒫 Val → 𝒫 Val → 𝒫 Val where
    pair-fst : ∀ {D E u v}
        → (u∈ : u ∈ D) → (v∈ : v ∈ E) 
        → (nbu : ¬ (isBlame u)) → (nbv : ¬ (isBlame v))
        → fst u ∈ pair D E
    pair-snd : ∀ {D E u v}
        → (u∈ : u ∈ D) → (v∈ : v ∈ E) 
        → (nbu : ¬ (isBlame u)) → (nbv : ¬ (isBlame v))
        → snd v ∈ pair D E
    pair-blame-fst : ∀ {D E ℓ}
        → (bl∈ : blame ℓ ∈ D)
        → blame ℓ ∈ pair D E
    pair-blame-snd : ∀ {D E ℓ}
        → (bl∈ : blame ℓ ∈ E)
        → blame ℓ ∈ pair D E

  data car : 𝒫 Val → 𝒫 Val where
    car-fst : ∀ {D u}
        → (fstu∈ : fst u ∈ D) → (nbu : ¬isBlame u)
        → u ∈ car D
    car-blame : ∀ {D ℓ}
        → (bl∈ : blame ℓ ∈ D)
        → blame ℓ ∈ car D

  data cdr : 𝒫 Val → 𝒫 Val where
    cdr-snd : ∀ {D v}
        → (sndv∈ : snd v ∈ D) → (nbv : ¬isBlame v)
        → v ∈ cdr D
    cdr-blame : ∀ {D ℓ}
        → (bl∈ : blame ℓ ∈ D)
        → blame ℓ ∈ cdr D

  -------------------------------------------------------------------------
  -- Sums
    -- inleft, inright
    -- case

  data inleft : 𝒫 Val → 𝒫 Val where
    inleft-inl : ∀{V D} → (V⊆ : mem V ⊆ D) → (nbV : ¬isBlame₊ V) → inl V ∈ inleft D
    inleft-blame : ∀{ℓ D} → (bl∈ : blame ℓ ∈ D) → blame ℓ ∈ inleft D

  data inright : 𝒫 Val → 𝒫 Val where
    inright-inr : ∀{V D} → (V⊆ : mem V ⊆ D) → (nbV : ¬isBlame₊ V) → inr V ∈ inright D
    inright-blame : ∀{ℓ D} → (bl∈ : blame ℓ ∈ D) → blame ℓ ∈ inright D

  data cond : 𝒫 Val → (𝒫 Val → 𝒫 Val) → (𝒫 Val → 𝒫 Val) → 𝒫 Val where
    cond-inl : ∀{D F₁ F₂ V w}
        → (LV∈ : inl V ∈ D) → (nbV : ¬isBlame₊ V) → (w∈ : w ∈ F₁ (mem V)) → w ∈ cond D F₁ F₂
    cond-inr : ∀{D F₁ F₂ V w}
        → (RV∈ : inr V ∈ D) → (nbV : ¬isBlame₊ V) → (w∈ : w ∈ F₂ (mem V)) → w ∈ cond D F₁ F₂
    cond-blame : ∀{D F₁ F₂ ℓ}
        → blame ℓ ∈ D → blame ℓ ∈ cond D F₁ F₂


  -------------------------------------------------------------------------
  -- Primitives (constants and functions)
    -- ℘ ,  written `\wp'
    -- If (boolean conditional), (uses _∗_ for function application)

  data If : 𝒫 Val → 𝒫 Val → 𝒫 Val → 𝒫 Val where
    If-then : ∀{D E₁ E₂ w}
        → (const true) ∈ D → w ∈ E₁ → w ∈ If D E₁ E₂
    If-else : ∀{D E₁ E₂ w}
        → (const false) ∈ D → w ∈ E₂ → w ∈ If D E₁ E₂
    If-blame : ∀{D E₁ E₂ ℓ}
        → blame ℓ ∈ D  →  blame ℓ ∈ If D E₁ E₂
  
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


  ℬ : Label → 𝒫 Val
  ℬ ℓ (blame ℓ') = ℓ' ≡ ℓ
  ℬ ℓ v = ⊥  



  {- =========================================================================
   Operator Monotonicity
  ========================================================================= -}

  Λ-mono : ∀ {A}{F F' : 𝒫 Val → 𝒫 Val} → 
    (∀ D D' → D ⊆ D' → F D ⊆ F' D') → Λ A F ⊆ Λ A F'
  Λ-mono F⊆ (V ↦ d) (Λ-↦ w∈ V∶A scV nbV neV) = 
    Λ-↦ (F⊆ (mem V) (mem V) (λ d z → z) d w∈) V∶A scV nbV neV 
  Λ-mono F⊆ ν Λ-ν = Λ-ν

  {-
  Λ-mono F⊆ (blame ℓ) (Λ-blame {V = V} w∈ V∶A nbV neV) = 
    Λ-blame (F⊆ (mem V) (mem V) (λ d z → z) (blame ℓ) w∈) V∶A nbV neV -}

  ∗-mono : ∀ {D E D' E'} → D ⊆ D' → E ⊆ E' → (D ∗ E) ⊆ (D' ∗ E')
  ∗-mono {D}{E}{D'}{E'} D⊆ E⊆ d (∗-app {V = V} V↦w∈ V⊆ nbV) = 
    ∗-app (D⊆ (V ↦ d) V↦w∈) (λ d z → E⊆ d (V⊆ d z)) nbV
  ∗-mono {D}{E}{D'}{E'} D⊆ E⊆ (blame ℓ) (∗-blame-rator x) = 
    ∗-blame-rator (D⊆ (blame ℓ) x)
  ∗-mono {D}{E}{D'}{E'} D⊆ E⊆ (blame ℓ) (∗-blame-rand x) = 
    ∗-blame-rand (E⊆ (blame ℓ) x)

  pair-mono : ∀ {D E D' E'} → D ⊆ D' → E ⊆ E' → (pair D E) ⊆ (pair D' E')
  pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (fst u) (pair-fst {v = v} x x₁ x₂ x₃) = 
    pair-fst (D⊆ u x) (E⊆ v x₁) x₂ x₃
  pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (snd v) (pair-snd {u = u} x x₁ x₂ x₃) = 
    pair-snd (D⊆ u x) (E⊆ v x₁) x₂ x₃
  pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (blame ℓ) (pair-blame-fst x) = 
    pair-blame-fst (D⊆ (blame ℓ) x)
  pair-mono {D} {E} {D'} {E'} D⊆ E⊆ (blame ℓ) (pair-blame-snd x) = 
    pair-blame-snd (E⊆ (blame ℓ) x)

  car-mono : ∀ {D D'} → D ⊆ D' → car D ⊆ car D'
  car-mono {D} {D'} D⊆ d (car-fst x nbu) = car-fst (D⊆ (fst d) x) nbu
  car-mono {D} {D'} D⊆ (blame ℓ) (car-blame x) = car-blame (D⊆ (blame ℓ) x)

  cdr-mono : ∀ {D D'} → D ⊆ D' → cdr D ⊆ cdr D'
  cdr-mono {D} {D'} D⊆ d (cdr-snd x nbv) = cdr-snd (D⊆ (snd d) x) nbv
  cdr-mono {D} {D'} D⊆ (blame ℓ) (cdr-blame x) = cdr-blame (D⊆ (blame ℓ) x)

  inleft-mono : ∀ {D D'} → D ⊆ D' → inleft D ⊆ inleft D'
  inleft-mono {D} {D'} D⊆ (inl x) (inleft-inl V⊆ nbV) = inleft-inl (λ d z → D⊆ d (V⊆ d z)) nbV
  inleft-mono {D} {D'} D⊆ (blame x) (inleft-blame x₁) = inleft-blame (D⊆ (blame x) x₁)

  inright-mono : ∀ {D D'} → D ⊆ D' → inright D ⊆ inright D'
  inright-mono {D} {D'} D⊆ (inr x) (inright-inr V⊆ nbV) = inright-inr (λ d z → D⊆ d (V⊆ d z)) nbV
  inright-mono {D} {D'} D⊆ (blame x) (inright-blame x₁) = inright-blame (D⊆ (blame x) x₁)

  cond-mono :  ∀ {T D E T' D' E'} → T ⊆ T' 
          → (∀ a a' → a ⊆ a' → D a ⊆ D' a') → (∀ b b' → b ⊆ b' → E b ⊆ E' b') 
          → cond T D E ⊆ cond T' D' E'
  cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (cond-inl {V = V} x nbV x₁) = 
    cond-inl (T⊆ (inl V) x) nbV (D⊆ (mem V) (mem V) (λ d z → z) d x₁)
  cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (cond-inr {V = V} x nbV x₁) = 
    cond-inr (T⊆ (inr V) x) nbV (E⊆ (mem V) (mem V) (λ d z → z) d x₁)
  cond-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ (blame ℓ) (cond-blame x) = 
    cond-blame (T⊆ (blame ℓ) x)

  If-mono : ∀ {T D E T' D' E'} → T ⊆ T' → D ⊆ D' → E ⊆ E' → If T D E ⊆ If T' D' E'
  If-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (If-then x x₁) = 
    If-then (T⊆ (const true) x) (D⊆ d x₁)
  If-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ d (If-else x x₁) = 
    If-else (T⊆ (const false) x) (E⊆ d x₁)
  If-mono {T} {D} {E} {T'} {D'} {E'} T⊆ D⊆ E⊆ (blame ℓ) (If-blame x) = 
    If-blame (T⊆ (blame ℓ) x)


-- TODO
  {- =========================================================================
  Equational reasoning on operators; (w/o casts)
  ========================================================================= -}
  open SetsAsPredicates.≃-Reasoning


{-
{- --- eta rules --------------------------------- -}
  
infix 5 _≃𝑓_

_≃𝑓_ : ∀ (F F' : 𝒫 Val → 𝒫 Val) → Set₁
F ≃𝑓 F' = ∀ D → F D ≃ F' D  

-- syntactic Λ-η is  ƛ C ˙ ((rename ⇑ M) · (` 0)) ≃ M
-- or, simply,  λ x . (F x) = F
-- only true for blameless values
-- needs D closed-down for ↦ case
-- needs D is Fun for ν case
Λ-η-⊆ : ∀ {A} D → Λ A (λ X → D ∗ X) ⊆ D
Λ-η-⊆ D d d∈ = {!   !}

-- going to need D is functional
Λ-η-⊇ : ∀ {A} D → D ⊆ Λ A (λ X → D ∗ X)
Λ-η-⊇ D (blame ℓ) d∈ = {!  !}
Λ-η-⊇ D ν d∈ = {!   !}
Λ-η-⊇ D (V ↦ w) d∈ = {!   !}
Λ-η-⊇ D (const k) d∈ = {!   !}
Λ-η-⊇ D d d∈ = {!   !}

Λ-η : ∀ {A} D → Λ A (λ X → D ∗ X) ≃ D
Λ-η D = ({!   !} , {!   !})

pair-η-⊆ : ∀ {D} → pair (car D) (cdr D) ⊆ D
pair-η-⊆ .(fst _) (pair-fst (car-fst fstu∈ nbu₁) v∈ nbu nbv) = fstu∈
pair-η-⊆ .(fst (blame _)) (pair-fst (car-blame bl∈) v∈ nbu nbv) = ⊥-elim (nbu tt)
pair-η-⊆ .(snd _) (pair-snd u∈ (cdr-snd sndv∈ nbv₁) nbu nbv) = sndv∈
pair-η-⊆ .(snd (blame _)) (pair-snd u∈ (cdr-blame bl∈) nbu nbv) = ⊥-elim (nbv tt)
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
     pair-fst (car-fst d∈ nbu) (cdr-snd sndv∈ nbv) nbu nbv
   ... | snd v | d∶A×B | d∈ = 
     let nbv = cbvD (snd v) d∈ in
     let (u , fstu∈) = proj₂ pcD (v , d∈) in
     let nbu = cbvD (fst u) fstu∈ in
    pair-snd (car-fst fstu∈ nbu) (cdr-snd d∈ nbv) nbu nbv


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

-- requires F monotonic
-- requires some other property; unclear
Λ-β-⊆ : ∀ {A} {F : 𝒫 Val → 𝒫 Val} {D} → ((Λ A F) ∗ D) ⊆ (F D)
Λ-β-⊆ d (∗-app (Λ-↦ w∈ V∶A nbV₁ neV) V⊆ nbV) = {! w∈   !}
Λ-β-⊆ .(blame _) (∗-blame-rator (Λ-blame w∈ V∶A nbV neV)) = {! w∈  !}
Λ-β-⊆ .(blame _) (∗-blame-rand bl∈) = {!    !}

Λ-β-⊇ : ∀ {A} {F : 𝒫 Val → 𝒫 Val} {D} → (F D) ⊆ ((Λ A F) ∗ D)
Λ-β-⊇ d d∈ = {!   !}

Λ-β : ∀ {A} {F : 𝒫 Val → 𝒫 Val} {D} → ((Λ A F) ∗ D) ≃ (F D)
Λ-β = {!   !}

car-step : {!   !}
car-step = {!   !}

cdr-step : {!   !}
cdr-step = {!   !}



{- --- apply-cast rules -------------------------- -}




-}