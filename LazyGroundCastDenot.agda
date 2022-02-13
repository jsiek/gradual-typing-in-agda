module LazyGroundCastDenot where

open import Data.Bool using (Bool; true; false)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Relation.Nullary using (Dec; yes; no)

open import LazyGroundCast
open import Variables
open import PrimitiveTypes using (Base; Label)
open import Types hiding (_⊑_)
open import Val Base rep-base

blame! : Label → Val
blame! ℓ = const {Blame} ℓ

𝒫 : Set → Set₁
𝒫 V = V → Set

_∈_ : ∀{V} → V → 𝒫 V → Set
x ∈ D = D x

↓ : Val → 𝒫 Val
↓ v w = w ⊑ v

_∷_ : ∀{Γ B} → 𝒫 Val → (∀{A} → Γ ∋ A → 𝒫 Val) → (∀{A} → Γ , B ∋ A → 𝒫 Val)
(D ∷ ρ) Z = D
(D ∷ ρ) (S x) = ρ x

{- Function Application -}

_•_ : 𝒫 Val → 𝒫 Val → 𝒫 Val
(D₁ • D₂) w = Σ[ v ∈ Val ] (v ↦ w) ∈ D₁ × v ∈ D₂

{- Function Abstraction -}

Λ : (𝒫 Val → 𝒫 Val) → 𝒫 Val
Λ f ⊥ = ⊤
Λ f (const k) = Bot
Λ f (v ↦ w) = f (↓ v) w
Λ f (u ⊔ v) = Λ f u × Λ f v

{- Primitives -}

℘ : ∀{A}{P : Prim A} → rep A → Val → Set
℘ {A}{P} k ⊥ = ⊤
℘ {A}{P-Base {B}} k (const {B′} k′)
    with base-eq? B B′
... | yes eq rewrite eq = k ≡ k′
... | no neq = Bot
℘ {A}{P-Fun {B} P} f (const {B′} k′) = Bot
℘ {A}{P} f (v ↦ w)
    with P
... | P-Base {B} = Bot
... | P-Fun {B} P′ = Σ[ k ∈ base-rep B ] (const {B} k ⊑ v × ℘ {P = P′} (f k) w)
℘ {A}{P} k (u ⊔ v) = ℘ {A}{P} k u × ℘ {A}{P} k v

pair : 𝒫 Val → 𝒫 Val → 𝒫 Val
pair D₁ D₂ w = (Σ[ u ∈ Val ] const 0 ↦ u ⊑ w  ×  u ∈ D₁)
                 × (Σ[ v ∈ Val ] const 1 ↦ v ⊑ w  ×  v ∈ D₂)
car : 𝒫 Val → 𝒫 Val
car D u = (const 0 ↦ u) ∈ D

cdr : 𝒫 Val → 𝒫 Val
cdr D u = (const 1 ↦ u) ∈ D

cond : 𝒫 Val → (𝒫 Val → 𝒫 Val) → (𝒫 Val → 𝒫 Val) → 𝒫 Val
cond D₀ F₁ F₂ w = (const true ∈ (car D₀) × w ∈ F₁ (cdr D₀))
   ⊎ (const false ∈ (car D₀) × w ∈ F₂ (cdr D₀))

⟦_⟧ : ∀{Γ A} → Γ ⊢ A → (∀{A} → Γ ∋ A → 𝒫 Val) → 𝒫 Val
⟦ ` x ⟧ ρ = ρ x
⟦ ƛ M ⟧ ρ = Λ λ D → ⟦ M ⟧ (D ∷ ρ)
⟦ L · M ⟧ ρ = ⟦ L ⟧ ρ  •  ⟦ M ⟧ ρ
⟦ $_ {Γ}{A} k {p} ⟧ ρ = ℘ {A}{p} k
⟦ if L M N ⟧ ρ w = (const true ∈ ⟦ L ⟧ ρ  ×  w ∈ ⟦ M ⟧ ρ)
                 ⊎ (const false ∈ ⟦ L ⟧ ρ  ×  w ∈ ⟦ N ⟧ ρ)
⟦ cons M N ⟧ ρ = pair (⟦ M ⟧ ρ) (⟦ N ⟧ ρ)
⟦ fst M ⟧ ρ = car (⟦ M ⟧ ρ)
⟦ snd M ⟧ ρ = cdr (⟦ M ⟧ ρ)
⟦ inl M ⟧ ρ = pair (℘ {P = P-Base} true) (⟦ M ⟧ ρ)
⟦ inr M ⟧ ρ = pair (℘ {P = P-Base} false) (⟦ M ⟧ ρ)
⟦ case L M N ⟧ ρ = cond (⟦ L ⟧ ρ) (λ D → ⟦ M ⟧ (D ∷ ρ)) λ D → ⟦ N ⟧ (D ∷ ρ)
⟦ M ⟨ c ⟩ ⟧ ρ = {!!}
⟦ M ⟪ c ⟫ ⟧ ρ = {!!}
⟦ blame ℓ ⟧ ρ = {!!}
