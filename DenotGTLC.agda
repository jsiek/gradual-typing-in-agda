module DenotGTLC where

open import GTLC
open import Data.Bool using (true; false)
open import Data.Empty renaming (⊥ to False)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)

open import ValueConst renaming (_⊑_ to _⩽_) hiding (_~_) public
open import ValueStructAux value_struct public
open import OrderingAux value_struct ordering public
open import Consistency public
open import ConsistentAux value_struct ordering consistent public
open import CurryConst public
open import PrimConst public
open import ModelCurryConst public
open import ModelCallByValue
   value_struct ordering consistent ℱ model_curry public
open import CurryApplyAux
   value_struct ordering consistent _●_ ℱ model_curry_apply public
open import DenotProdSum

promote : Value → Denotation
promote w γ v = (v ⩽ w)

𝐹 : (Denotation → Denotation) → Denotation
𝐹 f γ ⊥ = ⊤
𝐹 f γ (const k) = False
𝐹 f γ (v ↦ w) = (f (promote v)) γ w
𝐹 f γ (v₁ ⊔ v₂) = 𝐹 f γ v₁ × 𝐹 f γ v₂


{------------------------------------------------------------------------------
  Denotation of Types
 -----------------------------------------------------------------------------}

𝓑 : Base → Value → Set
𝓑 Nat ⊥ = ⊤
𝓑 Nat (const {Nat} x) = ⊤
𝓑 Nat (v₁ ⊔ v₂) = 𝓑 Nat v₁ × 𝓑 Nat v₂
𝓑 Int ⊥ = ⊤
𝓑 Int (const {Int} x) = ⊤
𝓑 Int (v₁ ⊔ v₂) = 𝓑 Int v₁ × 𝓑 Int v₂
𝓑 𝔹 ⊥ = ⊤
𝓑 𝔹 (const {𝔹} x) = ⊤
𝓑 𝔹 (v₁ ⊔ v₂) = 𝓑 𝔹 v₁ × 𝓑 𝔹 v₂
𝓑 Unit ⊥ = ⊤
𝓑 Unit (const {Unit} x) = ⊤
𝓑 Unit (v₁ ⊔ v₂) = 𝓑 Unit v₁ × 𝓑 Unit v₂
𝓑 ι (const {Blame} ℓ) = ⊤
𝓑 ι v = False

ret : (Value → Set) → Denotation
ret f γ v = f v

𝒯 : Type → Value → Set
𝒯 ⋆ v = ⊤
𝒯 (` ι) v = 𝓑 ι v
𝒯 (A ⇒ B) ⊥ = ⊤
𝒯 (A ⇒ B) (const {Blame} ℓ) = ⊤
𝒯 (A ⇒ B) (const x) = False
𝒯 (A ⇒ B) (v ↦ w) = 𝒯 A v → 𝒯 B w
𝒯 (A ⇒ B) (v₁ ⊔ v₂) = 𝒯 (A ⇒ B) v₁ × 𝒯 (A ⇒ B) v₂
𝒯 (A `× B) (const {Blame} ℓ) = ⊤
𝒯 (A `× B) v = ⟬ ret (𝒯 A) , ret (𝒯 B) ⟭ `∅ v
𝒯 (A `⊎ B) (const {Blame} ℓ) = ⊤
𝒯 (A `⊎ B) v = inj1 (ret (𝒯 A)) `∅ v ⊎ inj2 (ret (𝒯 A)) `∅ v

{-
 A monad for propagating blame
-}

_>>=_ : Denotation → (Denotation → Denotation) → Denotation
(D >>= f) γ v = (f D) γ v
              ⊎ Σ[ ℓ ∈ ℕ ] ((D γ (const (label ℓ)) × const (label ℓ) ⩽ v))

module Denot (𝒞 : Type → Type → Label → Denotation → Denotation) where

  ℰ : ∀{Γ A} → (Γ ⊢G A) → Denotation
  ℰ ($_ k {P}) γ v = ℘ {prim→primd P} (rep→prim-rep P k) v
  ℰ (` x) γ v = v ⩽ (γ (∋→ℕ x))
  ℰ (ƛ A ˙ N) = ℱ (ℰ N)
  ℰ (_·_at_ {A = A}{A₁}{A₂}{B} L M ℓ {m} {cn}) = do
      D₁ ← 𝒞 A (A₁ ⇒ A₂) ℓ (ℰ L)
      D₂ ← 𝒞 B A₁ ℓ (ℰ M)
      D₁ ● D₂
  ℰ (if {A = A}{A'}{B} L M N ℓ {bb} {aa}) = do
      D ← 𝒞 B (` 𝔹) ℓ (ℰ L)
      λ γ v → (D γ (const true) × 𝒞 A (⨆ aa) ℓ (ℰ M) γ v)
            ⊎ (D γ (const false) × 𝒞 A' (⨆ aa) ℓ (ℰ N) γ v)
  ℰ (cons M N) = do
      D₁ ← ℰ M
      D₂ ← ℰ N
      ⟬ D₁ , D₂ ⟭
  ℰ (fst {A = A}{A₁}{A₂} M ℓ {m}) = do
      D ← 𝒞 A (A₁ `× A₂) ℓ (ℰ M)
      π₁ D
  ℰ (snd {A = A}{A₁}{A₂} M ℓ {m}) = do
      D ← 𝒞 A (A₁ `× A₂) ℓ (ℰ M)
      π₂ D
  ℰ (inl B M) = do
      D ← ℰ M
      inj1 D
  ℰ (inr A M) = do
      D ← ℰ M
      inj2 D
  ℰ (case {A = A}{A₁}{A₂}{B}{B₁}{B₂}{C}{C₁}{C₂}
           L M N ℓ {ma}{mb}{mc}{ab}{ac}{bc}) =
     case⊎ (𝒞 A (B₁ `⊎ C₁) ℓ (ℰ L))
           (𝒞 B (B₁ ⇒ (⨆ bc)) ℓ (ℰ M))
           (𝒞 C (C₁ ⇒ (⨆ bc)) ℓ (ℰ N))

{------------------------------------------------------------------------------
  Denotational Semantics of GTLC
 -----------------------------------------------------------------------------}

{- Or should casts be expressed using function values and applied using ●?
   𝐶 : Type → Type → Label → Denotation
  -Jeremy -}

{-
to-fun : Label → Denotation → Denotation
to-fun ℓ D = {!!}

𝐶 : Type → Type → Label → Denotation → Denotation
𝐶 ⋆ ⋆ ℓ D = D
𝐶 ⋆ (` ι) ℓ D γ v = D γ v × 𝓑 ι v
𝐶 ⋆ (A ⇒ B) ℓ D = do
  D′ ← to-fun ℓ D
  𝐹 (λ x → 𝐶 ⋆ B ℓ (D′ ● (𝐶 A ⋆ ℓ x)))
  
𝐶 ⋆ (A `× B) ℓ D = {!!}
𝐶 ⋆ (A `⊎ B) ℓ D = {!!}
𝐶 (` ι) B ℓ D = {!!}
𝐶 (A ⇒ A₁) B ℓ D = {!!}
𝐶 (A `× A₁) B ℓ D = {!!}
𝐶 (A `⊎ A₁) B ℓ D = {!!}
-}

{------------------------------------------------------------------------------
  Denotational Semantics of GTLC
 -----------------------------------------------------------------------------}

mkfun : (Env → Value → Value → Set) → Denotation
mkfun f γ ⊥ = ⊤
mkfun f γ (const k) = False
mkfun f γ (v ↦ w) = f γ v w
mkfun f γ (v₁ ⊔ v₂) = mkfun f γ v₁ × mkfun f γ v₂

id : Denotation
id = mkfun (λ γ v w → w ⩽ v)

{-
  This is D style projection.
-}

_??_ : Type → ℕ → Denotation
A ?? ℓ = mkfun (λ γ v w → (𝒯 A v × w ⩽ v) ⊎ ((¬ 𝒯 A v) × const (label ℓ) ⩽ w))

!! : Type → Denotation
!! A = id

_⨟_ : Denotation → Denotation → Denotation
D₁ ⨟ D₂ = 𝐹 (λ D → D₂ ● (D₁ ● D))

_↪_ : Denotation → Denotation → Denotation
D₁ ↪ D₂ = mkfun G
    where G : Env → Value → Value → Set
          G γ ⊥ w = w ⩽ ⊥
          G γ (const k) w = False
          G γ (v₁ ↦ v₂) w = D₁ γ v₁ × D₂ γ v₂ × w ⩽ (v₁ ↦ v₂)
          G γ (v₁ ⊔ v₂) w = G γ v₁ w × G γ v₂ w

_⊗_ : Denotation → Denotation → Denotation
D₁ ⊗ D₂ = 𝐹 (λ D → ⟬ D₁ ● π₁ D , D₂ ● π₂ D ⟭)

_⊕_ : Denotation → Denotation → Denotation
D₁ ⊕ D₂ = mkfun G
    where G : Env → Value → Value → Set
          G γ ⊥ w = w ⩽ ⊥
          G γ (const x) w = False
          G γ (v₁ ↦ v₂) w = {!(const 0 ⩽ v₁ × !}
          G γ (v₁ ⊔ v₂) w = G γ v₁ w × G γ v₂ w 

blame : ℕ → Denotation
blame ℓ γ v = const (label ℓ) ⩽ v

𝐶 : ∀{A B} → (c : A ~ B) → ℕ → Denotation
𝐶 {.⋆} {B} unk~L ℓ = B ?? ℓ
𝐶 {A} {.⋆} unk~R ℓ = !! A
𝐶 {` ι} {.(` ι)} base~ ℓ = id
𝐶 {.(_ ⇒ _)} {.(_ ⇒ _)} (fun~ c d) ℓ = 𝐶 c ℓ ↪ 𝐶 d ℓ
𝐶 {.(_ `× _)} {.(_ `× _)} (pair~ c d) ℓ = 𝐶 c ℓ ⊗ 𝐶 d ℓ
𝐶 {.(_ `⊎ _)} {.(_ `⊎ _)} (sum~ c d) ℓ = 𝐶 c ℓ ⊕ 𝐶 d ℓ


{------------------------------------------------------------------------------
  Omniscient Denotational Semantics of GTLC
 -----------------------------------------------------------------------------}

𝒞 : Type → Type → Label → Denotation → Denotation
𝒞 A B ℓ D γ v = (D γ v × 𝒯 B v)
              ⊎ ((Σ[ w ∈ Value ] (wf w × D γ w × ¬ (𝒯 B w)))
                 × const (label (label→ℕ ℓ)) ⩽ v)

open Denot 𝒞 renaming (ℰ to 𝒪) 



{-
 TODO:
 * proof of type soundness a la Milner
 -}
