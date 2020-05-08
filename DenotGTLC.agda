module DenotGTLC where

open import GTLC
open import Data.Bool using (true; false)
open import Data.Empty renaming (⊥ to False)
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

{------------------------------------------------------------------------------
  Omniscient Denotational Semantics of GTLC
 -----------------------------------------------------------------------------}

{-
  Denotation of Types
-}

𝓑 : Base → Value → Set
𝓑 Nat ⊥ = ⊤
𝓑 Nat (const {Nat} x) = ⊤
𝓑 Nat (v₁ ⊔ v₂) = 𝓑 Nat v₁ × 𝓑 Nat v₂
𝓑 Int ⊥ = ⊤
𝓑 Int (const {Int} x) = ⊤
𝓑 Int (v₁ ⊔ v₂) = 𝓑 Int v₁ × 𝓑 Int v₂
𝓑 𝔹 (const {𝔹} x) = ⊤
𝓑 𝔹 (v₁ ⊔ v₂) = 𝓑 𝔹 v₁ × 𝓑 𝔹 v₂
𝓑 Unit (const {Unit} x) = ⊤
𝓑 Unit (v₁ ⊔ v₂) = 𝓑 Unit v₁ × 𝓑 Unit v₂
𝓑 b v = False

ret : (Value → Set) → Denotation
ret f γ v = f v

𝒯 : Type → Value → Set
𝒯 ⋆ v = ⊤
𝒯 (` b) v = 𝓑 b v
𝒯 (A ⇒ B) ⊥ = ⊤
𝒯 (A ⇒ B) (const x) = False
𝒯 (A ⇒ B) (v ↦ w) = 𝒯 A v → 𝒯 B w
𝒯 (A ⇒ B) (v₁ ⊔ v₂) = 𝒯 (A ⇒ B) v₁ × 𝒯 (A ⇒ B) v₂
𝒯 (A `× B) = ⟬ ret (𝒯 A) , ret (𝒯 B) ⟭ `∅
𝒯 (A `⊎ B) v = inj1 (ret (𝒯 A)) `∅ v ⊎ inj2 (ret (𝒯 A)) `∅ v

𝒞 : Type → Label → Denotation → Denotation
𝒞 B ℓ D γ v = (D γ v × 𝒯 B v)
              ⊎ ((Σ[ w ∈ Value ] (wf w × D γ w × ¬ (𝒯 B w)))
                 × const (label (label→ℕ ℓ)) ⩽ v)

ℰ : ∀{Γ A} → (Γ ⊢G A) → Denotation
ℰ ($_ k {P}) γ v = ℘ {prim→primd P} (rep→prim-rep P k) v
ℰ (` x) γ v = v ⩽ (γ (∋→ℕ x))
ℰ (ƛ A ˙ N) = ℱ (ℰ N)
ℰ (_·_at_ {A = A}{A₁}{A₂}{B} L M ℓ {m} {cn}) =
  (𝒞 (A₁ ⇒ A₂) ℓ (ℰ L)) ● (𝒞 B ℓ (ℰ M))
ℰ (if L M N ℓ {bb} {aa}) γ v =
    (ℰ L γ (const true) × ℰ M γ v)
    ⊎ (ℰ L γ (const false) × ℰ L γ v)
ℰ (cons M N) = ⟬ ℰ M , ℰ N ⟭
ℰ (fst {A₁ = A₁}{A₂} M ℓ {m}) = π₁ (𝒞 (A₁ `× A₂) ℓ (ℰ M)) 
ℰ (snd M ℓ {m}) = π₂ (ℰ M)
ℰ (inl B M) = inj1 (ℰ M)
ℰ (inr A M) = inj2 (ℰ M)
ℰ (case L M N ℓ {ma}{mb}{mc}{ab}{ac}{bc}) = case⊎ (ℰ L) (ℰ M) (ℰ N)

{-
 TODO:
 * proof of type soundness a la Milner
 -}
