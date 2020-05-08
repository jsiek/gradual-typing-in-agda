module DenotGTLC where

open import GTLC
open import Data.Unit using (⊤)
open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import ValueConst renaming (_⊑_ to _⩽_) public
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

⟬_,_⟭ : Denotation → Denotation → Denotation
⟬_,_⟭ D₁ D₂ γ ⊥ = ⊤
⟬_,_⟭ D₁ D₂ γ (const k) = False
⟬_,_⟭ D₁ D₂ γ (v ↦ w) = const 0 ⩽ v × D₁ γ w
                      ⊎ const 1 ⩽ v × D₂ γ w
⟬_,_⟭ D₁ D₂ γ (v₁ ⊔ v₂) = ⟬ D₁ , D₂ ⟭ γ v₁ × ⟬ D₁ , D₂ ⟭ γ v₂

π₁ : Denotation → Denotation
π₁ D = D ● (λ γ v → ℘ {base Nat} 0 v)

π₂ : Denotation → Denotation
π₂ D = D ● (λ γ v → ℘ {base Nat} 1 v)

inj1 : Denotation → Denotation
inj1 D γ ⊥ = ⊤
inj1 D γ (const x) = False
inj1 D γ (v ↦ w) = const 0 ⩽ v × const 0 ⩽ w
                 ⊎ const 1 ⩽ v × D γ w
inj1 D γ (v₁ ⊔ v₂) = inj1 D γ v₁ × inj1 D γ v₂

inj2 : Denotation → Denotation
inj2 D γ ⊥ = ⊤
inj2 D γ (const x) = False
inj2 D γ (v ↦ w) = const 0 ⩽ v × const 1 ⩽ w
                 ⊎ const 1 ⩽ v × D γ w
inj2 D γ (v₁ ⊔ v₂) = inj2 D γ v₁ × inj2 D γ v₂

case⊎ : Denotation → Denotation → Denotation → Denotation
case⊎ D⊎ D₁ D₂ γ v =
    ((D⊎ ● (λ γ v → ℘ {base Nat} 0 v)) γ (const 0)
    ×
    (Σ[ v₁ ∈ Value ] (D⊎ ● (λ γ v → ℘ {base Nat} 1 v)) γ v₁  × D₁ (γ `, v₁) v))
    ⊎ 
    ((D⊎ ● (λ γ v → ℘ {base Nat} 0 v)) γ (const 1)
    ×
    (Σ[ v₂ ∈ Value ] (D⊎ ● (λ γ v → ℘ {base Nat} 1 v)) γ v₂  × D₂ (γ `, v₂) v))

ℰ : ∀{Γ A} → (Γ ⊢G A) → Denotation
ℰ ($_ k {P}) γ v = ℘ {prim→primd P} (rep→prim-rep P k) v
ℰ (` x) γ v = v ⩽ (γ (∋→ℕ x))
ℰ (ƛ A ˙ N) = ℱ (ℰ N)
ℰ ((L · M at ℓ) {m} {cn}) = (ℰ L) ● (ℰ M)
ℰ (if L M N ℓ {bb} {aa}) = {!!}
ℰ (cons M N) = ⟬ ℰ M , ℰ N ⟭
ℰ (fst M ℓ {m}) = π₁ (ℰ M)
ℰ (snd M ℓ {m}) = π₂ (ℰ M)
ℰ (inl B M) = inj1 (ℰ M)
ℰ (inr A M) = inj2 (ℰ M)
ℰ (case L M N ℓ {ma}{mb}{mc}{ab}{ac}{bc}) = case⊎ (ℰ L) (ℰ M) (ℰ N)
