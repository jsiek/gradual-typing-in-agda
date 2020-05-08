module DenotGTLC where

open import GTLC

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

ℰ : ∀{Γ A} → (Γ ⊢G A) → Denotation
ℰ ($_ k {P}) γ v = ℘ {prim→primd P} (rep→prim-rep P k) v
ℰ (` x) γ v = v ⩽ (γ (∋→ℕ x))
ℰ (ƛ A ˙ N) = ℱ (ℰ N)
ℰ (L · M at ℓ) = (ℰ L) ● (ℰ M)
ℰ (if L M N ℓ {bb} {aa}) = {!!}
ℰ (cons M N) = {!!}
ℰ (fst M ℓ {m}) = {!!}
ℰ (snd M ℓ {m}) = {!!}
ℰ (inl B M) = {!!}
ℰ (inr A M) = {!!}
ℰ (case L M N ℓ {ma}{mb}{mc}{ab}{ac}{bc}) = {!!}
