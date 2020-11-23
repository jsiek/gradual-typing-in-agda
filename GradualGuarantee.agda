open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂; inspect; [_])
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

-- We're using simple cast with inert cross cast - at least for now.
open import GroundInertX using (Cast; cast; Inert; Active; Cross; applyCast;
                                pcs; cs; dom; cod; fstC; sndC; inlC; inrC; compile; inert-ground)
open import Types
open import Variables
open import Labels

open import GTLC
import ParamCastCalculus
open ParamCastCalculus Cast Inert
import ParamCastAux
open ParamCastAux pcs
import ParamCastReduction
open ParamCastReduction cs
-------------------------
open import TermPrecision
open import GradualGuaranteeAux
open import GradualGuaranteeSim


{-
  Here is the statement of the gradual guarantee:
-}
gradual-guarantee : ∀ {A A′} {M₁ : ∅ ⊢ A} {M₁′ M₂′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ M₁ ⊑ᶜ M₁′     -- Note M₁′ is more precise here.
  → M₁′ —→ M₂′
    ---------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))

{-
  For constructors, just recur on the subterms if the reduction on the rhs is ξ.
  Otherwise if it is a ξ-blame, we're done and don't need to go anywhere.
-}
gradual-guarantee-cons : ∀ {A A′ B B′} {M : ∅ ⊢ A} {N : ∅ ⊢ B} {M′ : ∅ ⊢ A′} {N′ : ∅ ⊢ B′} {M₁ : ∅ ⊢ A `× B} {M₁′ M₂′ : ∅ ⊢ A′ `× B′}
  → ∅ , ∅ ⊢ M ⊑ᶜ M′ → ∅ , ∅ ⊢ N ⊑ᶜ N′
  → M₁ ≡ cons M N → M₁′ ≡ cons M′ N′
  → M₁′ —→ M₂′
    -----------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
gradual-guarantee-cons {M = M} {N} lpM lpN refl eq2 (ξ {F = F-×₁ _} rd)
  with plug-inv-cons₁ eq2
... | ⟨ refl , refl ⟩
  with gradual-guarantee lpN rd
...   | ⟨ N₁ , ⟨ rd* , lpN₁ ⟩ ⟩ = ⟨ cons M N₁ , ⟨ plug-cong (F-×₁ M) rd* , ⊑ᶜ-cons lpM lpN₁ ⟩ ⟩
gradual-guarantee-cons {M = M} {N} lpM lpN refl eq2 (ξ {F = F-×₂ _} rd)
  with plug-inv-cons₂ eq2
... | ⟨ refl , refl ⟩
  with gradual-guarantee lpM rd
...   | ⟨ M₁ , ⟨ rd* , lpM₁ ⟩ ⟩ = ⟨ cons M₁ N , ⟨ plug-cong (F-×₂ N) rd* , ⊑ᶜ-cons lpM₁ lpN ⟩ ⟩
gradual-guarantee-cons {M = M} {N} lpM lpN refl eq2 (ξ-blame {F = F-×₁ _})
  with plug-inv-cons₁ eq2
... | ⟨ refl , refl ⟩ = ⟨ cons M N , ⟨ cons M N ∎ , ⊑ᶜ-blame (pair⊑ (⊑ᶜ→⊑ ⊑*-∅ lpM) (⊑ᶜ→⊑ ⊑*-∅ lpN)) ⟩ ⟩
gradual-guarantee-cons {M = M} {N} lpM lpN refl eq2 (ξ-blame {F = F-×₂ _})
  with plug-inv-cons₂ eq2
... | ⟨ refl , refl ⟩ = ⟨ cons M N , ⟨ cons M N ∎ , ⊑ᶜ-blame (pair⊑ (⊑ᶜ→⊑ ⊑*-∅ lpM) (⊑ᶜ→⊑ ⊑*-∅ lpN)) ⟩ ⟩

gradual-guarantee-inl : ∀ {A A′ B B′} {M : ∅ ⊢ A} {M′ : ∅ ⊢ A′} {M₁ : ∅ ⊢ A `⊎ B} {M₁′ M₂′ : ∅ ⊢ A′ `⊎ B′}
  → B ⊑ B′ → ∅ , ∅ ⊢ M ⊑ᶜ M′
  → M₁ ≡ inl {B = B} M → M₁′ ≡ inl {B = B′} M′
  → M₁′ —→ M₂′
    ---------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
gradual-guarantee-inl lp lpM refl eq2 (ξ {F = F-inl} rd)
  with plug-inv-inl eq2
... | refl
  with gradual-guarantee lpM rd
...   | ⟨ M₁ , ⟨ rd* , lpM₁ ⟩ ⟩ = ⟨ inl M₁ , ⟨ plug-cong F-inl rd* , ⊑ᶜ-inl lp lpM₁ ⟩ ⟩
gradual-guarantee-inl {M = M} lp lpM refl eq2 (ξ-blame {F = F-inl})
  with plug-inv-inl eq2
... | refl = ⟨ inl M , ⟨ inl M ∎ , ⊑ᶜ-blame (sum⊑ (⊑ᶜ→⊑ ⊑*-∅ lpM) lp) ⟩ ⟩

gradual-guarantee-inr : ∀ {A A′ B B′} {M : ∅ ⊢ B} {M′ : ∅ ⊢ B′} {M₁ : ∅ ⊢ A `⊎ B} {M₁′ M₂′ : ∅ ⊢ A′ `⊎ B′}
  → A ⊑ A′ → ∅ , ∅ ⊢ M ⊑ᶜ M′
  → M₁ ≡ inr {A = A} M → M₁′ ≡ inr {A = A′} M′
  → M₁′ —→ M₂′
    ---------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
gradual-guarantee-inr lp lpM refl eq2 (ξ {F = F-inr} rd)
  with plug-inv-inr eq2
... | refl
  with gradual-guarantee lpM rd
...   | ⟨ M₁ , ⟨ rd* , lpM₁ ⟩ ⟩ = ⟨ inr M₁ , ⟨ plug-cong F-inr rd* , ⊑ᶜ-inr lp lpM₁ ⟩ ⟩
gradual-guarantee-inr {M = M} lp lpM refl eq2 (ξ-blame {F = F-inr})
  with plug-inv-inr eq2
... | refl = ⟨ inr M , ⟨ inr M ∎ , ⊑ᶜ-blame (sum⊑ lp (⊑ᶜ→⊑ ⊑*-∅ lpM)) ⟩ ⟩

{-
  The term constructor `fst` is an eliminator for pairs. By casing on the reduction of the rhs,
  the β and cast cases are the interesting ones - we prove them in separate lemmas.
-}
gradual-guarantee-fst : ∀ {A A′ B B′} {N₁ : ∅ ⊢ A `× B} {N₁′ : ∅ ⊢ A′ `× B′} {M₁ : ∅ ⊢ A} {M₁′ M₂′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ N₁ ⊑ᶜ N₁′
  → M₁ ≡ fst N₁ → M₁′ ≡ fst N₁′
  → M₁′ —→ M₂′
    -----------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
gradual-guarantee-fst {N₁ = N₁} {N₁′} {M₁} {M₁′} {M₂′} N₁⊑N₁′ refl eq2 (ξ {M′ = N₂′} {F} N₁′→N₂′)
  with plug-inv-fst F eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩
  with gradual-guarantee N₁⊑N₁′ N₁′→N₂′
...   | ⟨ N₂ , ⟨ N₁↠N₂ , N₂⊑N₂′ ⟩ ⟩ = ⟨ fst N₂ , ⟨ plug-cong F-fst N₁↠N₂ , ⊑ᶜ-fst N₂⊑N₂′ ⟩ ⟩
gradual-guarantee-fst {N₁ = N₁} lpf refl eq2 (ξ-blame {F = F})
  with plug-inv-fst F eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩ with ⊑ᶜ→⊑ ⊑*-∅ lpf
...   | pair⊑ lpA lpB = ⟨ fst N₁ , ⟨ fst N₁ ∎ , ⊑ᶜ-blame lpA ⟩ ⟩
gradual-guarantee-fst lpf refl refl (β-fst vV′ vW′) = sim-fst-cons vV′ vW′ lpf
gradual-guarantee-fst lpf refl refl (fst-cast v′ {x′} {i′}) = sim-fst-wrap v′ i′ x′ lpf

gradual-guarantee-snd : ∀ {A A′ B B′} {N₁ : ∅ ⊢ A `× B} {N₁′ : ∅ ⊢ A′ `× B′} {M₁ : ∅ ⊢ B} {M₁′ M₂′ : ∅ ⊢ B′}
  → ∅ , ∅ ⊢ N₁ ⊑ᶜ N₁′
  → M₁ ≡ snd N₁ → M₁′ ≡ snd N₁′
  → M₁′ —→ M₂′
    -----------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
gradual-guarantee-snd {N₁ = N₁} {N₁′} {M₁} {M₁′} {M₂′} N₁⊑N₁′ refl eq2 (ξ {M′ = N₂′} {F} N₁′→N₂′)
  with plug-inv-snd F eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩
  with gradual-guarantee N₁⊑N₁′ N₁′→N₂′
...   | ⟨ N₂ , ⟨ N₁↠N₂ , N₂⊑N₂′ ⟩ ⟩ = ⟨ snd N₂ , ⟨ plug-cong F-snd N₁↠N₂ , ⊑ᶜ-snd N₂⊑N₂′ ⟩ ⟩
gradual-guarantee-snd {N₁ = N₁} lpN₁ refl eq2 (ξ-blame {F = F})
  with plug-inv-snd F eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩ with ⊑ᶜ→⊑ ⊑*-∅ lpN₁
...   | pair⊑ lpA lpB = ⟨ snd N₁ , ⟨ snd N₁ ∎ , ⊑ᶜ-blame lpB ⟩ ⟩
gradual-guarantee-snd lpN₁ refl refl (β-snd vV′ vW′) = sim-snd-cons vV′ vW′ lpN₁
gradual-guarantee-snd lpN₁ refl refl (snd-cast v′ {x′} {i′}) = sim-snd-wrap v′ i′ x′ lpN₁

gradual-guarantee-if : ∀ {A A′} {L L′ : ∅ ⊢ ` 𝔹} {M : ∅ ⊢ A} {N : ∅ ⊢ A} {M′ : ∅ ⊢ A′} {N′ : ∅ ⊢ A′} {M₁ : ∅ ⊢ A} {M₁′ M₂′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ L ⊑ᶜ L′ → ∅ , ∅ ⊢ M ⊑ᶜ M′ → ∅ , ∅ ⊢ N ⊑ᶜ N′
  → M₁ ≡ if L M N → M₁′ ≡ if L′ M′ N′
  → M₁′ —→ M₂′
    -----------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
gradual-guarantee-if {L = L} {L′} {M} {N} {M′} {N′} lpL lpM lpN refl eq2 (ξ {F = F-if M′ᵒ N′ᵒ} rd)
  with plug-inv-if eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩
  with gradual-guarantee lpL rd
... | ⟨ L₂ , ⟨ rd* , lpL₂ ⟩ ⟩ = ⟨ if L₂ M N , ⟨ plug-cong (F-if M N) rd* , ⊑ᶜ-if lpL₂ lpM lpN ⟩ ⟩
gradual-guarantee-if {L = L} {L′} {M} {N} {M′} {N′} lpL lpM lpN refl eq2 (ξ-blame {F = F-if M′ᵒ N′ᵒ})
  with plug-inv-if eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩ = ⟨ if L M N , ⟨ if L M N ∎ , ⊑ᶜ-blame (⊑ᶜ→⊑ ⊑*-∅ lpM) ⟩ ⟩
gradual-guarantee-if {L′ = .($ true)  {P-Base}} lpL lpM lpN refl refl β-if-true  = sim-if-true  lpL lpM
gradual-guarantee-if {L′ = .($ false) {P-Base}} lpL lpM lpN refl refl β-if-false = sim-if-false lpL lpN

gradual-guarantee-wrap : ∀ {A A′ B B′} {M : ∅ ⊢ A} {M′ : ∅ ⊢ A′} {M₁ : ∅ ⊢ B} {M₁′ M₂′ : ∅ ⊢ B′}
                           {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)} {i : Inert c} {i′ : Inert c′}
  → ⟪ i ⟫⊑⟪ i′ ⟫ → ∅ , ∅ ⊢ M ⊑ᶜ M′
  → M₁ ≡ M ⟪ i ⟫ → M₁′ ≡ M′ ⟪ i′ ⟫
  → M₁′ —→ M₂′
    ---------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
gradual-guarantee-wrap {i = i} lpi lpM refl eq2 (ξ {F = F-wrap _} rd)
  with plug-inv-wrap-M eq2
... | ⟨ refl , refl ⟩
  with plug-inv-wrap-i eq2
...   | ⟨ refl , refl ⟩
  with gradual-guarantee lpM rd
...     | ⟨ M₂ , ⟨ rd* , lpM₂ ⟩ ⟩ = ⟨ M₂ ⟪ i ⟫ , ⟨ plug-cong (F-wrap _) rd* , ⊑ᶜ-wrap lpi lpM₂ ⟩ ⟩
gradual-guarantee-wrap {M = M} {i = i} lpi lpM refl eq2 (ξ-blame {F = F-wrap _})
  with plug-inv-wrap-M eq2
... | ⟨ refl , refl ⟩
  with plug-inv-wrap-i eq2
...   | ⟨ refl , refl ⟩ = ⟨ M ⟪ i ⟫ , ⟨ M ⟪ i ⟫ ∎ , ⊑ᶜ-blame (proj₂ (lpii→⊑ lpi)) ⟩ ⟩

gradual-guarantee-wrapr : ∀ {A A′ B′} {M′ : ∅ ⊢ A′} {M₁ : ∅ ⊢ A} {M₁′ M₂′ : ∅ ⊢ B′} {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
  → A ⊑⟪ i′ ⟫ → ∅ , ∅ ⊢ M₁ ⊑ᶜ M′
  → M₁′ ≡ M′ ⟪ i′ ⟫
  → M₁′ —→ M₂′
    ---------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
-- The proofs for both cases are practically the same as `wrap`.
gradual-guarantee-wrapr lpi lpM₁ eq (ξ {F = F-wrap _} rd)
  with plug-inv-wrap-M eq
... | ⟨ refl , refl ⟩
  with plug-inv-wrap-i eq
...   | ⟨ refl , refl ⟩
  with gradual-guarantee lpM₁ rd
...     | ⟨ M₂ , ⟨ rd* , lpM₂ ⟩ ⟩ = ⟨ M₂ , ⟨ rd* , ⊑ᶜ-wrapr lpi lpM₂ ⟩ ⟩
gradual-guarantee-wrapr {M₁ = M₁} lpi lpM₁ eq (ξ-blame {F = F-wrap _})
  with plug-inv-wrap-M eq
... | ⟨ refl , refl ⟩
  with plug-inv-wrap-i eq
...   | ⟨ refl , refl ⟩ = ⟨ M₁ , ⟨ M₁ ∎ , ⊑ᶜ-blame (proj₂ (lpti→⊑ lpi)) ⟩ ⟩

gradual-guarantee-app : ∀ {A A′ B B′} {L : ∅ ⊢ A ⇒ B} {L′ : ∅ ⊢ A′ ⇒ B′} {M : ∅ ⊢ A} {M′ : ∅ ⊢ A′} {M₁ : ∅ ⊢ B} {M₁′ M₂′ : ∅ ⊢ B′}
  → ∅ , ∅ ⊢ L ⊑ᶜ L′ → ∅ , ∅ ⊢ M ⊑ᶜ M′
  → M₁ ≡ L · M → M₁′ ≡ L′ · M′
  → M₁′ —→ M₂′
    ---------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))
gradual-guarantee-app {M = M} lpL lpM refl eq2 (ξ {F = F-·₁ _} rd)
  with plug-inv-app₁ eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩
  with gradual-guarantee lpL rd
...   | ⟨ L₂ , ⟨ rd* , lpL₂ ⟩ ⟩ = ⟨ L₂ · M , ⟨ plug-cong (F-·₁ _) rd* , ⊑ᶜ-· lpL₂ lpM ⟩ ⟩
gradual-guarantee-app {L = L} {M = M} lpL lpM refl eq2 (ξ {F = F-·₂ _ {v}} rd)
  with plug-inv-app₂ {vL = v} eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩
  with catchup v lpL
... | ⟨ L₂ , ⟨ vL₂ , ⟨ rd*₁ , lpL₂ ⟩ ⟩ ⟩
  with gradual-guarantee lpM rd
... | ⟨ M₂ , ⟨ rd*₂ , lpM₂ ⟩ ⟩ =
  ⟨ L₂ · M₂ , ⟨ ↠-trans (plug-cong (F-·₁ _) rd*₁) (plug-cong (F-·₂ _ {vL₂}) rd*₂) , ⊑ᶜ-· lpL₂ lpM₂ ⟩ ⟩
gradual-guarantee-app {L = L} {M = M} lpL lpM refl eq2 (ξ-blame {F = F-·₁ _})
  with plug-inv-app₁ eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩
  with ⊑ᶜ→⊑ ⊑*-∅ lpL
...   | fun⊑ lpA lpB = ⟨ L · M , ⟨ L · M ∎ , ⊑ᶜ-blame lpB ⟩ ⟩
gradual-guarantee-app {L = L} {M = M} lpL lpM refl eq2 (ξ-blame {F = F-·₂ _ {v}})
  with plug-inv-app₂ {vL = v} eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩
  with ⊑ᶜ→⊑ ⊑*-∅ lpL
...   | fun⊑ lpA lpB = ⟨ L · M , ⟨ L · M ∎ , ⊑ᶜ-blame lpB ⟩ ⟩
gradual-guarantee-app lpL lpM refl refl (β v) = {!!}
gradual-guarantee-app lpL lpM refl refl δ = sim-app-δ lpL lpM
gradual-guarantee-app lpL lpM refl refl (fun-cast v w) = {!!}


gradual-guarantee ⊑ᶜ-prim rd = ⊥-elim (V⌿→ V-const rd)
gradual-guarantee (⊑ᶜ-ƛ _ _) rd = ⊥-elim (V⌿→ V-ƛ rd)
gradual-guarantee (⊑ᶜ-· lpL lpM) rd = {!!}
gradual-guarantee (⊑ᶜ-if lpL lpM lpN) rd = gradual-guarantee-if lpL lpM lpN refl refl rd
gradual-guarantee (⊑ᶜ-cons lpM lpN) rd = gradual-guarantee-cons lpM lpN refl refl rd
gradual-guarantee (⊑ᶜ-fst lpM) rd = gradual-guarantee-fst lpM refl refl rd
gradual-guarantee (⊑ᶜ-snd lpM) rd = gradual-guarantee-snd lpM refl refl rd
gradual-guarantee (⊑ᶜ-inl lp lpf) rd = gradual-guarantee-inl lp lpf refl refl rd
gradual-guarantee (⊑ᶜ-inr lp lpf) rd = gradual-guarantee-inr lp lpf refl refl rd
gradual-guarantee (⊑ᶜ-case lpf lpf₁ lpf₂) rd = {!!}
gradual-guarantee (⊑ᶜ-cast x x₁ lpf) rd = {!!}
gradual-guarantee (⊑ᶜ-castl x x₁ lpf) rd = {!!}
gradual-guarantee (⊑ᶜ-castr x x₁ lpf) rd = {!!}
gradual-guarantee (⊑ᶜ-wrap lpi lpM) rd = gradual-guarantee-wrap lpi lpM refl refl rd
gradual-guarantee (⊑ᶜ-wrapl {i = i} lpi lpM) rd
  with gradual-guarantee lpM rd
... | ⟨ M₂ , ⟨ rd* , lpM₂ ⟩ ⟩ = ⟨ M₂ ⟪ i ⟫ , ⟨ plug-cong (F-wrap i) rd* , ⊑ᶜ-wrapl lpi lpM₂ ⟩ ⟩
gradual-guarantee (⊑ᶜ-wrapr lpi lpM) rd = gradual-guarantee-wrapr lpi lpM refl rd
gradual-guarantee (⊑ᶜ-blame _) rd = ⊥-elim (blame⌿→ rd)
