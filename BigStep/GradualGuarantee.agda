{-# OPTIONS --rewriting #-}
module BigStep.GradualGuarantee where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Maybe
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import BigStep.Cast
open import BigStep.BigStepGas

Val : Set
Val = ∃[ V ] Value V

trm : Val → Term
trm (V , v) = V

val : (v : Val) → Value (trm v)
val (V , v) = v

_⊑̬_ : Val → Val → ℕ → Set
(V ⊑̬ V′) zero = ⊤
(($ c , _) ⊑̬ ($ c′ , _)) (suc k) = c ≡ c′
(($ c , _) ⊑̬ V′) (suc k) = ⊥
((ƛ N , _) ⊑̬ (ƛ N′ , _)) (suc k) = 
       (∀ {W W′ V′ : Val}
        → (W ⊑̬ W′) k → N′ [ trm W′ ] ⇓ trm V′ # k
        → ∃[ V ] N [ trm W ] ⇓ trm V # k × (V ⊑̬ V′) k)

((ƛ N , _) ⊑̬ V′) (suc k) = ⊥
((V ⟨ G !⟩ , v 〈 _ 〉) ⊑̬ (V′ ⟨ H !⟩ , v′ 〈 _ 〉)) (suc k)
    with G ≡ᵍ H
... | yes refl = ((V , v) ⊑̬ (V′ , v′)) k
... | no neq = ⊥
((V ⟨ G !⟩ , v 〈 _ 〉) ⊑̬ v′) (suc k) = ⊥

postulate downClosed⊑̬ : ∀{V}{V′}{k}{j} → (V ⊑̬ V′) k → j ≤ k → (V ⊑̬ V′) j

⊑̬-lam-R-inv : ∀{V : Val}{N′}{k}
   → (V ⊑̬ (ƛ N′ , ƛ̬ N′)) (suc k)
   → ∃[ N ] V ≡ (ƛ N , ƛ̬ N) ×
       (∀ {W W′ V′ : Val}
        → (W ⊑̬ W′) k → N′ [ trm W′ ] ⇓ trm V′ # k
        → ∃[ V ] N [ trm W ] ⇓ trm V # k × (V ⊑̬ V′) k)
⊑̬-lam-R-inv {.(ƛ N) , (ƛ̬ N)} {N′} {k} V⊑λN′ = N , (refl , V⊑λN′)

{-
⊑-lam-R-inv : ∀{V}{N′}{A}{B}{A′}{B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}
   → Value V
   → [] ⊩ V ⊑ ƛ N′ ⦂ fun⊑ A⊑A′ B⊑B′
   → ∃[ N ] V ≡ ƛ N  ×  (A , A′ , A⊑A′) ∷ [] ⊩ N ⊑ N′ ⦂ B⊑B′
⊑-lam-R-inv {.(ƛ N)} (ƛ̬ N) (⊑-lam N⊑N′) = N , refl , N⊑N′
-}

sim : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}{V′ : Val}{k}
   → [] ⊩ M ⊑ M′ ⦂ A⊑A′
   → M′ ⇓ trm V′ # k
   → ∃[ V ] M ⇓ trm V # k × (V ⊑̬ V′) k
   
sim {_} {_} {.base⊑} {$ c} {$ c} ⊑-lit lit⇓ = ($ c , $̬ c) , lit⇓ , refl
sim {A} {A′} {A⊑A′} {.(_ · _)} {.(_ · _)}{k = suc k} (⊑-app L⊑L′ M⊑M′)
    (app⇓{N = N′}{W = W′}{V = V′} L′⇓λN′ M′⇓W′ w′ NW′⇓V′ v′) 
    with sim{V′ = (ƛ N′ , ƛ̬ N′)} L⊑L′ L′⇓λN′ | sim{V′ = (W′ , w′)} M⊑M′ M′⇓W′
... | (λN , v) , L⇓V , V⊑λN | (W , w) , M⇓W , W⊑W′
    with ⊑̬-lam-R-inv{V = (λN , v)}{N′ = N′}{k} V⊑λN
... | N , refl , body 
    with body{(W , w)}{(W′ , w′)}{V′ , v′}
               (downClosed⊑̬ W⊑W′ (n≤1+n k)) NW′⇓V′ 
... | (V , v) , NW⇓V , V⊑V′ =
      (V , v) , ((app⇓ L⇓V M⇓W w NW⇓V v) , {!V⊑V′!})
{-
V⊑V′   : ((V , v) ⊑̬ (proj₁ V′₁ , v′)) k
Goal: ((V , v) ⊑̬ V′₁) (suc k)
-}

sim {.(_ ⇒ _)} {.(_ ⇒ _)} {.(fun⊑ _ _)} {.(ƛ _)} {.(ƛ _)} (⊑-lam M⊑M′) M′⇓V′ = {!!}
sim {.★} {A′} {.unk⊑} {.(_ ⟨ _ !⟩)} {M′} (⊑-inj-L M⊑M′) M′⇓V′ = {!!}
sim {.★} {.★} {.unk⊑} {M} {.(_ ⟨ _ !⟩)} (⊑-inj-R M⊑M′) M′⇓V′ = {!!}
sim {.(gnd⇒ty _)} {A′} {A⊑A′} {.(_ ⟨ _ ?⟩)} {M′} (⊑-proj-L M⊑M′) M′⇓V′ = {!!}
sim {.★} {.(gnd⇒ty _)} {A⊑A′} {M} {.(_ ⟨ _ ?⟩)} (⊑-proj-R M⊑M′) M′⇓V′ = {!!}
sim {A} {.A} {.Refl⊑} {M} {.blame} (⊑-blame x) M′⇓V′ = {!!}
