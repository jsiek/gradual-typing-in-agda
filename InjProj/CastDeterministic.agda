{-# OPTIONS --rewriting #-}
module InjProj.CastDeterministic where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
--open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import Structures using (extensionality)
open import InjProj.CastCalculus
open import InjProj.Reduction

inject-eq : ∀{G}{N N′}
   → (N ⟨ G !⟩) ≡ (N′ ⟨ G !⟩)
   → N ≡ N′
inject-eq {G} {N} {.N} refl = refl

deterministic : ∀{M N N′}
  → M ⟶ N
  → M ⟶ N′
  → N ≡ N′
deterministic (ξ (□· M) M⟶N) (ξ (□· M₁) M⟶N′)
    with deterministic M⟶N M⟶N′
... | refl = refl
deterministic (ξ (□· M) M⟶N) (ξ (v ·□) M⟶N′) =
    ⊥-elim (value-irreducible v M⟶N)
deterministic (ξ (□· M) M⟶N) (ξ-blame (□· M₁)) =
    ⊥-elim (blame-irreducible M⟶N)
deterministic (ξ (□· M) M⟶N) (ξ-blame (v ·□)) =
    ⊥-elim (value-irreducible v M⟶N)
deterministic (ξ (□· M) M⟶N) (β v) =
    ⊥-elim (value-irreducible (ƛ̬ _) M⟶N)
deterministic (ξ (v ·□) M⟶N) (ξ (□· M) M⟶N′) = 
    ⊥-elim (value-irreducible v M⟶N′)
deterministic (ξ (v ·□) M⟶N) (ξ (v₁ ·□) M⟶N′)
    with deterministic M⟶N M⟶N′
... | refl = refl
deterministic (ξ (() ·□) M⟶N) (ξ-blame (□· M))
deterministic (ξ (v ·□) M⟶N) (ξ-blame (v₁ ·□)) =
    ⊥-elim (blame-irreducible M⟶N)
deterministic (ξ (v ·□) M⟶N) (β x) =
    ⊥-elim (value-irreducible x M⟶N)
deterministic (ξ (□⟨ G !⟩) M⟶N) (ξ (□⟨ _ !⟩) M⟶N′)
    with deterministic M⟶N M⟶N′
... | refl = refl
deterministic (ξ (□⟨ G !⟩) M⟶N) (ξ-blame (□⟨ _ !⟩)) =
    ⊥-elim (blame-irreducible M⟶N)
deterministic (ξ (□⟨ H ?⟩) M⟶N) (ξ (□⟨ _ ?⟩) M⟶N′)
    with deterministic M⟶N M⟶N′
... | refl = refl
deterministic (ξ (□⟨ H ?⟩) M⟶N) (ξ-blame (□⟨ _ ?⟩)) =
    ⊥-elim (blame-irreducible M⟶N)
deterministic (ξ □⟨ H ?⟩ r) (collapse v refl) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (ξ □⟨ H ?⟩ r) (collide v neq refl) = 
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (ξ-blame (□· M)) (ξ (□· M₁) M⟶N′) =
    ⊥-elim (blame-irreducible M⟶N′)
deterministic (ξ-blame (□· M)) (ξ (() ·□) M⟶N′)
deterministic (ξ-blame (□· M)) (ξ-blame (□· M₁)) = refl
deterministic (ξ-blame (□· M)) (ξ-blame (v ·□)) = refl
deterministic (ξ-blame (v ·□)) (ξ (□· M) M⟶N′) =
    ⊥-elim (value-irreducible v M⟶N′)
deterministic (ξ-blame (v ·□)) (ξ (v₁ ·□) M⟶N′) =
    ⊥-elim (blame-irreducible M⟶N′)
deterministic (ξ-blame (() ·□)) (ξ-blame (□· .blame))
deterministic (ξ-blame (v ·□)) (ξ-blame (v₁ ·□)) = refl
deterministic (ξ-blame (□⟨ G !⟩)) (ξ (□⟨ _ !⟩) M⟶N′) =
    ⊥-elim (blame-irreducible M⟶N′)
deterministic (ξ-blame (□⟨ G !⟩)) (ξ-blame (□⟨ _ !⟩)) = refl
deterministic (ξ-blame (□⟨ H ?⟩)) (ξ (□⟨ _ ?⟩) M⟶N′) =
    ⊥-elim (blame-irreducible M⟶N′)
deterministic (ξ-blame (□⟨ H ?⟩)) (ξ-blame (□⟨ _ ?⟩)) = refl
deterministic (β x) (ξ (□· M) M⟶N′) = ⊥-elim (value-irreducible (ƛ̬ _) M⟶N′)
deterministic (β x) (ξ (v ·□) M⟶N′) = ⊥-elim (value-irreducible x M⟶N′)
deterministic (β ()) (ξ-blame (v ·□))
deterministic (β x) (β x₁) = refl
deterministic (collapse v refl) (ξξ □⟨ _ ?⟩ refl refl r) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (collapse v refl) (ξξ-blame (□· M) ())
deterministic (collapse v refl) (ξξ-blame (v₁ ·□) ())
deterministic (collapse v refl) (ξξ-blame □⟨ _ !⟩ ())
deterministic (collapse v refl) (ξξ-blame □⟨ _ ?⟩ ())
deterministic (collapse v refl) (collapse x refl) = refl
deterministic (collapse v refl) (collide x neq refl) =
    ⊥-elim (neq refl)
deterministic (collide v neq refl) (ξξ □⟨ _ ?⟩ refl refl r) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (collide v neq refl) (ξξ-blame (□· M) ())
deterministic (collide v neq refl) (ξξ-blame (v₁ ·□) ())
deterministic (collide v neq refl) (ξξ-blame □⟨ _ !⟩ ())
deterministic (collide v neq refl) (ξξ-blame □⟨ _ ?⟩ ())
deterministic (collide v neq refl) (collapse x refl) =
    ⊥-elim (neq refl)
deterministic (collide v neq refl) (collide x x₁ x₂) = refl

frame-inv2 : ∀{L N : Term}{F}
   → reducible L
   → F ⟦ L ⟧ ⟶ N
   → ∃[ L′ ] ((L ⟶ L′) × (N ≡ F ⟦ L′ ⟧))
frame-inv2{L}{.((□· M₁) ⟦ _ ⟧)}{□· M} (L′ , L→L′) (ξξ (□· M₁) refl refl L→N) =
    L′ , (L→L′ , cong (λ X → X · M) (deterministic L→N L→L′))
frame-inv2 {L} {.((v ·□) ⟦ _ ⟧)} {□· M} (L′ , L→L′) (ξξ (v ·□) refl refl FL→N) =
   ⊥-elim (value-irreducible v L→L′)
frame-inv2 {L} {.blame} {□· M} (L′ , L→L′) (ξξ-blame (□· M₁) refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {.blame} {□· M} (L′ , L→L′) (ξξ-blame (v ·□) refl) =
    ⊥-elim (value-irreducible v L→L′)
frame-inv2 {ƛ N} {_} {□· M} (L′ , L→L′) (β x) =
    ⊥-elim (value-irreducible (ƛ̬ N) L→L′)
frame-inv2 {L} {N} {v ·□} (L′ , L→L′) (ξξ (□· M) refl refl FL→N) =
    ⊥-elim (value-irreducible v FL→N)
frame-inv2 {L} {N} {v ·□} (L′ , L→L′) (ξξ (v₁ ·□) refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {() ·□} (L′ , L→L′) (ξξ-blame (□· M) refl)
frame-inv2 {L} {.blame} {v ·□} (L′ , L→L′) (ξξ-blame (v₁ ·□) refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {_} {v ·□} (L′ , L→L′) (β w) =
    ⊥-elim (value-irreducible w L→L′)
frame-inv2 {L} {N} {□⟨ G !⟩} (L′ , L→L′) (ξξ □⟨ _ !⟩ refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {□⟨ G !⟩} (L′ , L→L′) (ξξ-blame □⟨ _ !⟩ refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {_} {□⟨ H ?⟩} (L′ , L→L′) (ξξ □⟨ _ ?⟩ refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {□⟨ H ?⟩} (L′ , L→L′) (ξξ-blame □⟨ _ ?⟩ refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {N} {□⟨ H ?⟩} (L′ , L→L′) (collapse v refl) = 
    ⊥-elim (value-irreducible (v 〈 _ 〉) L→L′)
frame-inv2 {L} {.blame} {□⟨ H ?⟩} (L′ , L→L′) (collide v neq refl) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) L→L′)

frame-inv3 : ∀{L N : Term}{F : PEFrame}
   → reducible L
   → F ⦉ L ⦊ ⟶ N
   → ∃[ L′ ] ((L ⟶ L′) × (N ≡ F ⦉ L′ ⦊))
frame-inv3 {L}{N}{□} rL FL→N = _ , (FL→N , refl)
frame-inv3 {L}{N}{` F} rL FL→N = frame-inv2 rL FL→N

blame-frame2 : ∀{F}{N}
   → (F ⦉ blame ⦊) ⟶ N
   → N ≡ blame
blame-frame2 {□}{N} Fb→N = ⊥-elim (blame-irreducible Fb→N)
blame-frame2 {` F}{N} Fb→N = blame-frame Fb→N

step-value-plus-one : ∀{M N V}
   → (M→N : M ↠ N)
   → (M→V : M ↠ V)
   → Value V
   → len M→N ≡ suc (len M→V)
   → ⊥
step-value-plus-one (_ ⟶⟨ r ⟩ _ END) (_ END) v eq = value-irreducible v r
step-value-plus-one (_ ⟶⟨ r1 ⟩ M→N) (_ ⟶⟨ r2 ⟩ M→V) v eq
    with deterministic r1 r2
... | refl = step-value-plus-one M→N M→V v (suc-injective eq)

step-blame-plus-one : ∀{M N}
   → (M→N : M ↠ N)
   → (M→b : M ↠ blame)
   → len M→N ≡ suc (len M→b)
   → ⊥
step-blame-plus-one (_ ⟶⟨ r ⟩ _ END) (_ END) eq = blame-irreducible r
step-blame-plus-one (_ ⟶⟨ r1 ⟩ M→N) (_ ⟶⟨ r2 ⟩ M→b) eq
    with deterministic r1 r2
... | refl = step-blame-plus-one M→N M→b (suc-injective eq)

diverge-not-halt : ∀{M}
  → M ⇑
  → ¬ halt M
diverge-not-halt divM (inj₁ M→blame)
    with divM (suc (len M→blame))
... | N , M→N , eq = step-blame-plus-one M→N M→blame (sym eq)    
diverge-not-halt divM (inj₂ (V , M→V , v))
    with divM (suc (len M→V))
... | N , M→N , eq = step-value-plus-one M→N M→V v (sym eq)    
  
cant-reduce-value-and-blame : ∀{M}{V}
   → Value V
   → M ↠ V
   → M ↠ blame
   → ⊥
cant-reduce-value-and-blame v (M END) (M ⟶⟨ M→N ⟩ N→b) =
  ⊥-elim (value-irreducible v M→N)
cant-reduce-value-and-blame v (.blame ⟶⟨ M→N ⟩ N→V) (.blame END) =
  ⊥-elim (blame-irreducible M→N)
cant-reduce-value-and-blame v (M ⟶⟨ M→N ⟩ N→V) (.M ⟶⟨ M→N′ ⟩ N′→b)
  rewrite deterministic M→N M→N′ = cant-reduce-value-and-blame v N→V N′→b

{-
determinism : ∀{M N}
  → (r1 : M ⟶ N)
  → (r2 : M ⟶ N)
  → r1 ≡ r2
determinism {M} {N} (ξξ (□· M₁) eq1 eq2 r1) (ξξ (□· M₂) eq3 eq4 r2)
    with eq1 | eq2 | eq3 | eq4 
... | refl | refl | refl | refl
    with deterministic r1 r2
... | refl rewrite determinism r1 r2 = refl    
determinism {M} {N} (ξξ (□· M₁) eq1 eq2 r1) (ξξ (v ·□) eq3 eq4 r2)
    with eq1 | eq2 | eq3 | eq4 
... | refl | refl | refl | refl = ⊥-elim (value-irreducible v r1)
determinism {M} {N} (ξξ (□· M₁) eq1 eq2 r1) (ξξ □⟨ G !⟩ eq3 eq4 r2)
    with eq1 | eq2 | eq3
... | refl | refl | ()
determinism {M} {N} (ξξ (□· M₁) eq1 eq2 r1) (ξξ □⟨ H ?⟩ eq3 eq4 r2)
    with eq1 | eq2 | eq3
... | refl | refl | ()
determinism {.(ƛ _ · _)} {_} (ξξ (□· M₁) eq1 eq2 r1) (β x₂)
    with eq1
... | refl = ⊥-elim (value-irreducible (ƛ̬ _) r1)
determinism {M} {N} (ξξ (v ·□) eq1 eq2 r1) r2 = {!!}
determinism {M} {N} (ξξ □⟨ G !⟩ x x₁ r1) r2 = {!!}
determinism {M} {N} (ξξ □⟨ H ?⟩ x x₁ r1) r2 = {!!}
determinism {M} {.blame} (ξξ-blame F x) r2 = {!!}
determinism {.(ƛ _ · _)} {_} (β x) r2 = {!!}
determinism {.(_ ⟨ _ ?⟩)} {N} (collapse x x₁) r2 = {!!}
determinism {.(_ ⟨ _ ?⟩)} {.blame} (collide x x₁ x₂) r2 = {!!}

triangle↠ : ∀{L M N : Term}
   → (L→M : L ↠ M)
   → (L→N : L ↠ N)
   → (len L→M ≤ len L→N)
   → (Σ[ M→N ∈ (M ↠ N) ] (L→N ≡ (L→M ++ M→N)))
triangle↠ (_ END) L→N m≤n  = L→N , refl 
triangle↠ (_ ⟶⟨ L→M₁ ⟩ M₁→M)
            (_ ⟶⟨ L→M₂ ⟩ M₂→N) (s≤s m≤n)
    with deterministic L→M₁ L→M₂
... | refl
    with triangle↠ M₁→M M₂→N m≤n
... | M→N , refl
    with determinism L→M₁ L→M₂
... | refl = M→N , refl    
-}
