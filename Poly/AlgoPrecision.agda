{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-++-commute; map-compose)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
open import Data.List.Membership.DecPropositional using (_∈?_) renaming (_∈_ to _∈ₗ_)
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig renaming (ν to nu)
open import Var using (Var)
open import Poly.SetsAsPredicates
open import Poly.Types

module Poly.AlgoPrecision where

vars : Type → List Var
vars Nat = []
vars ★ = []
vars (^ X) = X ∷ []
vars (A ⇒ B) = vars A ++ vars B
vars (∀̇ A) = dec (vars A)

dec-both : List (Var × Var) → List (Var × Var)
dec-both [] = []
dec-both ((zero , zero) ∷ ls) = dec-both ls
dec-both ((zero , suc y) ∷ ls) = dec-both ls {- shouldn't happen -}
dec-both ((suc x , zero) ∷ ls) = dec-both ls {- shouldn't happen -}
dec-both ((suc x , suc y) ∷ ls) = (x , y) ∷ dec-both ls

dec-cod : List (Var × Var) → List (Var × Var)
dec-cod [] = []
dec-cod ((x , zero) ∷ ls) = dec-cod ls {- shouldn't happen -}
dec-cod ((x , suc y) ∷ ls) = (x , y) ∷ dec-cod ls

ok? : (Var × Var) → List (Var × Var) → 𝔹
ok? (x , y) [] = true
ok? (x , y) ((w , z) ∷ ls)
    with x ≟ w | y ≟ z
... | no _ | no _ = true
... | no _ | yes _ = false 
... | yes _ | no _ = false 
... | yes _ | yes _ = true 

merge : List (Var × Var) → List (Var × Var) → Maybe (List (Var × Var))
merge [] B2 = just B2
merge ((x , y) ∷ B1) B2
    with ok? (x , y) B2
... | false = nothing
... | true
    with merge B1 B2
... | nothing = nothing
... | just B3 = just ((x , y) ∷ B3)

pair-eq? : (p1 : Var × Var) → (p2 : Var × Var) → Dec (p1 ≡ p2)
pair-eq? (x1 , y1) (x2 , y2)
    with x1 ≟ x2 | y1 ≟ y2
... | no neq | _ = no λ { refl → neq refl}
... | yes refl | no neq = no λ { refl → neq refl}
... | yes refl | yes refl = yes refl

zero-cod? : (ls : List (Var × Var)) → Dec (∃[ x ] (_∈ₗ_ pair-eq? (x , 0)  ls))
zero-cod? [] = no λ { ()}
zero-cod? ((x , zero) ∷ ls) = yes (x , here refl)
zero-cod? ((x , suc y) ∷ ls)
    with zero-cod? ls
... | yes (x , mem) = yes (x , (there mem))
... | no nm = no λ { (z , there snd) → nm (z , snd)}

infix 3 _⊑?_
_⊑?_ : Type → Type → Maybe (List Var × List (Var × Var))
Nat ⊑? Nat = just ([] , [])
Nat ⊑? B = nothing
★ ⊑? B = just (vars B , [])
(^ X) ⊑? (^ Y) = just ([] , (X , Y) ∷ [])
(^ X) ⊑? B = nothing
(A₁ ⇒ A₂) ⊑? (B₁ ⇒ B₂)
    with A₁ ⊑? B₁ | A₂ ⊑? B₂
... | nothing | _ = nothing
... | just (G1 , B1) | nothing = nothing
... | just (G1 , B1) | just (G2 , B2)
    with merge B1 B2
... | nothing = nothing
... | just B3 = just (G1 ++ G2 , B3)
(A₁ ⇒ A₂) ⊑? ∀̇ B
    with (A₁ ⇒ A₂) ⊑? B
... | nothing = nothing
... | just (G1 , B1)
    with zero-cod? B1
... | yes xz∈B1 = nothing
... | no xz∉B1 = just (dec G1 , dec-cod B1) 

(A₁ ⇒ A₂) ⊑? B = nothing
(∀̇ A) ⊑? (∀̇ B)
    with (∀̇ A) ⊑? B
... | nothing = nothing
... | just (G1 , B1)
     {- choice: match up the two ∀'s or instantiate ∀̇ B -}
     {- match up if (0,0) ∈ B1 -}
    with _∈?_ pair-eq? ((0 , 0)) B1
... | yes zz∈B1
    with _∈?_ _≟_ 0 G1
... | yes z∈G1 = nothing    
... | no z∉G1 = just (dec G1 , dec-both B1)
(∀̇ A) ⊑? (∀̇ B) | just (G1 , B1)
    | no zz∉B1
    with zero-cod? B1
... | yes xz∈B1 = nothing
... | no xz∉B1 = 
      just (dec G1 , dec-cod B1)
(∀̇ A) ⊑? B = A ⊑? B

module Example where

  _ : (∀̇ (^ 0) ⊑? ∀̇ (^ 0)) ≡ just ([] , [])
  _ = refl

  _ : (★ ⊑? ∀̇ (^ 0)) ≡ just ([] , [])
  _ = refl

  _ : (★ ⊑? ∀̇ ★) ≡ just ([] , [])
  _ = refl

  _ : (★ ⊑? (^ 0)) ≡ just (0 ∷ [] , [])
  _ = refl

  _ : (∀̇ (^ 0) ⊑? ∀̇ (∀̇ (^ 0))) ≡ just ([] , [])
  _ = refl

  _ : (★ ⊑? Nat) ≡ just ([] , [])
  _ = refl

  _ : (★ ⇒ Nat ⊑? Nat ⇒ Nat) ≡ just ([] , [])
  _ = refl

  _ : (Nat ⇒ ★ ⊑? Nat ⇒ Nat) ≡ just ([] , [])
  _ = refl

  _ : (★ ⇒ ★ ⊑? (∀̇ ((^ 0) ⇒ (^ 0)))) ≡ just ([] , [])
  _ = refl

  _ : ((∀̇ ((^ 0) ⇒ (^ 0))) ⊑? (∀̇ ((^ 0) ⇒ (^ 0)))) ≡ just ([] , [])
  _ = refl

  _ : ((∀̇ ((^ 0) ⇒ ★)) ⊑? (∀̇ ((^ 0) ⇒ (^ 0)))) ≡ nothing
  _ = refl

