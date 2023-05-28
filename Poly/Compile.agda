{-# OPTIONS --rewriting #-}

open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning

open import Poly.Types
open import Poly.Gradual renaming (Term to GTerm; `_ to #_)
open import Poly.CastCalculus renaming (Term to CTerm)

module Poly.Compile where

coerce : ∀{A}{B}{𝒞} Γ → 𝒞 ⊢ A ~ B → Σ[ c ∈ CTerm ] (Γ ⊢ c ⦂ A ↝ B)
coerce {.★} {.★} {𝒞} Γ unk~unk = idᶜ , wt-id
coerce {.Nat} {.Nat} {𝒞} Γ nat~nat = idᶜ , wt-id
coerce {^ X} {^ Y} {𝒞} Γ (var~var XY∈𝒞) = {!!} , {!!} {- problem! -}
coerce {.★} {.(^ _)} {𝒞} Γ (unk~var x) = {!!} , {!!} {- problem! -}
coerce {.(^ _)} {.★} {𝒞} Γ (var~unk x) = {!!} , {!!} {- problem! -}
coerce {.★} {.Nat} {𝒞} Γ unk~nat = (nat ??) , wt-proj G-nat
coerce {.★} {B₁ ⇒ B₂} {𝒞} Γ (unk~fun B₁~★ ★~B₂)
    with coerce Γ B₁~★ | coerce Γ ★~B₂
... | c , ⊢c | d , ⊢d =
    ((★→★ ??) ⍮ (c ↪ d)) , wt-seq (wt-proj G-fun) (wt-fun ⊢c ⊢d)
coerce {.Nat} {.★} {𝒞} Γ nat~unk = (nat !!) , wt-inj G-nat
coerce {A₁ ⇒ A₂} {.★} {𝒞} Γ (fun~unk ★~A₁ A₂~★)
    with coerce Γ ★~A₁ | coerce Γ A₂~★
... | c , ⊢c | d , ⊢d =
    ((c ↪ d) ⍮ (★→★ !!)) , wt-seq (wt-fun ⊢c ⊢d) (wt-inj G-fun)
coerce {A ⇒ B} {A′ ⇒ B′} {𝒞} Γ (fun~fun A~A′ B~B′)
    with coerce Γ A~A′ | coerce Γ B~B′
... | c , ⊢c | d , ⊢d =
    c ↪ d , wt-fun ⊢c ⊢d
coerce {∀̇ A} {∀̇ B} {𝒞} Γ (all~all A~B)
    with coerce Γ A~B
... | c , ⊢c = ∀̰ c , wt-all ⊢c
coerce {∀̇ A} {B} {𝒞} Γ (all~any A~B)
    with coerce Γ A~B
... | c , ⊢c = inst c , wt-inst ⊢c
coerce {A} {∀̇ B} {𝒞} Γ (any~all A~B)
    with coerce Γ A~B
... | c , ⊢c = gen c , wt-gen ⊢c

{-
coerce ★ ★ unk~unk = idᶜ
coerce ★ Nat = nat ??
coerce ★ (B₁ ⇒ B₂)
    with ★ =?ᵗ B₁ | ★ =?ᵗ B₂
... | no no1 | _ = (★→★ ??) ⍮ coerce (★ ⇒ ★) (B₁ ⇒ B₂)
... | yes refl | no no2 = (★→★ ??) ⍮ coerce (★ ⇒ ★) (B₁ ⇒ B₂)
... | yes refl | yes refl = ★→★ ??
coerce ★ (∀̇ B) = {!!}
coerce ★ (^ Y) = {!!}
coerce Nat B = {!!}
coerce (^ X) B = {!!}
coerce (A₁ ⇒ A₂) ★ = {!!}
coerce (A₁ ⇒ A₂) Nat = {!!}
coerce (A₁ ⇒ A₂) (^ Y) = {!!}
coerce (A₁ ⇒ A₂)  = {!!}
coerce (A₁ ⇒ A₂) B = {!!}
coerce (A₁ ⇒ A₂) B = {!!}
coerce (∀̇ A) B = {!!}
-}

compile : ∀{Γ}{M : GTerm}{A} → Γ ⊢ᵍ M ⦂ A → Σ[ M′ ∈ CTerm ] (Γ ⊢ M′ ⦂ A)
compile (⊢ᵍ-nat n) = $ n , ⊢-nat n
compile {M = # x} (⊢ᵍ-var ∋x) = (` x) , ⊢-var ∋x
compile {M = λᵍ A N} (⊢ᵍ-lam Aok ⊢N)
    with compile ⊢N
... | N′ , ⊢N′ = ƛ N′ , ⊢-lam Aok ⊢N′
compile {Γ} (⊢ᵍ-app ⊢L ⊢M A′~A)
    with compile ⊢L | compile ⊢M
... | L′ , ⊢L′ | M′ , ⊢M′
    with coerce Γ A′~A
... | c , ⊢c =    
    L′ · (M′ ⟨ c ⟩) , ⊢-app ⊢L′ (⊢-cast ⊢M′ ⊢c)
compile (⊢ᵍ-app★ ⊢M ⊢M₁) = {!!}
compile (⊢ᵍ-tyabs x ⊢M) = {!!}
compile (⊢ᵍ-tyapp ⊢M x) = {!!}
compile (⊢ᵍ-tyapp★ ⊢M x) = {!!}
