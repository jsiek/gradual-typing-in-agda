{-# OPTIONS --rewriting #-}
{-
   A polymorphic blame calculus partly based on a version 
   by Jeremy, Phil Wadler, and Peter Thiemann.
-}

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
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

module Poly.CastCalculus where

open import Poly.Types

{-------------      Terms    -------------}

data Op : Set where
  op-nat : ℕ → Op
  op-lam : Op
  op-app : Op
  op-tyabs : Op
  op-tyapp : Op
  op-cast : Op
  op-blame : Op
  op-nu : Op
  {- coercions -}
  c-id : Op
  c-inject : Op
  c-project : Op
  c-seal : Op
  c-unseal : Op
  c-fun : Op
  c-seq : Op
  c-all : Op
  c-inst : Op
  c-gen : Op
  {- ground types -}
  g-nat : Op
  g-fun : Op

sig : Op → List Sig
sig (op-nat n) = []
sig op-lam = (nu ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-tyabs = (nu ■) ∷ []
sig op-tyapp = ■ ∷ ■ ∷ []
sig op-cast = ■ ∷ ■ ∷ []
sig op-blame = []
sig op-nu = (nu ■) ∷ []
sig c-id = []
sig c-inject = ■ ∷ []
sig c-project = ■ ∷ []
sig c-seal = ■ ∷ []
sig c-unseal = ■ ∷ []
sig c-fun = ■ ∷ ■ ∷ []
sig c-seq = ■ ∷ ■ ∷ []
sig c-all = (nu ■) ∷ []
sig c-inst = (nu ■) ∷ []
sig c-gen = (nu ■) ∷ []
sig g-nat = []
sig g-fun = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern $ n = (op-nat n) ⦅ nil ⦆
pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern Λ N  = op-tyabs ⦅ cons (bind (ast N)) nil ⦆
infix 5 _【_】
pattern _【_】 L α = op-tyapp ⦅ cons (ast L) (cons (ast α) nil) ⦆
infix 5 _⟨_⟩
pattern _⟨_⟩ L c = op-tyapp ⦅ cons (ast L) (cons (ast c) nil) ⦆
pattern blame = op-blame ⦅ nil ⦆
infix 3 ν_
pattern ν_ N  = op-nu ⦅ cons (bind (ast N)) nil ⦆
pattern idᶜ = c-id ⦅ nil ⦆
pattern _!! G = c-inject ⦅ cons (ast G) nil ⦆
pattern _?? G = c-project ⦅ cons (ast G) nil ⦆
infix 6 _↡
pattern _↡ α = c-seal ⦅ cons (ast α) nil ⦆
infix 6 _↟
pattern _↟ α = c-unseal ⦅ cons (ast α) nil ⦆
pattern _↪_ c d = c-fun ⦅ cons (ast c) (cons (ast d) nil) ⦆
pattern _⍮_ c d = c-seq ⦅ cons (ast c) (cons (ast d) nil) ⦆
pattern ∀̰ c = c-all ⦅ cons (bind (ast c)) nil ⦆
pattern inst c = c-inst ⦅ cons (bind (ast c)) nil ⦆
pattern gen c = c-gen ⦅ cons (bind (ast c)) nil ⦆
pattern nat = g-nat ⦅ nil ⦆
pattern ★→★ = g-fun ⦅ nil ⦆

{----------------------- Ground Types ------------------------}

data Ground : Term → Set where

  G-nat : Ground nat
  G-fun : Ground ★→★
  G-var : ∀{α : Var} → Ground (` α)

{----------------------- Values ------------------------}

data Value : Term → Set where

  V-nat : ∀ {n : ℕ}
      -------------
    → Value ($ n)
    
  V-ƛ : ∀ {N : Term}
      ---------------------------
    → Value (ƛ N)

  V-Λ : ∀ {N : Term}
      ---------------------------
    → Value (Λ N)
    
value : ∀ {V : Term}
  → (v : Value V)
    -------------
  → Term
value {V = V} v  =  V  

{----------------------- Frames ------------------------}

infix  6 □·_
infix  6 _·□

data Frame : Set where

  □·_ : 
      (M : Term)
      ----------
    → Frame

  _·□ : ∀ {V : Term}
    → (v : Value V)
      -------------
    → Frame

  □【_】 :
     (α : Term)
     → Frame

  □⟨_⟩ :
     (c : Term)
     → Frame


_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
□【 α 】 ⟦ M ⟧       =  M 【 α 】
□⟨ c ⟩ ⟦ M ⟧        =  M ⟨ c ⟩

{-------------      Reduction Semantics    -------------}

infix 2 _—→_

data _—→_ : Term → Term → Set where

  β-ƛ : ∀ {N W : Term}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {N : Term}{α : Var}
      ---------------------------
    → (Λ N) 【 ` α 】 —→ N [ ` α ]

  -- todo: constraint on c?
  β-gen : ∀ {V : Term}{c : Term}{α : Var}
    → Value V
      ----------------------------------------
    → V ⟨ gen c ⟩ 【 ` α 】 —→ V ⟨ c [ ` α ] ⟩

  cast-id : ∀ {V : Term}
    → Value V
    → V ⟨ idᶜ ⟩ —→ V

  reveal : ∀ {V : Term}{α : Var}
    → Value V
    → V ⟨ ` α ↡ ⟩ ⟨ ` α ↟ ⟩ —→ V

  collapse : ∀ {V : Term}{G : Term}
    → Value V
    → V ⟨ G !! ⟩ ⟨ G ?? ⟩ —→ V

  conflict : ∀ {V : Term}{G H : Term}
    → Value V
    → G ≢ H
    → V ⟨ G !! ⟩ ⟨ H ?? ⟩ —→ blame

  cast-inst : ∀ {V : Term}{c : Term}
    → V ⟨ inst c ⟩ —→ ν V 【 ` 0 】 ⟨ c ⟩

  cast-all : ∀ {V : Term}{c : Term}
    → V ⟨ ∀̰ c ⟩ —→ Λ V ⟨ c ⟩

  cast-seq : ∀ {V : Term}{c d : Term}
    → V ⟨ c ⍮ d ⟩ —→ V ⟨ c ⟩ ⟨ d ⟩

  cast-fun : ∀ {V : Term}{c d : Term}
    → V ⟨ c ↪ d ⟩ —→ ƛ (V · ` 0 ⟨ c ⟩) ⟨ d ⟩

infix 2 _∣_—→_∣_

data _∣_—→_∣_ : ℕ → Term → ℕ → Term → Set where

  ξξ : ∀ {Σ}{M N : Term} {Σ′}{M′ N′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ M ⟧
    → N′ ≡ F ⟦ N ⟧
    → Σ ∣ M —→ Σ′ ∣ N
      -----------------
    → Σ ∣ M′ —→ Σ′ ∣ N′

  pure : ∀ {Σ}{M N : Term}
    → M —→ N
      ---------------
    → Σ ∣ M —→ Σ ∣ N

  new-ty : ∀{Σ}{N}
     → Σ ∣ ν N —→ suc Σ ∣ N [ ` Σ ]

pattern ξ F M—→N = ξξ F refl refl M—→N


{-------------      Type System    -------------}


{- Well-typed Coercions -}

gnd⇒ty : ∀{G} → Ground G → Type
gnd⇒ty {.nat} G-nat = Nat
gnd⇒ty {.★→★} G-fun = ★ ⇒ ★
gnd⇒ty {` α} G-var = ^ α

infix 1 _⊢_⦂_↝_
data _⊢_⦂_↝_ : TyEnv → Term → Type → Type → Set where

  wt-id : ∀{Γ}{A} → Γ ⊢ idᶜ ⦂ A ↝ A

  wt-inj : ∀{Γ}{G}
    → (g : Ground G)
    → Γ ⊢ G !! ⦂ gnd⇒ty g ↝ ★

  wt-proj : ∀{Γ}{G}
    → (g : Ground G)
    → Γ ⊢ G ?? ⦂ ★ ↝ gnd⇒ty g

  wt-seq : ∀{Γ}{A}{B}{C}{c}{d}
    → Γ ⊢ c ⦂ A ↝ B
    → Γ ⊢ d ⦂ B ↝ C
    → Γ ⊢ c ⍮ d ⦂ A ↝ C

  wt-fun : ∀{Γ}{A}{B}{A′}{B′}{c}{d}
    → Γ ⊢ c ⦂ A′ ↝ A
    → Γ ⊢ d ⦂ B ↝ B′
    → Γ ⊢ c ↪ d ⦂ (A ⇒ B) ↝ (A′ ⇒ B′)

  wt-seal : ∀{Γ}{α}{A}
    → Γ ∋ α ⦂ bnd A
    → Γ ⊢ ` α ↡ ⦂ A ↝ ^ α

  wt-unseal : ∀{Γ}{α}{A}
    → Γ ∋ α ⦂ bnd A
    → Γ ⊢ ` α ↟ ⦂ ^ α ↝ A

  wt-all : ∀{Γ}{c}{A}{B}
    → Γ ⊢ c ⦂ A ↝ B
    → Γ ⊢ ∀̰ c ⦂ ∀̇ A ↝ ∀̇ B
    
  wt-gen : ∀{Γ}{c}{A}{B}
    → Γ ⊢ c ⦂ A ↝ B
    → Γ ⊢ gen c ⦂ A ↝ ∀̇ B

  wt-inst : ∀{Γ}{c}{A}{B}
    → Γ ⊢ c ⦂ A ↝ B
    → Γ ⊢ inst c ⦂ ∀̇ A ↝ B

{- Well-typed Terms -}

infix 1 _⊢_⦂_
data _⊢_⦂_ : TyEnv → Term → Type → Set where

  ⊢-nat : ∀{Γ} → ∀ n
        -----------------
      → Γ ⊢ $ n ⦂ Nat

  ⊢-var : ∀{Γ}{x}{A}
      → Γ ∋ x ⦂ trm A
        ---------------
      → Γ ⊢ ` x ⦂ A

  ⊢-lam : ∀{Γ}{N}{A}{B}
     → Γ ⊢ A ok
     → trm A ∷ Γ ⊢ N ⦂ B
       -------------------
     → Γ ⊢ ƛ N ⦂ A ⇒ B
     
  ⊢-app : ∀{Γ}{L}{M}{A}{B}
     → Γ ⊢ L ⦂ A ⇒ B
     → Γ ⊢ M ⦂ A
       -----------------
     → Γ ⊢ L · M ⦂ B

  ⊢-tyabs : ∀{Γ}{V}{A}
     → Value V
     → typ ∷ Γ ⊢ V ⦂ A
       ---------------
     → Γ ⊢ Λ V ⦂ ∀̇ A

  ⊢-tyapp : ∀{Γ}{L}{A}{B}{α}
     → Γ ⊢ L ⦂ ∀̇ A
     → Γ ∋ α ⦂ bnd B
       ---------------------------
     → Γ ⊢ L 【 ` α 】 ⦂ A ⦗ ^ α ⦘

  ⊢-ν : ∀{Γ}{N}{A}{B}
     → bnd B ∷ Γ ⊢ N ⦂ ⟪ renᵗ suc ⟫ᵗ A
       -------------------------------
     → Γ ⊢ ν N ⦂ A

  ⊢-cast : ∀{Γ}{M}{c}{A}{B}
     → Γ ⊢ M ⦂ A
     → Γ ⊢ c ⦂ A ↝ B
       ---------------
     → Γ ⊢ M ⟨ c ⟩ ⦂ B

{- Well-formed Top-Level Type Environment -}

infix 1 _⊢_
data _⊢_ : ℕ → TyEnv → Set where
  empty-env : zero ⊢ []

  bnd-env : ∀{Γ}{α : ℕ}{A : Type}
     → α ⊢ Γ
     → suc α ⊢ bnd A ∷ Γ

{- Well-typed Configurations -}

infix 1 _⊢ᶜ_⦂_
data _⊢ᶜ_⦂_ : ℕ → Term → Type → Set where
   wtconfig : ∀{Σ}{Γ}{M}{A}
      → Σ ⊢ Γ
      → Γ ⊢ M ⦂ A
      → Σ ⊢ᶜ M ⦂ A

