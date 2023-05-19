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
open import Var

module Poly.CastCalculus where

{-------------      Types    -------------}


data TypeOp : Set where
  op-fun : TypeOp
  op-all : TypeOp
  op-nat : TypeOp
  op-unk : TypeOp

type-sig : TypeOp → List Sig
type-sig op-fun = ■ ∷ ■ ∷ []
type-sig op-all = (nu ■) ∷ []
type-sig op-nat = []
type-sig op-unk = []

open import rewriting.AbstractBindingTree TypeOp type-sig
  using ()
  renaming (ABT to Type; Rename to Renameᵗ; Subst to Substᵗ;
            ren to renᵗ; ren-def to ren-defᵗ; extr to extrᵗ; ext to extᵗ;
            ⟪_⟫ to ⟪_⟫ᵗ; sub-var to sub-varᵗ; seq-def to seq-defᵗ; ↑ to ↑ᵗ;
            _[_] to _⦗_⦘; _⦅_⦆ to _‹_›; _•_ to _•ᵗ_; id to idᵗ; _⨟_ to _⨟ᵗ_;
            nil to tnil; cons to tcons; bind to tbind; ast to tast; `_ to ^_)
  public

pattern Nat = op-nat ‹ tnil ›
pattern ★ = op-unk ‹ tnil ›

infixl 7  _⇒_
pattern _⇒_ A B = op-fun ‹ tcons (tast A) (tcons (tast B) tnil) ›

pattern ∀̇ A = op-all ‹ tcons (tbind (tast A)) tnil ›

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
pattern _⟨_⟩ L c = op-tyapp ⦅ cons (ast L) (cons (ast c) nil) ⦆
pattern blame = op-blame ⦅ nil ⦆
pattern ν N  = op-nu ⦅ cons (bind (ast N)) nil ⦆
pattern idᶜ = c-id ⦅ nil ⦆
pattern _!! G = c-inject ⦅ cons (ast G) nil ⦆
pattern _?? G = c-project ⦅ cons (ast G) nil ⦆
pattern _↓ α = c-seal ⦅ cons (ast α) nil ⦆
pattern _↑ α = c-unseal ⦅ cons (ast α) nil ⦆
pattern _↪_ c d = c-fun ⦅ cons (ast c) (cons (ast d) nil) ⦆
pattern _⍮_ c d = c-seq ⦅ cons (ast c) (cons (ast d) nil) ⦆
pattern ∀̰ c = c-all ⦅ cons (bind (ast c)) nil ⦆
pattern inst c = c-inst ⦅ cons (bind (ast c)) nil ⦆
pattern gen c = c-gen ⦅ cons (bind (ast c)) nil ⦆
pattern nat = g-nat ⦅ nil ⦆
pattern ★→★ = g-fun ⦅ nil ⦆

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

  ξξ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ M ⟧
    → N′ ≡ F ⟦ N ⟧
    → M —→ N
      --------
    → M′ —→ N′

  β-ƛ : ∀ {N W : Term}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {N : Term}{α : Var}
      ---------------------------
    → (Λ N) 【 ` α 】 —→ N [ ` α ]

pattern ξ F M—→N = ξξ F refl refl M—→N
