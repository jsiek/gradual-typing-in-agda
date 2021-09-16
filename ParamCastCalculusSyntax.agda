open import Data.Unit using (⊤) renaming (tt to unit)
open import Data.List
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; cong-app)

open import Types
open import Labels
open import PreCastStructure

open import Syntax

module ParamCastCalculusSyntax (pcs : PreCastStruct) where

open PreCastStruct pcs using (Cast; Inert)

{-
  We define well-typed expressions with the following typing judgment.
  Compared to the STLC, there are two important new features.
  The cast is written M ⟨ c ⟩, where M is an expression and c
  is a cast (whatever that may be). We also have blame ℓ for
  raising uncatchable exceptions.
-}

-- Syntax
data Op : Set where
  op-lam : Type → Op
  op-app : Op
  op-lit : ∀ {A} → rep A → Prim A → Op
  op-if : Op
  op-cons : Op
  op-fst : Op
  op-snd : Op
  op-inl : Type → Op
  op-inr : Type → Op
  op-case : Type → Type → Op
  op-cast : ∀ {A B} → Cast (A ⇒ B) → Op
  op-wrap : ∀ {A B} → (c : Cast (A ⇒ B)) → Inert c → Op
  op-blame : Label → Op

sig : Op → List Sig
sig (op-lam A) = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit r p) = []
sig op-if = ■ ∷ ■ ∷ ■ ∷ []
sig op-cons = ■ ∷ ■ ∷ []
sig op-fst = ■ ∷ []
sig op-snd = ■ ∷ []
sig (op-inl B) = ■ ∷ []
sig (op-inr A) = ■ ∷ []
sig (op-case A B) = ■ ∷ (ν ■) ∷ (ν ■) ∷ []
sig (op-cast c) = ■ ∷ []
sig (op-wrap c i) = ■ ∷ []
sig (op-blame ℓ) = []

open Syntax.OpSig Op sig
  renaming (ABT to Term)
  hiding (plug)  -- we'll implement `plug` for frame
  public

infixl 7  _·_
infix  8 _⟨_⟩
{-
  We use this to express "term *wrapped* with inert cast".
  Corresponds to `_⟪_⟫` in `ParamCastCalculus`. The later
  creates visual confusion with the ABT library.
-}
infix  9 _⟨_₍_₎⟩

pattern ƛ_˙_ A N = (op-lam A) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_#_ r p = (op-lit r p) ⦅ nil ⦆
pattern if_then_else_endif L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern ⟦_,_⟧ M N = op-cons ⦅ cons (ast M) (cons (ast N) nil) ⦆
pattern fst_ M = op-fst ⦅ cons (ast M) nil ⦆
pattern snd_ M = op-snd ⦅ cons (ast M) nil ⦆
pattern inl_other_ M B = (op-inl B) ⦅ cons (ast M) nil ⦆
pattern inr_other_ M A = (op-inr A) ⦅ cons (ast M) nil ⦆
pattern case_of_⇒_∣_⇒_ L A M B N =
  (op-case A B) ⦅ cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil)) ⦆
pattern _⟨_⟩ M c = (op-cast c) ⦅ cons (ast M) nil ⦆
pattern _⟨_₍_₎⟩ M c i = (op-wrap c i) ⦅ cons (ast M) nil ⦆
pattern blame_ ℓ = (op-blame ℓ) ⦅ nil ⦆
