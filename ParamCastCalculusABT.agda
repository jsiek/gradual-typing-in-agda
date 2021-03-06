open import Types

{-

Here we define the Cast Calculus in a way that parameterizes over the
actual casts, to enable succinct definitions and proofs of type safety
for many different cast calculi.  The Agda type constructor for
representing casts is given by the module parameter named Cast.  The
Type argument to Cast is typically a function type whose domain is the
source of the cast and whose codomain is the target type of the
cast. However, in cast calculi with fancy types such as intersections,
the type of a cast may not literally be a function type.

-}
module ParamCastCalculusABT (Cast : Type → Set) where

open import Variables
open import Labels
open import Data.Nat
open import Data.Bool hiding (if_then_else_)
open import Data.List
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Syntax hiding (_∋_⦂_; _,_)

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
sig (op-blame ℓ) = []

open Syntax.OpSig Op sig renaming (ABT to Term) public

infixl 7  _·_
infix  8 _⟨_⟩

pattern ƛ_˙_ A N = (op-lam A) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_#_ r p = (op-lit r p) ⦅ nil ⦆
pattern if_then_else_ L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern ⟦_,_⟧ M N = op-cons ⦅ cons (ast M) (cons (ast N) nil) ⦆
pattern fst_ M = op-fst ⦅ cons (ast M) nil ⦆
pattern snd_ M = op-snd ⦅ cons (ast M) nil ⦆
pattern inl_other_ M B = (op-inl B) ⦅ cons (ast M) nil ⦆
pattern inr_other_ M A = (op-inr A) ⦅ cons (ast M) nil ⦆
pattern case_of_⇒_∣_⇒_ L A M B N =
  (op-case A B) ⦅ cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil)) ⦆
pattern _⟨_⟩ M c = (op-cast c) ⦅ cons (ast M) nil ⦆
pattern blame_ ℓ = (op-blame ℓ) ⦅ nil ⦆

-- May need to put this into `Variables` at some point. - Tianyu
data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      -------------
    → (Γ , A) ∋ 0 ⦂ A

  S_ : ∀ {Γ A B n}
    → Γ ∋ n ⦂ A
      -----------------
    → (Γ , B) ∋ suc n ⦂ A

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢var : ∀ {Γ A} {x : ℕ}
    → Γ ∋ x ⦂ A
      --------------
    → Γ ⊢ ` x ⦂ A

  ⊢lam : ∀ {Γ A B} {N}
    → Γ , A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ A ˙ N ⦂ A ⇒ B

  ⊢app : ∀ {Γ A B} {L M}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      --------------------
    → Γ ⊢ L · M ⦂ B

  ⊢lit : ∀ {Γ A} {r : rep A} {p : Prim A}
      ------------------
    → Γ ⊢ $ r # p ⦂ A

  ⊢if : ∀ {Γ A} {L M N}
    → Γ ⊢ L ⦂ ` 𝔹
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ A
      --------------------------------------
    → Γ ⊢ if L then M else N ⦂ A

  ⊢cons : ∀ {Γ A B} {M N}
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ B
      -------------------------
    → Γ ⊢ ⟦ M , N ⟧ ⦂ A `× B

  ⊢fst : ∀ {Γ A B} {M}
    → Γ ⊢ M ⦂ A `× B
      ---------------------
    → Γ ⊢ fst M ⦂ A

  ⊢snd : ∀ {Γ A B} {M}
    → Γ ⊢ M ⦂ A `× B
      ---------------------
    → Γ ⊢ snd M ⦂ B

  ⊢inl : ∀ {Γ A B} {M}
    → Γ ⊢ M ⦂ A
      --------------------------
    → Γ ⊢ inl M other B ⦂ A `⊎ B

  ⊢inr : ∀ {Γ A B} {M}
    → Γ ⊢ M ⦂ B
      --------------------------
    → Γ ⊢ inr M other A ⦂ A `⊎ B

  ⊢case : ∀ {Γ A B C} {L M N}
    → Γ ⊢ L ⦂ A `⊎ B
    → Γ , A ⊢ M ⦂ C
    → Γ , B ⊢ N ⦂ C
      -----------------------------------------
    → Γ ⊢ case L of A ⇒ M ∣ B ⇒ N ⦂ C

  ⊢cast : ∀ {Γ A B} {M}
    → Γ ⊢ M ⦂ A
    → (c : Cast (A ⇒ B))
      --------------------
    → Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {Γ A} {ℓ}
      -----------------
    → Γ ⊢ blame ℓ ⦂ A
