open import Types
open import PreCastStructure

open import Syntax

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
module ParamCastCalculusABT (pcs : PreCastStruct) where

open import Labels
open import Data.Nat
open import Data.Unit using (⊤) renaming (tt to unit)
open import Data.Bool
open import Data.List
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

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


infix  4  _⊢_⦂_
-- data _⊢_⦂_ : Context → Term → Type → Set where
𝑉 : List Type → Var → Type → Type → Set
𝑃 : (op : Op) → Vec Type (length (sig op)) → BTypes Type (sig op) → Type → Set

open import ABTPredicate Op sig 𝑉 𝑃 public renaming (_⊢_⦂_ to predicate)
_⊢_⦂_ = predicate

--   ⊢var : ∀ {Γ A} {x : ℕ}
--     → Γ ∋ x ⦂ A
--       --------------
--     → Γ ⊢ ` x ⦂ A
𝑉 Γ x A B = A ≡ B

--   ⊢lam : ∀ {Γ A B} {N}
--     → Γ , A ⊢ N ⦂ B
--       -------------------
--     → Γ ⊢ ƛ A ˙ N ⦂ A ⇒ B
𝑃 (op-lam A₁) (B ∷ᵥ []ᵥ) ⟨ ⟨ A , tt ⟩ , tt ⟩ C =
  C ≡ A ⇒ B × A ≡ A₁

--   ⊢app : ∀ {Γ A B} {L M}
--     → Γ ⊢ L ⦂ A ⇒ B
--     → Γ ⊢ M ⦂ A
--       --------------------
--     → Γ ⊢ L · M ⦂ B
𝑃 op-app (C ∷ᵥ A ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , tt ⟩ ⟩ B =
  C ≡ A ⇒ B

--   ⊢lit : ∀ {Γ A} {r : rep A} {p : Prim A}
--       ------------------
--     → Γ ⊢ $ r # p ⦂ A
𝑃 (op-lit {A₁} r p) []ᵥ tt A = A ≡ A₁

--   ⊢if : ∀ {Γ A} {L M N}
--     → Γ ⊢ L ⦂ ` 𝔹
--     → Γ ⊢ M ⦂ A
--     → Γ ⊢ N ⦂ A
--       --------------------------------------
--     → Γ ⊢ if L then M else N endif ⦂ A
𝑃 op-if (B ∷ᵥ A₁ ∷ᵥ A₂ ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , ⟨ tt , tt ⟩ ⟩ ⟩ A =
  (A ≡ A₁ × A₁ ≡ A₂) × B ≡ ` 𝔹

--   ⊢cons : ∀ {Γ A B} {M N}
--     → Γ ⊢ M ⦂ A
--     → Γ ⊢ N ⦂ B
--       -------------------------
--     → Γ ⊢ ⟦ M , N ⟧ ⦂ A `× B
𝑃 op-cons (A ∷ᵥ B ∷ᵥ []ᵥ) ⟨ tt , ⟨ tt , tt ⟩ ⟩ C = C ≡ A `× B

--   ⊢fst : ∀ {Γ A B} {M}
--     → Γ ⊢ M ⦂ A `× B
--       ---------------------
--     → Γ ⊢ fst M ⦂ A
𝑃 op-fst (C ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ A = ∃[ B ] C ≡ A `× B

--   ⊢snd : ∀ {Γ A B} {M}
--     → Γ ⊢ M ⦂ A `× B
--       ---------------------
--     → Γ ⊢ snd M ⦂ B
𝑃 op-snd (C ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ B = ∃[ A ] C ≡ A `× B

--   ⊢inl : ∀ {Γ A B} {M}
--     → Γ ⊢ M ⦂ A
--       --------------------------
--     → Γ ⊢ inl M other B ⦂ A `⊎ B
𝑃 (op-inl B) (A ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ C = C ≡ A `⊎ B

--   ⊢inr : ∀ {Γ A B} {M}
--     → Γ ⊢ M ⦂ B
--       --------------------------
--     → Γ ⊢ inr M other A ⦂ A `⊎ B
𝑃 (op-inr A) (B ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ C = C ≡ A `⊎ B

--   ⊢case : ∀ {Γ A B C} {L M N}
--     → Γ ⊢ L ⦂ A `⊎ B
--     → Γ , A ⊢ M ⦂ C
--     → Γ , B ⊢ N ⦂ C
--       -----------------------------------------
--     → Γ ⊢ case L of A ⇒ M ∣ B ⇒ N ⦂ C
𝑃 (op-case A₁ B₁) (X ∷ᵥ C₁ ∷ᵥ C₂ ∷ᵥ []ᵥ) ⟨ tt , ⟨ ⟨ A , tt ⟩ , ⟨ ⟨ B , tt ⟩ , tt ⟩ ⟩ ⟩ C =
  (C ≡ C₁ × C₁ ≡ C₂) × (X ≡ A `⊎ B × A ≡ A₁ × B ≡ B₁)

--   ⊢cast : ∀ {Γ A B} {M}
--     → Γ ⊢ M ⦂ A
--     → (c : Cast (A ⇒ B))
--       --------------------
--     → Γ ⊢ M ⟨ c ⟩ ⦂ B
𝑃 (op-cast {A₁} {B₁} c) (A ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ B = A ≡ A₁ × B ≡ B₁

--   ⊢wrap : ∀ {Γ A B} {M}
--     → Γ ⊢ M ⦂ A
--     → (c : Cast (A ⇒ B))
--     → (i : Inert c)
--       ---------------------
--     → Γ ⊢ M ⟨ c ₍ i ₎⟩ ⦂ B
𝑃 (op-wrap {A₁} {B₁} c i) (A ∷ᵥ []ᵥ) ⟨ tt , tt ⟩ B = A ≡ A₁ × B ≡ B₁

--   ⊢blame : ∀ {Γ A} {ℓ}
--       -----------------
--     → Γ ⊢ blame ℓ ⦂ A
𝑃 (op-blame _) []ᵥ tt A = ⊤

{- Create the typing rules. -}
pattern ⊢` ∋x = var-p ∋x refl

pattern ⊢ƛ A ⊢N eq = op-p {op = op-lam A} (cons-p (bind-p (ast-p ⊢N)) nil-p) eq
pattern ⊢ƛ-refl A ⊢N = ⊢ƛ A ⊢N (⟨ refl , refl ⟩)

pattern ⊢· ⊢L ⊢M eq = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq
pattern ⊢·-refl ⊢L ⊢M = ⊢· ⊢L ⊢M refl

pattern ⊢$ r p eq = op-p {op = op-lit r p} nil-p eq
pattern ⊢$-refl r p = ⊢$ r p refl

pattern ⊢if ⊢L ⊢M ⊢N eq = op-p {op = op-if}
                               (cons-p (ast-p ⊢L)
                                       (cons-p (ast-p ⊢M)
                                               (cons-p (ast-p ⊢N) nil-p))) eq
pattern ⊢if-refl ⊢L ⊢M ⊢N = ⊢if ⊢L ⊢M ⊢N (⟨ ⟨ refl , refl ⟩ , refl ⟩)

pattern ⊢cons ⊢M ⊢N eq = op-p {op = op-cons}
                           (cons-p (ast-p ⊢M) (cons-p (ast-p ⊢N) nil-p)) eq
pattern ⊢cons-refl ⊢M ⊢N = ⊢cons ⊢M ⊢N refl

pattern ⊢fst ⊢M eq = op-p {op = op-fst} (cons-p (ast-p ⊢M) nil-p) eq
pattern ⊢fst-refl ⊢M = ⊢fst ⊢M (⟨ _ , refl ⟩)

pattern ⊢snd ⊢M eq = op-p {op = op-snd} (cons-p (ast-p ⊢M) nil-p) eq
pattern ⊢snd-refl ⊢M = ⊢snd ⊢M (⟨ _ , refl ⟩)

pattern ⊢inl B ⊢M eq = op-p {op = op-inl B} (cons-p (ast-p ⊢M) nil-p) eq
pattern ⊢inl-refl B ⊢M = ⊢inl B ⊢M refl

pattern ⊢inr A ⊢M eq = op-p {op = op-inr A} (cons-p (ast-p ⊢M) nil-p) eq
pattern ⊢inr-refl A ⊢M = ⊢inr A ⊢M refl

pattern ⊢case A B ⊢L ⊢M ⊢N eq = op-p {op = op-case A B}
                                     (cons-p (ast-p ⊢L)
                                             (cons-p (bind-p (ast-p ⊢M))
                                                     (cons-p (bind-p (ast-p ⊢N)) nil-p))) eq
pattern ⊢case-refl A B ⊢L ⊢M ⊢N = ⊢case A B ⊢L ⊢M ⊢N (⟨ ⟨ refl , refl ⟩ , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩)

pattern ⊢cast c ⊢M eq = op-p {op = op-cast c} (cons-p (ast-p ⊢M) nil-p) eq
pattern ⊢cast-refl c ⊢M = ⊢cast c ⊢M (⟨ refl , refl ⟩)

pattern ⊢wrap c i ⊢M eq = op-p {op = op-wrap c i} (cons-p (ast-p ⊢M) nil-p) eq
pattern ⊢wrap-refl c i ⊢M = ⊢wrap c i ⊢M (⟨ refl , refl ⟩)

pattern ⊢blame ℓ eq = op-p {op = op-blame ℓ} nil-p eq
pattern ⊢blame-refl ℓ = ⊢blame ℓ unit
