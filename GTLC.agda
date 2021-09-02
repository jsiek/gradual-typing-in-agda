
module GTLC where

open import Syntax hiding (_∋_⦂_)
open import Types public
open import Variables public
open import Labels public
open import Data.List
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)


{-
  Syntax
-}

data Op : Set where
  op-lam : Type → Op
  op-app : Label → Op
  op-lit : ∀{A} → rep A → Prim A → Op
  op-if : Label → Op
  op-cons : Op
  op-fst : Label → Op
  op-snd : Label → Op
  op-inl : Type → Op
  op-inr : Type → Op
  op-case : Label → Type → Type → Op
  -- mutable reference
  op-ref : Op
  op-deref : Label → Op
  op-assign : Label → Op

sig : Op → List Sig
sig (op-lam A) = (ν ■) ∷ []
sig (op-app ℓ) = ■ ∷ ■ ∷ []
sig (op-lit r p) = []
sig (op-if ℓ) = ■ ∷ ■ ∷ ■ ∷ []
sig op-cons = ■ ∷ ■ ∷ []
sig (op-fst ℓ) = ■ ∷ []
sig (op-snd ℓ) = ■ ∷ []
sig (op-inl B) = ■ ∷ []
sig (op-inr A) = ■ ∷ []
sig (op-case ℓ A B) = ■ ∷ (ν ■) ∷ (ν ■) ∷ []
-- mutable reference
sig op-ref = ■ ∷ []
sig (op-deref ℓ) = ■ ∷ []
sig (op-assign ℓ) = ■ ∷ ■ ∷ []

open Syntax.OpSig Op sig
  renaming (ABT to Term) public

pattern ƛ_˙_ A N  = (op-lam A) ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_at_
pattern _·_at_ L M ℓ = (op-app ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern $_#_ r p = (op-lit r p) ⦅ nil ⦆

pattern if_then_else_at_ L M N ℓ = (op-if ℓ) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆

pattern ⟦_,_⟧ M N = op-cons ⦅ cons (ast M) (cons (ast N) nil) ⦆

pattern fst_at_ M ℓ = (op-fst ℓ) ⦅ cons (ast M) nil ⦆

pattern snd_at_ M ℓ = (op-snd ℓ) ⦅ cons (ast M) nil ⦆

pattern inl_other_ M B = (op-inl B) ⦅ cons (ast M) nil ⦆

pattern inr_other_ M A = (op-inr A) ⦅ cons (ast M) nil ⦆

pattern case_of_⇒_∣_⇒_at_ L A M B N ℓ = (op-case ℓ A B) ⦅ cons (ast L)
                                                               (cons (bind (ast M))
                                                               (cons (bind (ast N)) nil)) ⦆

pattern ref_ M = op-ref ⦅ cons (ast M) nil ⦆
pattern !_at_ M ℓ = (op-deref ℓ) ⦅ cons (ast M) nil ⦆
pattern _:=_at_ L M ℓ = (op-assign ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆

infix  4  _⊢G_⦂_
data _⊢G_⦂_ : Context → Term → Type → Set where

  ⊢var : ∀ {Γ A}{x : ℕ}
    → Γ ∋ x ⦂ A
      --------------
    → Γ ⊢G (` x) ⦂ A

  ⊢lam : ∀ {Γ A B}{N}
    → (Γ , A) ⊢G N ⦂ B
      -------------------
    → Γ ⊢G (ƛ A ˙ N) ⦂ A ⇒ B

  ⊢app : ∀ {Γ A A₁ A₂ B}{L M}{ℓ}
    → Γ ⊢G L ⦂ A
    → Γ ⊢G M ⦂ B
    → A ▹ A₁ ⇒ A₂
    → A₁ ~ B
      --------------------
    → Γ ⊢G L · M at ℓ ⦂ A₂

  ⊢lit : ∀ {Γ A}{r : rep A}{p : Prim A}
      ------------------
    → Γ ⊢G ($ r # p) ⦂ A

  ⊢if : ∀ {Γ}{A A' B : Type}{L M N}{ℓ}
    → Γ ⊢G L ⦂ B
    → Γ ⊢G M ⦂ A
    → Γ ⊢G N ⦂ A'
    → B ~ ` 𝔹
    → (aa : A ~ A')
      --------------------------------------
    → Γ ⊢G (if L then M else N at ℓ) ⦂ ⨆ aa

  ⊢cons : ∀ {Γ A B}{M N}
    → Γ ⊢G M ⦂ A  →  Γ ⊢G N ⦂ B
      -------------------------
    → Γ ⊢G ⟦ M , N ⟧ ⦂ A `× B

  ⊢fst : ∀ {Γ A A₁ A₂}{M}{ℓ}
    → Γ ⊢G M ⦂ A
    → A ▹ A₁ × A₂
      ---------------------
    → Γ ⊢G (fst M at ℓ) ⦂ A₁

  ⊢snd : ∀ {Γ A A₁ A₂}{M}{ℓ}
    → Γ ⊢G M ⦂ A
    → A ▹ A₁ × A₂
      ---------------------
    → Γ ⊢G (snd M at ℓ) ⦂ A₂

  ⊢inl : ∀ {Γ A B}{M}
    → Γ ⊢G M ⦂ A
      --------------------------
    → Γ ⊢G (inl M other B) ⦂ A `⊎ B

  ⊢inr : ∀ {Γ A B}{M}
    → Γ ⊢G M ⦂ B
      --------------------------
    → Γ ⊢G (inr M other A) ⦂ A `⊎ B

  ⊢case : ∀{Γ A B₁ B₂ C₁ C₂}{L M N}{ℓ}
    → Γ ⊢G L ⦂ A
    → (Γ , B₁) ⊢G M ⦂ B₂
    → (Γ , C₁) ⊢G N ⦂ C₂
    → A ~ (B₁ `⊎ C₁)
    → (bc : B₂ ~ C₂)
      -----------------------------------------
    → Γ ⊢G case L of B₁ ⇒ M ∣ C₁ ⇒ N at ℓ ⦂ ⨆ bc

  ⊢ref : ∀ {Γ A} {M}
    → Γ ⊢G M ⦂ A
      -------------------
    → Γ ⊢G ref M ⦂ Ref A

  ⊢deref : ∀ {Γ A A₁} {M} {ℓ}
    → Γ ⊢G M ⦂ A
    → A ▹Ref A₁
      -------------------
    → Γ ⊢G ! M at ℓ ⦂ A₁

  ⊢assign : ∀ {Γ A A' A₁} {L M} {ℓ}
    → Γ ⊢G L ⦂ A
    → Γ ⊢G M ⦂ A'
    → A ▹Ref A₁
    → A' ~ A₁
      ----------------------
    → Γ ⊢G L := M at ℓ ⦂ A


{-

Old version using intrinsic typing but not the ABT library.

The following is the traditional version of the type system
for the GTLC.

infix  4  _⊢G_
data _⊢G_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
      ---------------------------
    → Γ ⊢G A

  ƛ_˙_ : ∀ {Γ B}
    → (A : Type)
    → Γ , A ⊢G B
      -------------------
    → Γ ⊢G A ⇒ B

  _·_at_ : ∀ {Γ A A₁ A₂ B}
    → Γ ⊢G A
    → Γ ⊢G B
    → Label
    → {m : A ▹ A₁ ⇒ A₂}
    → {cn : A₁ ~ B}
      -------------------------
    → Γ ⊢G A₂

  $_ : ∀ {Γ A}
    → rep A
    → {p : Prim A}
      ------------------
    → Γ ⊢G A

  if : ∀ {Γ}{A A' B : Type}
    → Γ ⊢G B
    → Γ ⊢G A
    → Γ ⊢G A'
    → Label
    → {bb : B ~ ` 𝔹}
    → {aa : A ~ A'}
      --------------------------------------
    → Γ ⊢G ⨆ aa

  cons : ∀ {Γ A B}
    → Γ ⊢G A  →  Γ ⊢G B
      -----------------------
    → Γ ⊢G A `× B

  fst : ∀ {Γ A A₁ A₂}
    → Γ ⊢G A
    → Label
    → { m : A ▹ A₁ × A₂ }
      -------------------------
    → Γ ⊢G A₁

  snd : ∀ {Γ A A₁ A₂}
    → Γ ⊢G A
    → Label
    → { m : A ▹ A₁ × A₂ }
      -------------------------
    → Γ ⊢G A₂

  inl : ∀ {Γ A}
    → (B : Type)
    → Γ ⊢G A
      -----------------------
    → Γ ⊢G A `⊎ B

  inr : ∀ {Γ B}
    → (A : Type)
    → Γ ⊢G B
      -----------------------
    → Γ ⊢G A `⊎ B

  case : ∀{Γ A A₁ A₂ B₁ B₂ C₁ C₂}
    → Γ ⊢G A
    → Γ , B₁ ⊢G B₂
    → Γ , C₁ ⊢G C₂
    → Label
    → {ma : A ▹ A₁ ⊎ A₂ }
    → {ab : A₁ ~ B₁}
    → {ac : A₂ ~ C₁}
    → {bc : B₂ ~ C₂}
      ----------------------------------
    → Γ ⊢G ⨆ bc

-}

{- Examples -}
