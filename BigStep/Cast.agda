{-# OPTIONS --rewriting #-}
{-
   A simple blame calculus partly based on a version 
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
open import Sig
open import Var

module BigStep.Cast where

{- Base types -}

data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base

_≡$?_ : (ι : Base) → (ι′ : Base) → Dec (ι ≡ ι′)
′ℕ  ≡$? ′ℕ  =  yes refl
′ℕ  ≡$? ′𝔹  =  no (λ ())
′𝔹  ≡$? ′ℕ  =  no (λ ())
′𝔹  ≡$? ′𝔹  =  yes refl

{- Types -}

infixr 7 _⇒_
infix  8 $ₜ_

data Type : Set where
  ★ : Type
  $ₜ_ : (ι : Base) → Type
  _⇒_ : (A : Type) → (B : Type) → Type

{- Ground types -}

infix  8 $ᵍ_

data Ground : Set where
  $ᵍ_  :
       (ι : Base) 
       ----------
     → Ground

  ★⇒★ :
       ------
       Ground

gnd⇒ty : Ground → Type
gnd⇒ty ($ᵍ ι) = $ₜ ι
gnd⇒ty ★⇒★ = ★ ⇒ ★

_≡ᵍ_ : ∀ (G : Ground) (H : Ground) → Dec (G ≡ H)
($ᵍ ι) ≡ᵍ ($ᵍ ι′)
    with ι ≡$? ι′
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
($ᵍ ι) ≡ᵍ ★⇒★ = no λ ()
★⇒★ ≡ᵍ ($ᵍ ι) = no λ ()
★⇒★ ≡ᵍ ★⇒★ = yes refl

{----------------------- Type Precision ------------------------}

infixr 6 _⊑_
data _⊑_ : Type → Type → Set where

  unk⊑ : ∀{B} → ★ ⊑ B
  
  base⊑ : ∀{ι} → $ₜ ι ⊑ $ₜ ι

  fun⊑ : ∀{A B C D}
     → A ⊑ C
     → B ⊑ D
     → A ⇒ B ⊑ C ⇒ D

Refl⊑ : ∀{A} → A ⊑ A
Refl⊑ {★} = unk⊑
Refl⊑ {$ₜ ι} = base⊑
Refl⊑ {A ⇒ B} = fun⊑ Refl⊑ Refl⊑

Trans⊑ : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
Trans⊑ unk⊑ b = unk⊑
Trans⊑ base⊑ b = b
Trans⊑ (fun⊑ a a₁) (fun⊑ b b₁) = fun⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)

AntiSym⊑ : ∀ {A B} → A ⊑ B → B ⊑ A → A ≡ B
AntiSym⊑ unk⊑ unk⊑ = refl
AntiSym⊑ base⊑ base⊑ = refl
AntiSym⊑ {A ⇒ B}{A' ⇒ B'} (fun⊑ a a₁) (fun⊑ b b₁) =
  cong₂ (_⇒_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)

{------------------------ Terms --------------------------------}

data Lit : Set where
  Num : ℕ → Lit
  Bool : 𝔹 → Lit

typeof : Lit → Base
typeof (Num n) = ′ℕ
typeof (Bool b) = ′𝔹

data Op : Set where
  op-lam : Op
  op-app : Op
  op-lit : Lit → Op
  op-inject : Ground → Op
  op-project : Ground → Op
  op-blame : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit c) = []
sig (op-inject G) = ■ ∷ []
sig (op-project H) = ■ ∷ []
sig (op-blame) = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $ c = (op-lit c) ⦅ nil ⦆
pattern _⟨_!⟩ M G = (op-inject G) ⦅ cons (ast M) nil ⦆
pattern _⟨_?⟩ M H = (op-project H) ⦅ cons (ast M) nil ⦆
pattern blame = op-blame ⦅ nil ⦆

data Blame : Term → Set where
  isBlame : Blame blame

{--------------------- Values -----------------------------}

data Value : Term → Set where
  ƛ̬_ : (N : Term) → Value (ƛ N)
  $̬ : (c : Lit) → Value ($ c)
  _〈_〉 : ∀{V} → Value V → (G : Ground) → Value (V ⟨ G !⟩)

value : ∀ {V : Term}
  → (v : Value V)
    -------------
  → Term
value {V = V} v  =  V  

rename-val : ∀ {V : Term}
  → (ρ : Rename)
  → Value V
    ------------------
  → Value (rename ρ V)
rename-val ρ (ƛ̬ N)    =  ƛ̬ (rename (extr ρ) N)
rename-val ρ ($̬ c)    =  $̬ c
rename-val ρ (V 〈 g 〉)  =  (rename-val ρ V) 〈 g 〉

sub-val : ∀ {V}
  → (σ : Subst)
  → Value V
  → Value (⟪ σ ⟫ V)
sub-val σ (ƛ̬ N) = ƛ̬ ⟪ ext σ ⟫ N
sub-val σ ($̬ c) = $̬ c
sub-val σ (V 〈 g 〉)  =  (sub-val σ V) 〈 g 〉

{----------------- Type System ------------------------}

{- Consistency -}
data _∼_ : Type → Type → Set where
  ★∼ : ∀{A}
       -----
     → ★ ∼ A

  ∼★ : ∀{A}
       -----
     → A ∼ ★

  ∼-base : ∀{ι}
       --------------
     → ($ₜ ι) ∼ ($ₜ ι)

  ∼-fun : ∀{A B A′ B′}
     → A ∼ A′
     → B ∼ B′
       -------------------
     → (A ⇒ B) ∼ (A′ ⇒ B′)


infix 3 _⊢_⦂_

data _⊢_⦂_ : List Type → Term → Type → Set

data _⊢_⦂_ where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢$ : ∀ {Γ} (c : Lit)
      -------------------------
    → Γ ⊢ $ c ⦂ ($ₜ (typeof c))

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢ƛ : ∀ {Γ N A B}
    → (A ∷ Γ) ⊢ N ⦂ B
      -----------------
    → Γ ⊢ ƛ N ⦂ (A ⇒ B)

  ⊢⟨!⟩ : ∀{Γ M G}
    → Γ ⊢ M ⦂ gnd⇒ty G
      --------------------
    → Γ ⊢ M ⟨ G !⟩ ⦂ ★

  ⊢⟨?⟩ : ∀{Γ M}
    → Γ ⊢ M ⦂ ★
    → (H : Ground)
      -----------------------
    → Γ ⊢ M ⟨ H ?⟩ ⦂ gnd⇒ty H

  ⊢blame : ∀{Γ A}
      ---------------
    → Γ ⊢ blame ⦂ A


{----------------------- Term Precision ------------------------}

infix 3 _⊩_⊑_⦂_

Prec : Set
Prec = (∃[ A ] ∃[ B ] A ⊑ B)

data _⊩_⊑_⦂_ : List Prec → Term → Term → ∀{A B : Type} → A ⊑ B → Set 

data _⊩_⊑_⦂_ where

  ⊑-var : ∀ {Γ x A⊑B}
     → Γ ∋ x ⦂ A⊑B
       -------------------------------------
     → Γ ⊩ (` x) ⊑ (` x) ⦂ proj₂ (proj₂ A⊑B)

  ⊑-lit : ∀ {Γ c}
       -----------------------------------
     → Γ ⊩ ($ c) ⊑ ($ c) ⦂ base⊑{typeof c}

  ⊑-app : ∀{Γ L M L′ M′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → Γ ⊩ L ⊑ L′ ⦂ fun⊑ c d
     → Γ ⊩ M ⊑ M′ ⦂ c
       -----------------------
     → Γ ⊩ L · M ⊑ L′ · M′ ⦂ d

  ⊑-lam : ∀{Γ N N′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → (A , C , c) ∷ Γ ⊩ N ⊑ N′ ⦂ d
       ----------------------------
     → Γ ⊩ ƛ N ⊑ ƛ N′ ⦂ fun⊑ c d

  ⊑-inj-L : ∀{Γ M M′}{G B}{c : (gnd⇒ty G) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ c
       ---------------------------
     → Γ ⊩ M ⟨ G !⟩ ⊑ M′ ⦂ unk⊑{B}

  ⊑-inj-R : ∀{Γ M M′}{G}{c : ★ ⊑ (gnd⇒ty G)}
     → Γ ⊩ M ⊑ M′ ⦂ c
       ---------------------------
     → Γ ⊩ M ⊑ M′ ⟨ G !⟩ ⦂ unk⊑{★}

  ⊑-proj-L : ∀{Γ M M′ H B}{c : (gnd⇒ty H) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑{B}
       ---------------------
     → Γ ⊩ M ⟨ H ?⟩ ⊑ M′ ⦂ c

  ⊑-proj-R : ∀{Γ M M′ H}{c : ★ ⊑ (gnd⇒ty H)}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑{★}
       ---------------------
     → Γ ⊩ M ⊑ M′ ⟨ H ?⟩  ⦂ c

  ⊑-blame : ∀{Γ M A}
     → map proj₁ Γ ⊢ M ⦂ A
       ------------------------
     → Γ ⊩ M ⊑ blame ⦂ Refl⊑{A}

{----------------------- Frames ------------------------}


infix  6 □·_
infix  6 _·□
infix  6 □⟨_!⟩
infix  6 □⟨_?⟩

data Frame : Set where

  □·_ : 
      (M : Term)
      ----------
    → Frame

  _·□ : ∀ {V : Term}
    → (v : Value V)
      -------------
    → Frame

  □⟨_!⟩ : 
      (G : Ground)
      -----
    → Frame

  □⟨_?⟩ : 
      (H : Ground)
      -----
    → Frame

{- Plug an expression into a frame. -}

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
(□⟨ G !⟩) ⟦ M ⟧  =  M ⟨ G !⟩
(□⟨ H ?⟩) ⟦ M ⟧  =  M ⟨ H ?⟩

{- Possibly-empty Frame -}

data PEFrame : Set where
  `_ : Frame → PEFrame
  □ : PEFrame

_⦉_⦊ : PEFrame → Term → Term
(` F) ⦉ M ⦊ = F ⟦ M ⟧
□ ⦉ M ⦊ = M

{- Reduction -}

infix 2 _—→_
data _—→_ : Term → Term → Set where

  ξξ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ M ⟧
    → N′ ≡ F ⟦ N ⟧
    → M —→ N
      --------
    → M′ —→ N′

  ξξ-blame : ∀ {M′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ blame ⟧
      ------------------
    → M′ —→ blame

  β : ∀ {N : Term} {W : Term}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  collapse : ∀{G} {M V : Term}
    → Value V
    → M ≡ V ⟨ G !⟩
      ---------------------------
    → M ⟨ G ?⟩ —→ V

  collide  : ∀{G H} {M V : Term}
    → Value V
    → G ≢ H
    → M ≡ V ⟨ G !⟩
      ---------------------------------
    → M ⟨ H ?⟩ —→ blame

pattern ξ F M—→N = ξξ F refl refl M—→N
pattern ξ-blame F = ξξ-blame F refl

ξ′ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : PEFrame)
    → M′ ≡ F ⦉ M ⦊
    → N′ ≡ F ⦉ N ⦊
    → M —→ N
      --------
    → M′ —→ N′
ξ′ (` F) refl refl M→N = ξ F M→N
ξ′ □ refl refl M→N = M→N

ξ′-blame : ∀ {M′ : Term}
   → (F : PEFrame)
   → M′ ≡ F ⦉ blame ⦊
     ------------------------
   → M′ —→ blame ⊎ M′ ≡ blame
ξ′-blame (` F) refl = inj₁ (ξ-blame F)
ξ′-blame □ refl = inj₂ refl

ξ″-blame : ∀ {M′ : Term}
   → (F : PEFrame)
   → M′ ≡ F ⦉ blame ⦊
     ----------------------------------
   → M′ —→ blame ⊎ (M′ ≡ blame × F ≡ □)
ξ″-blame (` F) refl = inj₁ (ξ-blame F)
ξ″-blame □ refl = inj₂ (refl , refl)

{- Reflexive and transitive closure of reduction -}

infixr 1 _++_
--infix  1 begin_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
infix  3 _END

data _—↠_ : Term → Term → Set where
  _END : (M : Term)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : (L : Term) {M N : Term}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

--begin_ : ∀ {M N : Term} → (M —↠ N) → (M —↠ N)
--begin M—↠N = M—↠N

{- Convenience function to build a sequence of length one. -}

unit : ∀ {M N : Term} → (M —→ N) → (M —↠ N)
unit {M = M} {N = N} M—→N  =  M —→⟨ M—→N ⟩ (N END)


{- Apply ξ to each element of a sequence -}

ξ* : ∀ {M N : Term} → (F : Frame) → M —↠ N → F ⟦ M ⟧ —↠ F ⟦ N ⟧
ξ* F (M END) = F ⟦ M ⟧ END
ξ* F (L —→⟨ L—→M ⟩ M—↠N) = (F ⟦ L ⟧ —→⟨ ξ F L—→M ⟩ ξ* F M—↠N)

{- Concatenate two sequences. -}

_++_ : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
(M END) ++ M—↠N                =  M—↠N
(L —→⟨ L—→M ⟩ M—↠N) ++ N—↠P  =  L —→⟨ L—→M ⟩ (M—↠N ++ N—↠P)

{- Alternative notation for sequence concatenation. -}

_—↠⟨_⟩_ : (L : Term) {M N : Term}
  → L —↠ M
  → M —↠ N
    ---------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N  =  L—↠M ++ M—↠N

reducible : (M : Term) → Set
reducible M = ∃[ N ] (M —→ N)

irred : (M : Term) → Set
irred M = ¬ reducible M

len : ∀{M N : Term} → (M→N : M —↠ N) → ℕ
len (_ END) = 0
len (_ —→⟨ x ⟩ red) = suc (len red)

len-concat : ∀ {L}{M}{N} (s : L —↠ M) (r : M —↠ N)
  → len (s ++ r) ≡ len s + len r
len-concat (_ END) r = refl
len-concat (_ —→⟨ x ⟩ s) r rewrite len-concat s r = refl

diverge : Term → Set
diverge M = ∀ k → ∃[ N ] Σ[ r ∈ M —↠ N ] k ≡ len r

diverge⊎blame : Term → Set
diverge⊎blame M = ∀ k → ∃[ N ] Σ[ r ∈ M —↠ N ] ((k ≡ len r) ⊎ (N ≡ blame))

ToVal : Term → Set
ToVal M = ∃[ V ] (M —↠ V) × Value V

halt : Term → Set
halt M  = (M —↠ blame) ⊎ (ToVal M)

{- The Gradual Guarantee Property, aka. Error Ordering -}

⊨_⊑_ : Term → Term → Set
⊨ M ⊑ M′ =
     (ToVal M′ → ToVal M)
   × (diverge M′ → diverge M)
   × (ToVal M → ToVal M′ ⊎ M′ —↠ blame)
   × (diverge M → diverge⊎blame M′)



