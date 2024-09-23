{-# OPTIONS --rewriting #-}

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

module NewType.CastCalculus where

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
  `_ : Var → Type

{------------------------ Terms --------------------------------}

infixl 7  _·_

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
  op-inject : Op
  op-project : Op
  op-blame : Op
  op-new : Op
  op-base : Base → Op
  op-fun : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit c) = []
sig op-inject = ■ ∷ ■ ∷ []
sig op-project = ■ ∷ ■ ∷ []
sig op-blame = []
sig op-new = (ν ■) ∷ []
sig (op-base ι) = []
sig op-fun = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $ c = (op-lit c) ⦅ nil ⦆
pattern _⟨_!⟩ M G = op-inject ⦅ cons (ast M) (cons (ast G) nil) ⦆
pattern _⟨_?⟩ M H = op-project ⦅ cons (ast M) (cons (ast H) nil) ⦆
pattern blame = op-blame ⦅ nil ⦆
pattern $ᵍ_ ι = (op-base ι) ⦅ nil ⦆
pattern ★⇒★ = op-fun ⦅ nil ⦆
pattern Ν_ M = op-new ⦅ cons (bind (ast M)) nil ⦆

{----- Ground Types ---}

data Ground : Term → Set where
  gnd-base : (ι : Base) → Ground ($ᵍ ι)
  gnd-fun : Ground ★⇒★
  gnd-var : (x : Var) → Ground (` x)


gnd : ∀{G} → Ground G → Term
gnd {G} g = G

{-
gnd⇒ty : ∀{G} → Ground G → Type
gnd⇒ty (gnd-base ι) = $ₜ ι
gnd⇒ty gnd-fun = ★ ⇒ ★
gnd⇒ty (gnd-var α) = ` α
-}

{--------------------- Values -----------------------------}

data Value : Term → Set where
  ƛ̬_ : (N : Term) → Value (ƛ N)
  $̬ : (c : Lit) → Value ($ c)
  _〈_〉 : ∀{V G} → Value V → Ground G → Value (V ⟨ G !⟩)

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
rename-val ρ (_〈_〉 {V}{G} v g) =  (rename-val ρ v) 〈 rG g 〉
  where
  rG : ∀{G} → Ground G → Ground (rename ρ G)
  rG {.($ᵍ ι)} (gnd-base ι) = gnd-base ι
  rG {.★⇒★} gnd-fun = gnd-fun
  rG {.(` x)} (gnd-var x) = gnd-var (ρ x)

{-  The following is not true.
sub-val : ∀ {V}
  → (σ : Subst)
  → Value V
  → Value (⟪ σ ⟫ V)
sub-val σ (ƛ̬ N) = ƛ̬ ⟪ ext σ ⟫ N
sub-val σ ($̬ c) = $̬ c
sub-val σ (V 〈 g 〉)  =  (sub-val σ V) 〈 {!!} 〉
-}

{----------------- Type System ------------------------}

infix 3 _⊢ᵍ_≐_
data _⊢ᵍ_≐_ : List Type → {G : Term} → Ground G → Type → Set where
  ⊢ᵍbase : ∀{Γ ι}
    → Γ ⊢ᵍ gnd-base ι ≐ $ₜ ι
  ⊢ᵍfun : ∀ {Γ}
    → Γ ⊢ᵍ gnd-fun ≐ ★ ⇒ ★
  ⊢ᵍvar : ∀ {Γ α A}
    → Γ ∋ α ⦂ A
      ------------------
    → Γ ⊢ᵍ gnd-var α ≐ A

infix 3 _⊢_⦂_

data _⊢_⦂_ : List Type → Term → Type → Set where

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

  ⊢⟨!⟩ : ∀{Γ M G A}
    → (g : Ground G)
    → Γ ⊢ᵍ g ≐ A
    → Γ ⊢ M ⦂ A
      --------------------
    → Γ ⊢ M ⟨ G !⟩ ⦂ ★

  ⊢⟨?⟩ : ∀{Γ M H A}
    → (h : Ground H)
    → Γ ⊢ M ⦂ ★
    → Γ ⊢ᵍ h ≐ A
      ----------------
    → Γ ⊢ M ⟨ H ?⟩ ⦂ A

  ⊢blame : ∀{Γ A}
      ---------------
    → Γ ⊢ blame ⦂ A

  ⊢Ν : ∀ {Γ M A B}
    → (A ∷ Γ) ⊢ M ⦂ B
      -----------------
    → Γ ⊢ Ν M ⦂ B

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

  □⟨_!⟩ : ∀ {G}
    → Ground G
      --------
    → Frame

  □⟨_?⟩ : ∀ {H}
    → Ground H
      --------
    → Frame

  Ν□ : Frame

{- Plug an expression into a frame. -}

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧     =  L · M
(v ·□) ⟦ M ⟧     =  value v · M
(□⟨ g !⟩) ⟦ M ⟧  =  M ⟨ gnd g !⟩
(□⟨ h ?⟩) ⟦ M ⟧  =  M ⟨ gnd h ?⟩
Ν□  ⟦ M ⟧        =  Ν M

{- Possibly-empty Frame -}

data PEFrame : Set where
  `_ : Frame → PEFrame
  □ : PEFrame

_⦉_⦊ : PEFrame → Term → Term
(` F) ⦉ M ⦊ = F ⟦ M ⟧
□ ⦉ M ⦊ = M

{- Reduction -}

infix 2 _⟶_
data _⟶_ : Term → Term → Set where

  ξξ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ M ⟧
    → N′ ≡ F ⟦ N ⟧
    → M ⟶ N
      --------
    → M′ ⟶ N′

  ξξ-blame : ∀ {M′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ blame ⟧
      ------------------
    → M′ ⟶ blame

  β : ∀ {N : Term} {W : Term}
    → Value W
      --------------------
    → (ƛ N) · W ⟶ N [ W ]

  collapse : ∀{G} {M V : Term}
    → Value V
    → M ≡ V ⟨ G !⟩
      ---------------------------
    → M ⟨ G ?⟩ ⟶ V

  collide  : ∀{G H} {M V : Term}
    → Value V
    → G ≢ H
    → M ≡ V ⟨ G !⟩
      ---------------------------------
    → M ⟨ H ?⟩ ⟶ blame

  newtype : ∀ {V : Term}
    → Value V
    → Ν V ⟶ V

pattern ξ F M⟶N = ξξ F refl refl M⟶N
pattern ξ-blame F = ξξ-blame F refl

ξ′ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : PEFrame)
    → M′ ≡ F ⦉ M ⦊
    → N′ ≡ F ⦉ N ⦊
    → M ⟶ N
      --------
    → M′ ⟶ N′
ξ′ (` F) refl refl M→N = ξ F M→N
ξ′ □ refl refl M→N = M→N

ξ′-blame : ∀ {M′ : Term}
   → (F : PEFrame)
   → M′ ≡ F ⦉ blame ⦊
     ------------------------
   → M′ ⟶ blame ⊎ M′ ≡ blame
ξ′-blame (` F) refl = inj₁ (ξ-blame F)
ξ′-blame □ refl = inj₂ refl

ξ″-blame : ∀ {M′ : Term}
   → (F : PEFrame)
   → M′ ≡ F ⦉ blame ⦊
     ----------------------------------
   → M′ ⟶ blame ⊎ (M′ ≡ blame × F ≡ □)
ξ″-blame (` F) refl = inj₁ (ξ-blame F)
ξ″-blame □ refl = inj₂ (refl , refl)

{- Reflexive and transitive closure of reduction -}

infixr 1 _++_
--infix  1 begin_
infix  2 _↠_
infixr 2 _⟶⟨_⟩_
infixr 2 _↠⟨_⟩_
infix  3 _END

data _↠_ : Term → Term → Set where
  _END : (M : Term)
      ---------
    → M ↠ M

  _⟶⟨_⟩_ : (L : Term) {M N : Term}
    → L ⟶ M
    → M ↠ N
      ---------
    → L ↠ N

{- Convenience function to build a sequence of length one. -}

unit : ∀ {M N : Term} → (M ⟶ N) → (M ↠ N)
unit {M = M} {N = N} M⟶N  =  M ⟶⟨ M⟶N ⟩ (N END)


{- Apply ξ to each element of a sequence -}

ξ* : ∀ {M N : Term} → (F : Frame) → M ↠ N → F ⟦ M ⟧ ↠ F ⟦ N ⟧
ξ* F (M END) = F ⟦ M ⟧ END
ξ* F (L ⟶⟨ L⟶M ⟩ M↠N) = (F ⟦ L ⟧ ⟶⟨ ξ F L⟶M ⟩ ξ* F M↠N)

ξ′* : ∀{M N} → (F : PEFrame) → M ↠ N → F ⦉ M ⦊ ↠ F ⦉ N ⦊
ξ′* {M} {N} (` F) M→N = ξ* F M→N
ξ′* {M} {N} □ M→N = M→N

{- Concatenate two sequences. -}

_++_ : ∀ {L M N : Term} → L ↠ M → M ↠ N → L ↠ N
(M END) ++ M↠N                =  M↠N
(L ⟶⟨ L⟶M ⟩ M↠N) ++ N↠P  =  L ⟶⟨ L⟶M ⟩ (M↠N ++ N↠P)

ξ-blame₃ : ∀ {M}{M′ : Term}
   → (F : PEFrame)
   → M ↠ blame
   → M′ ≡ F ⦉ M ⦊
     -----------
   → M′ ↠ blame
ξ-blame₃ (` F) M→b refl = (ξ* F M→b) ++ unit (ξ-blame F)
ξ-blame₃ □ M→b refl = M→b

{- Alternative notation for sequence concatenation. -}

_↠⟨_⟩_ : (L : Term) {M N : Term}
  → L ↠ M
  → M ↠ N
    ---------
  → L ↠ N
L ↠⟨ L↠M ⟩ M↠N  =  L↠M ++ M↠N

reducible : (M : Term) → Set
reducible M = ∃[ N ] (M ⟶ N)

irred : (M : Term) → Set
irred M = ¬ reducible M

len : ∀{M N : Term} → (M→N : M ↠ N) → ℕ
len (_ END) = 0
len (_ ⟶⟨ x ⟩ red) = suc (len red)

len-concat : ∀ {L}{M}{N} (s : L ↠ M) (r : M ↠ N)
  → len (s ++ r) ≡ len s + len r
len-concat (_ END) r = refl
len-concat (_ ⟶⟨ x ⟩ s) r rewrite len-concat s r = refl

_⇓ : Term → Set
M ⇓ = ∃[ V ] (M ↠ V) × Value V

_⇑ : Term → Set
M ⇑ = ∀ k → ∃[ N ] Σ[ r ∈ M ↠ N ] k ≡ len r

halt : Term → Set
halt M  = (M ↠ blame) ⊎ (M ⇓)
