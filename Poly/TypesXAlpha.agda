{-# OPTIONS --rewriting #-}
{-
   A polymorphic blame calculus partly based on a version 
   by Jeremy, Phil Wadler, and Peter Thiemann.
-}

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (map-++-commute; map-compose)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
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
open import Poly.SetsAsPredicates

module Poly.TypesXAlpha where

{-------------      Types    -------------}


data TypeOp : Set where
  op-fun : TypeOp
  op-all : TypeOp
  op-nat : TypeOp
  op-unk : TypeOp
  op-var : TypeOp 

type-sig : TypeOp → List Sig
type-sig op-fun = ■ ∷ ■ ∷ []
type-sig op-all = (nu ■) ∷ []
type-sig op-nat = []
type-sig op-unk = []
type-sig op-var = ■ ∷ []

open import rewriting.AbstractBindingTree TypeOp type-sig
  using (FV; FV-suc-0)
  renaming (ABT to Type; Rename to Renameᵗ; rename to renameᵗ; Subst to Substᵗ;
            ren to renᵗ; ren-def to ren-defᵗ; extr to extrᵗ; ext to extᵗ;
            ⟪_⟫ to ⟪_⟫ᵗ; sub-var to sub-varᵗ; seq-def to seq-defᵗ; ↑ to ↑ᵗ;
            _[_] to _⦗_⦘; _⦅_⦆ to _‹_›; _•_ to _•ᵗ_; id to idᵗ; _⨟_ to _⨟ᵗ_;
            nil to tnil; cons to tcons; bind to tbind; ast to tast; `_ to ^_;
            FV-ren to FV-renᵗ; FV-ren-fwd to FV-ren-fwdᵗ)
  public

pattern Nat = op-nat ‹ tnil ›
pattern ★ = op-unk ‹ tnil ›

infixl 7  _⇒_
pattern _⇒_ A B = op-fun ‹ tcons (tast A) (tcons (tast B) tnil) ›

pattern ∀̇ A = op-all ‹ tcons (tbind (tast A)) tnil ›

pattern % A = op-var ‹ tcons (tast A) tnil ›

{- Variable Lookup -}

data Cat : Set where
  trm : Type → Cat
  typ : Cat
  bnd : Type → Cat

TyEnv : Set
TyEnv = List Cat

data _∋_⦂_ : TyEnv → Var → Cat → Set where
  trmZ : ∀{Γ}{A} → (trm A ∷ Γ) ∋ zero ⦂ trm A
  trmStrm : ∀{Γ}{A}{B}{x}
     → Γ ∋ x ⦂ trm A
     → (trm B ∷ Γ) ∋ suc x ⦂ trm A
  typtrm : ∀{Γ}{A}{x}
     → Γ ∋ x ⦂ trm A
     → (typ ∷ Γ) ∋ x ⦂ trm (⟪ renᵗ suc ⟫ᵗ A)
  bndtrm : ∀{Γ}{A}{B}{x}
     → Γ ∋ x ⦂ trm A
     → (bnd B ∷ Γ) ∋ x ⦂ trm (⟪ renᵗ suc ⟫ᵗ A)
     
  typZ : ∀{Γ} → (typ ∷ Γ) ∋ zero ⦂ typ
  typStyp : ∀{Γ}{x}
     → Γ ∋ x ⦂ typ
     → (typ ∷ Γ) ∋ suc x ⦂ typ
  bndStyp : ∀{Γ}{B}{x}
     → Γ ∋ x ⦂ typ
     → (bnd B ∷ Γ) ∋ suc x ⦂ typ
  trmStyp : ∀{Γ}{B}{x}
     → Γ ∋ x ⦂ typ
     → (trm B ∷ Γ) ∋ x ⦂ typ

  bndZ : ∀{Γ}{A} → (bnd A ∷ Γ) ∋ zero ⦂ bnd A
  typSbnd : ∀{Γ}{A}{x}
     → Γ ∋ x ⦂ bnd A
     → (typ ∷ Γ) ∋ suc x ⦂ bnd A
  bndSbnd : ∀{Γ}{A}{B}{x}
     → Γ ∋ x ⦂ bnd A
     → (bnd B ∷ Γ) ∋ suc x ⦂ bnd A
  trmSbnd : ∀{Γ}{A}{B}{x}
     → Γ ∋ x ⦂ bnd A
     → (trm B ∷ Γ) ∋ x ⦂ bnd A

{- Well-formed Types -}

infix 1 _⊢_ok
data _⊢_ok : TyEnv → Type → Set where

  ⊢-Nat : ∀{Γ}
       ----------
     → Γ ⊢ Nat ok

  ⊢-★ : ∀{Γ}
       ----------
     → Γ ⊢ ★ ok

  ⊢-XVar : ∀{Γ}{X}
     → Γ ∋ X ⦂ typ
       -----------
     → Γ ⊢ ^ X ok

  ⊢-Var : ∀{Γ}{α}
     → Γ ∋ α ⦂ typ
       --------------
     → Γ ⊢ % (^ α) ok

  ⊢-BndVar : ∀{Γ}{α}{A}
     → Γ ∋ α ⦂ bnd A
       --------------
     → Γ ⊢ % (^ α) ok

  ⊢-⇒ : ∀{Γ}{A}{B}
     → Γ ⊢ A ok
     → Γ ⊢ B ok
       ------------
     → Γ ⊢ A ⇒ B ok

  ⊢-∀ :  ∀{Γ}{A}
     → typ ∷ Γ ⊢ A ok
       --------------
     → Γ ⊢ ∀̇ A ok

{- Mono means not ∀ -}

data Mono : Type → Set where
  mono-nat : Mono Nat
  mono-unk : Mono ★
  mono-var : ∀{α} → Mono (^ α)
  mono-fun : ∀{A B} → Mono (A ⇒ B)

{- Precision -}

infix 3 _⊑_
data _⊑_ : Type → Type → Set where

  nat⊑nat : Nat ⊑ Nat

  Xvar⊑Xvar : ∀{X} → ^ X ⊑ ^ X

  var⊑var : ∀{α} → % (^ α) ⊑ % (^ α)

  unk⊑alpha : ∀{α} → ★ ⊑ % (^ α)
  
  unk⊑nat : ★ ⊑ Nat
  
  unk⊑fun : ∀{A}{B}
     → ★ ⊑ A
     → ★ ⊑ B
     → ★ ⊑ A ⇒ B

  fun⊑fun : ∀{A}{B}{A′}{B′}
     → A ⊑ A′
     → B ⊑ B′ 
     → A ⇒ B ⊑ A′ ⇒ B′ 

  all⊑all : ∀{A}{A′}
     → A ⊑ A′
     → ∀̇ A ⊑ ∀̇ A′

  any⊑all : ∀{A}{A′}
     → A ⊑ ⟪ % (^ 0) •ᵗ idᵗ ⟫ᵗ  A′   {- side condition that 0 ∈ A′? -}
     → A ⊑ ∀̇ A′

⊑-trans : ∀{A}{B}{C}
   → A ⊑ B
   → B ⊑ C
   → A ⊑ C
⊑-trans {A}{B}{C} A⊑B B⊑C = {!!}
   

{- Consistency is Least Upper Bound of ⊑ -}
infix 3 _~_
_~_ : Type → Type → Set
A ~ B = ∃[ C ] A ⊑ C × B ⊑ C × (∀ D → A ⊑ D → B ⊑ D → C ⊑ D)

nat~nat : Nat ~ Nat
nat~nat = Nat , nat⊑nat , nat⊑nat , λ D _ z → z

unk~nat : ★ ~ Nat
unk~nat  = Nat , unk⊑nat , nat⊑nat , λ D _ z → z

nat~unk : Nat ~ ★
nat~unk = Nat , nat⊑nat , unk⊑nat , λ D z _ → z

unk~var : ∀ {α} → ★ ~ % (^ α)
unk~var {α} = % (^ α) , unk⊑alpha , var⊑var , λ D _ z → z

var~unk : ∀ {α} → % (^ α) ~ ★
var~unk {α} = % (^ α) , var⊑var , unk⊑alpha , λ D z _ → z

all~all : ∀{A}{B}
   → A ~ B
   → ∀̇ A ~ ∀̇ B
all~all {A}{B} (C , AC , BC , least) = ∀̇ C , all⊑all AC , all⊑all BC , Goal
  where
  Goal : (D : Type) → ∀̇ A ⊑ D → ∀̇ B ⊑ D → ∀̇ C ⊑ D
  Goal (∀̇ D) (all⊑all A⊑D) (all⊑all B⊑D) = all⊑all (least D A⊑D B⊑D)
  Goal (∀̇ D) (all⊑all A⊑D) (any⊑all ∀B⊑D) =
     let ∀C⊑D = Goal D {!!} {!!} in
     all⊑all {!!}
  
  Goal (∀̇ D) (any⊑all ∀A⊑D) ∀B⊑D = {!!}

   
