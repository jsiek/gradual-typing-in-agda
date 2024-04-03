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
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Induction
open import Data.Maybe
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
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

module Poly.Types where

{-------------      Types    -------------}

data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base

_≡$?_ : (ι : Base) → (ι′ : Base) → Dec (ι ≡ ι′)
′ℕ  ≡$? ′ℕ  =  yes refl
′ℕ  ≡$? ′𝔹  =  no (λ ())
′𝔹  ≡$? ′ℕ  =  no (λ ())
′𝔹  ≡$? ′𝔹  =  yes refl

rep : Base → Set 
rep ′ℕ  =  ℕ
rep ′𝔹  =  𝔹

data TypeOp : Set where
  op-fun : TypeOp
  op-all : TypeOp
  op-base : Base → TypeOp
  op-unk : TypeOp

type-sig : TypeOp → List Sig
type-sig op-fun = ■ ∷ ■ ∷ []
type-sig op-all = (nu ■) ∷ []
type-sig (op-base ι) = []
type-sig op-unk = []

open import rewriting.AbstractBindingTree TypeOp type-sig
  using (FV; FV-suc-0)
  renaming (ABT to Type; Rename to Renameᵗ; rename to renameᵗ; Subst to Substᵗ;
            ren to renᵗ; ren-def to ren-defᵗ; extr to extrᵗ; ext to extᵗ;
            ⟪_⟫ to ⟪_⟫ᵗ; sub-var to sub-varᵗ; seq-def to seq-defᵗ; ↑ to ↑ᵗ;
            _[_] to _⦗_⦘; _⦅_⦆ to _‹_›; _•_ to _•ᵗ_; id to idᵗ; _⨟_ to _⨟ᵗ_;
            nil to tnil; cons to tcons; bind to tbind; ast to tast; `_ to ^_;
            FV-ren to FV-renᵗ; FV-ren-fwd to FV-ren-fwdᵗ)
  public

pattern $ b = (op-base b) ‹ tnil ›
pattern ★ = op-unk ‹ tnil ›

infixl 7  _⇒_
pattern _⇒_ A B = op-fun ‹ tcons (tast A) (tcons (tast B) tnil) ›

pattern ∀̇ A = op-all ‹ tcons (tbind (tast A)) tnil ›

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
  typZbnd : ∀{Γ}{A} → (bnd A ∷ Γ) ∋ zero ⦂ typ
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

  ⊢-base : ∀{Γ}{ι}
       ----------
     → Γ ⊢ $ ι ok

  ⊢-★ : ∀{Γ}
       ----------
     → Γ ⊢ ★ ok

  ⊢-Var : ∀{Γ}{x}
     → Γ ∋ x ⦂ typ
       -----------
     → Γ ⊢ ^ x ok

  ⊢-⇒ : ∀{Γ}{A}{B}
     → Γ ⊢ A ok
     → Γ ⊢ B ok
       ------------
     → Γ ⊢ A ⇒ B ok

  ⊢-∀ :  ∀{Γ}{A}
     → typ ∷ Γ ⊢ A ok
       --------------
     → Γ ⊢ ∀̇ A ok

dec : List Var → List Var
dec [] = []
dec (zero ∷ ls) = dec ls
dec (suc x ∷ ls) = x ∷ dec ls

{- Mono means not ∀ -}
data Mono : Type → Set where
  mono-base : ∀{ι} → Mono ($ ι)
  mono-unk : Mono ★
  mono-var : ∀{X} → Mono (^ X)
  mono-fun : ∀{A B} → Mono (A ⇒ B)

{-
sucₗ : Type × Type → Type × Type
sucₗ (A , B) = (⟪ renᵗ suc ⟫ᵗ A , B)

sucᵣ : Type × Type → Type × Type
sucᵣ (A , B) = (A , ⟪ renᵗ suc ⟫ᵗ B)

sucₚ : Type × Type → Type × Type
sucₚ (A , B) = (⟪ renᵗ suc ⟫ᵗ A , ⟪ renᵗ suc ⟫ᵗ B)
-}

{- Decide type equality -}
{-
infix 2 _=?ᵗ_
_=?ᵗ_ : (A : Type) → (B : Type) → Dec (A ≡ B)
★ =?ᵗ ★ = yes refl 
★ =?ᵗ ($ ι) = no λ () 
★ =?ᵗ (^ Y) = no λ () 
★ =?ᵗ (B₁ ⇒ B₂) = no λ () 
★ =?ᵗ (∀̇ B) = no λ () 
($ ι) =?ᵗ ($ ι′)
    with ι ≡$? ι′
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
($ ι) =?ᵗ ★ = no λ () 
($ ι) =?ᵗ (^ Y) = no λ () 
($ ι) =?ᵗ (B₁ ⇒ B₂) = no λ () 
($ ι) =?ᵗ (∀̇ B) = no λ () 
(^ X) =?ᵗ ★ = no λ () 
(^ X) =?ᵗ ($ ι) = no λ () 
(^ X) =?ᵗ (^ Y)
    with X ≟ Y
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
(^ X) =?ᵗ (B₁ ⇒ B₂) = no λ () 
(^ X) =?ᵗ (∀̇ B) = no λ () 
(A₁ ⇒ A₂) =?ᵗ ($ ι) = no λ () 
(A₁ ⇒ A₂) =?ᵗ ★ = no λ () 
(A₁ ⇒ A₂) =?ᵗ (^ Y) = no λ () 
(A₁ ⇒ A₂) =?ᵗ (B₁ ⇒ B₂)
    with A₁ =?ᵗ B₁ | A₂ =?ᵗ B₂
... | no no1 | _ = no λ {refl → no1 refl}
... | yes refl | no no2 = no λ {refl → no2 refl}
... | yes refl | yes refl = yes refl
(A₁ ⇒ A₂) =?ᵗ (∀̇ B) = no λ () 
(∀̇ A) =?ᵗ ($ ι) = no λ () 
(∀̇ A) =?ᵗ ★ = no λ () 
(∀̇ A) =?ᵗ (^ Y) = no λ () 
(∀̇ A) =?ᵗ (B₁ ⇒ B₂) = no λ () 
(∀̇ A) =?ᵗ (∀̇ B)
    with A =?ᵗ B
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
-}
{-
  The lub C will have all the ∀'s from A and B.

  Need to figure out the 𝒢's and Ψ's to use for A ⊑ C and B ⊑ C.

-}
{-
~⇒lub⊑ : ∀{𝒢}{ℋ}{Ψ}{A}{B}
   → 𝒞 ⊢ A ~ B
   → ∃[ C ] ∃[ Ψₗ ] ∃[ Ψᵣ ] (𝒢 ∣ Ψₗ ⊢ A ⊑ C) × (ℋ ∣ Ψᵣ ⊢ B ⊑ C)
~⇒lub⊑ {𝒢} {ℋ} {Ψ} {.Nat} {.Nat} nat~nat =
    Nat , [] , [] , nat⊑nat , nat⊑nat
~⇒lub⊑ {𝒢} {ℋ} {Ψ} {^ α} {^ β} (var~var ab∈Ψ) =
    (^ β) , Ψ , (β , β) ∷ [] , var⊑var ab∈Ψ , var⊑var (here refl)
~⇒lub⊑ {𝒢} {ℋ} {Ψ} {.★} {B} (unk~any m x) =
  B , {!!} , {!!} , unk⊑any m {!!} , {!!}
~⇒lub⊑ {𝒢} {ℋ} {Ψ} {A} {.★} (any~unk m x) = {!!}
~⇒lub⊑ {𝒢} {ℋ} {Ψ} {.(_ ⇒ _)} {.(_ ⇒ _)} (fun~fun A~B A~B₁) = {!!}
~⇒lub⊑ {𝒢} {ℋ} {Ψ} {.(∀̇ _)} {.(∀̇ _)} (all~all A~B) = {!!}
~⇒lub⊑ {𝒢} {ℋ} {Ψ} {.(∀̇ _)} {B} (all~any A~B) = {!!}
~⇒lub⊑ {𝒢} {ℋ} {Ψ} {A} {.(∀̇ _)} (any~all A~B) = {!!}
-}

{- Precision -}

infix 6 _⊑_
data _⊑_ : Type → Type → Set where

  base⊑base : ∀{ι} → $ ι ⊑ $ ι

  var⊑var : ∀{X} → ^ X ⊑ ^ X

  unk⊑unk : ★ ⊑ ★

  unk⊑base : ∀{ι} → ★ ⊑ $ ι

  unk⊑fun : ∀{A}{B}
      → ★ ⊑ A
      → ★ ⊑ B
      → ★ ⊑ A ⇒ B

  unk⊑all : ∀{B}
      → ★ ⊑ ∀̇ B

  fun⊑fun : ∀{A}{B}{A′}{B′}
     → A ⊑ A′
     → B ⊑ B′ 
     → A ⇒ B ⊑ A′ ⇒ B′ 

  all⊑all : ∀{A}{A′}
     → A ⊑ A′
     → ∀̇ A ⊑ ∀̇ A′

{- Least Upper Bound -}

infix 6 _⊔_
_⊔_ : Type → Type → Maybe Type
★ ⊔ ★ = just ★
★ ⊔ (^ X) = nothing
★ ⊔ ($ ι) = just ($ ι)
★ ⊔ (B₁ ⇒ B₂) = just (B₁ ⇒ B₂)
★ ⊔ (∀̇ B) = just (∀̇ B)
($ ι) ⊔ ★ = just ($ ι)
($ ι) ⊔ ($ ι′)
    with ι ≡$? ι′ 
... | yes refl = just ($ ι)
... | no neq = nothing
($ ι) ⊔ B = nothing
(^ X) ⊔ ★ = nothing
(^ X) ⊔ (^ Y)
    with X ≟ Y
... | yes refl = just (^ X)
... | no neq = nothing
(^ X) ⊔ B = nothing
(A₁ ⇒ A₂) ⊔ ★ = just (A₁ ⇒ A₂)
(A₁ ⇒ A₂) ⊔ (B₁ ⇒ B₂)
    with A₁ ⊔ B₁ | A₂ ⊔ B₂
... | nothing | _ = nothing
... | just C₁ | nothing = nothing
... | just C₁ | just C₂ = just (C₁ ⇒ C₂)
(A₁ ⇒ A₂) ⊔ B = nothing
(∀̇ A) ⊔ ★ = just (∀̇ A)
(∀̇ A) ⊔ (∀̇ B)
    with A ⊔ B
... | nothing = nothing
... | just C = just (∀̇ C)
(∀̇ A) ⊔ B = nothing


{- Consistency -}

infix 6 _~_
data _~_ : Type → Type → Set where

  base~base : ∀{ι} → $ ι ~ $ ι

  var~var : ∀{X} → ^ X ~ ^ X

  unk~unk : ★ ~ ★

  unk~base : ∀{ι}
     → ★ ~ $ ι

  unk~fun : ∀{A}{B}
     → ★ ~ A ⇒ B

  unk~all : ∀{A}
     → ★ ~ ∀̇ A

  base~unk : ∀{ι}
     → $ ι ~ ★

  fun~unk : ∀{A}{B}
     → A ⇒ B ~ ★

  all~unk : ∀{A}
     → ∀̇ A ~ ★

  fun~fun : ∀{A}{B}{A′}{B′}
     → A ~ A′
     → B ~ B′ 
     → A ⇒ B ~ A′ ⇒ B′ 

  all~all : ∀{A}{A′}
     → A ~ A′
     → ∀̇ A ~ ∀̇ A′

⊔-upper-bound : ∀{A B C}
   → A ⊔ B ≡ just C
   → A ⊑ C × B ⊑ C
⊔-upper-bound {★}{★}{C} refl = unk⊑unk , unk⊑unk
⊔-upper-bound {★}{$ ι}{C} refl = unk⊑base , base⊑base
⊔-upper-bound {★}{^ X}{C} ()
⊔-upper-bound {★}{B₁ ⇒ B₂}{C} refl = {!!} , {!!}
⊔-upper-bound {★}{∀̇ B}{C} A⊔B=C = {!!}
⊔-upper-bound {$ ι}{B}{C} A⊔B=C = {!!}
⊔-upper-bound {^ X}{B}{C} A⊔B=C = {!!}
⊔-upper-bound {A₁ ⇒ A₂}{B}{C} A⊔B=C = {!!}
⊔-upper-bound {∀̇ A}{B}{C} A⊔B=C = {!!}

