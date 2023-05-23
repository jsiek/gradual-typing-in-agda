{-# OPTIONS --rewriting #-}
{-
   A polymorphic blame calculus partly based on a version 
   by Jeremy, Phil Wadler, and Peter Thiemann.
-}

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (map-++-commute)
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

module Poly.Types where

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

{- Free Variables -}

dec : List Var → List Var
dec [] = []
dec (zero ∷ ls) = dec ls
dec (suc x ∷ ls) = x ∷ dec ls

{-
FV : Type → List Var
FV Nat = []
FV ★ = []
FV (^ β) = β ∷ []
FV (A ⇒ B) = FV A ++ FV B
FV (∀̇ A) = dec (FV A)
-}

{- Consistency -}

{- Mono means not ∀ -}
data Mono : Type → Set where
  mono-nat : Mono Nat
  mono-unk : Mono ★
  mono-var : ∀{α} → Mono (^ α)
  mono-fun : ∀{A B} → Mono (A ⇒ B)

infix 1 _⊢_~_
data _⊢_~_ : List Var → Type → Type → Set where

  nat~nat : ∀{Ψ} → Ψ ⊢ Nat ~ Nat

  var~var : ∀{Ψ}{α} → Ψ ⊢ ^ α ~ ^ α

  unk~any : ∀{Ψ}{A}
     → FV A ⊆ mem Ψ
     → Ψ ⊢ ★ ~ A

  any~unk : ∀{Ψ}{A}
     → FV A ⊆ mem Ψ
     → Ψ ⊢ A ~ ★

  fun~fun : ∀{Ψ}{A}{B}{A′}{B′}
     → Ψ ⊢ A ~ A′
     → Ψ ⊢ B ~ B′ 
     → Ψ ⊢ A ⇒ B ~ A′ ⇒ B′ 

  all~all : ∀{Ψ}{A}{A′}
     → map suc Ψ ⊢ A ~ A′
     → Ψ ⊢ ∀̇ A ~ ∀̇ A′

  all~any : ∀{Ψ}{A}{A′}
     → 0 ∷ map suc Ψ ⊢ A ~ ⟪ renᵗ suc ⟫ᵗ A′
     → Ψ ⊢ ∀̇ A ~ A′

  any~all : ∀{Ψ}{A}{A′}
     → 0 ∷ map suc Ψ ⊢ ⟪ renᵗ suc ⟫ᵗ A ~ A′
     → Ψ ⊢ A ~ ∀̇ A′

{- Precision -}

infix 1 _⊢_⊑_
data _⊢_⊑_ : List Var → Type → Type → Set where

  nat⊑nat : ∀{Ψ} → Ψ ⊢ Nat ⊑ Nat

  var⊑var : ∀{Ψ}{α} → Ψ ⊢ ^ α ⊑ ^ α

  unk⊑any : ∀{Ψ}{A}
     → Mono A                     {- to prevent overlap with mono⊑all -}
     → FV A ⊆ mem Ψ
     → Ψ ⊢ ★ ⊑ A

  fun⊑fun : ∀{Ψ}{A}{B}{A′}{B′}
     → Ψ ⊢ A ⊑ A′
     → Ψ ⊢ B ⊑ B′ 
     → Ψ ⊢ A ⇒ B ⊑ A′ ⇒ B′ 

  all⊑all : ∀{Ψ}{A}{A′}
     → map suc Ψ ⊢ A ⊑ A′
     → Ψ ⊢ ∀̇ A ⊑ ∀̇ A′

  any⊑all : ∀{Ψ}{A}{A′}
     → 0 ∷ map suc Ψ ⊢ ⟪ renᵗ suc ⟫ᵗ A ⊑ A′
     → Ψ ⊢ A ⊑ ∀̇ A′

∈-mem-map : ∀{A B : Set}{Ψ : List A}{f : A → B}{x : A}
   → x ∈ mem Ψ
   → f x ∈ mem (map f Ψ)
∈-mem-map {A} {B} {x ∷ Ψ} (here refl) = here refl
∈-mem-map {A} {B} {x ∷ Ψ} (there x∈) = there (∈-mem-map x∈)

∈-mem-map-inv : ∀{Ψ : List Var}{y : Var}
   → y ∈ mem (map suc Ψ)
   → ∃[ x ] y ≡ suc x × x ∈ mem Ψ
∈-mem-map-inv {[]} {y} ()
∈-mem-map-inv {z ∷ Ψ} {y} (here refl) = z , refl , here refl
∈-mem-map-inv {z ∷ Ψ} {y} (there fx∈)
    with ∈-mem-map-inv fx∈
... | x , refl , x∈ = x , refl , there x∈

mem-map-⊆ : ∀{Ψ}{Ψ′}
   → mem Ψ ⊆ mem Ψ′
   → mem (map suc Ψ) ⊆ mem (map suc Ψ′)
mem-map-⊆ {[]} {Ψ′} Ψ⊆Ψ′ = λ d ()
mem-map-⊆ {x ∷ Ψ} {Ψ′} Ψ⊆Ψ′ d (here refl) =
    let x∈Ψ′ = Ψ⊆Ψ′ x (here refl) in
    ∈-mem-map x∈Ψ′
mem-map-⊆ {x ∷ Ψ} {Ψ′} Ψ⊆Ψ′ y (there y∈sucΨ)
    with ∈-mem-map-inv y∈sucΨ
... | z , refl , z∈ =
    let z∈Ψ′ = Ψ⊆Ψ′ z (there z∈) in
    ∈-mem-map z∈Ψ′

weaken⊑ : ∀{A}{B}{Ψ}{Ψ′}
  → Ψ ⊢ A ⊑ B
  → mem Ψ ⊆ mem Ψ′
  → Ψ′ ⊢ A ⊑ B
weaken⊑ {A}{B}{Ψ}{Ψ′} A⊑B Ψ⊆Ψ′ = {!!}

weaken~ : ∀{A}{B}{Ψ}{Ψ′}
  → Ψ ⊢ A ~ B
  → mem Ψ ⊆ mem Ψ′
  → Ψ′ ⊢ A ~ B
weaken~ {.Nat} {.Nat} {Ψ} {Ψ′} nat~nat Ψ⊆Ψ′ =
    nat~nat
weaken~ var~var Ψ⊆Ψ′ = var~var
weaken~ {.★} {B} {Ψ} {Ψ′} (unk~any x) Ψ⊆Ψ′ =
    unk~any (λ d z → Ψ⊆Ψ′ d (x d z))
weaken~ {A} {.★} {Ψ} {Ψ′} (any~unk x) Ψ⊆Ψ′ =
    any~unk (λ d z → Ψ⊆Ψ′ d (x d z))
weaken~ {.(_ ⇒ _)} {.(_ ⇒ _)} {Ψ} {Ψ′} (fun~fun A~B A~B₁) Ψ⊆Ψ′ =
    fun~fun (weaken~ A~B Ψ⊆Ψ′) (weaken~ A~B₁ Ψ⊆Ψ′)
weaken~ {∀̇ A} {∀̇ B} {Ψ} {Ψ′} (all~all A~B) Ψ⊆Ψ′ =
    let IH = weaken~{A}{B}{map suc Ψ}{map suc Ψ′} A~B (mem-map-⊆ Ψ⊆Ψ′) in
    all~all IH
weaken~ {.(∀̇ _)} {B} {Ψ} {Ψ′} (all~any A~B) Ψ⊆Ψ′ =
    let IH = weaken~ A~B (λ { d (here px) → here px
                         ; d (there d∈sucΨ) → there (mem-map-⊆ Ψ⊆Ψ′ d d∈sucΨ)})
                         in
    all~any IH
weaken~ {A} {.(∀̇ _)} {Ψ} {Ψ′} (any~all A~B) Ψ⊆Ψ′ =
    let IH = weaken~ A~B (λ { d (here px) → here px
                         ; d (there d∈sucΞ) → there (mem-map-⊆ Ψ⊆Ψ′ d d∈sucΞ)})
                         in
    any~all IH

weaken~₂ : ∀{A}{B}{Ψ}{Ψ′}
  → Ψ ⊢ A ~ B
  → (∀ d → d ∈ ((FV A) ∪ (FV B)) → d ∈ mem Ψ → d ∈ mem Ψ′)
  → Ψ′ ⊢ A ~ B
weaken~₂ {A}{B}{Ψ}{Ψ′} A~B = {!!}

mem-map-suc-dec : ∀ ls
   → mem ls ⊆ mem (0 ∷ map suc (dec ls))
mem-map-suc-dec (zero ∷ ls) d (here px) = here px
mem-map-suc-dec (suc x ∷ ls) d (here px) = there (here px)
mem-map-suc-dec (zero ∷ ls) d (there d∈)
    with mem-map-suc-dec ls d d∈
... | here refl = here refl
... | there d∈sdls = there d∈sdls
mem-map-suc-dec (suc x ∷ ls) d (there d∈)
    with mem-map-suc-dec ls d d∈
... | here refl = here refl
... | there d∈sdls = there (there d∈sdls)

unk⊑unk : ∀{Ψ} → Ψ ⊢ ★ ⊑ ★
unk⊑unk = unk⊑any mono-unk λ d ()

⊑-refl : ∀{Ψ}{A} → Ψ ⊢ A ⊑ A
⊑-refl {Ψ}{Nat} = nat⊑nat
⊑-refl {Ψ}{^ α} = var⊑var
⊑-refl {Ψ}{★} = unk⊑unk
⊑-refl {Ψ}{A ⇒ B} = fun⊑fun ⊑-refl ⊑-refl
⊑-refl {Ψ}{∀̇ A} = all⊑all ⊑-refl

{- todo: ⊑-trans -}

dec-++ : ∀ xs ys → dec (xs ++ ys) ≡ dec xs ++ dec ys
dec-++ [] ys = refl
dec-++ (zero ∷ xs) ys = dec-++ xs ys
dec-++ (suc x ∷ xs) ys = cong₂ _∷_ refl (dec-++ xs ys)

sα∈S→α∈decS : ∀{α}{S}
   → suc α ∈ mem S
   → α ∈ mem (dec S)
sα∈S→α∈decS {α} {zero ∷ S} (there sα∈S) = sα∈S→α∈decS sα∈S
sα∈S→α∈decS {α} {suc x ∷ S} (here refl) = here refl
sα∈S→α∈decS {α} {suc x ∷ S} (there sα∈S) = there (sα∈S→α∈decS sα∈S)

α∈decS→sα∈S : ∀{α}{S}
  → α ∈ mem (dec S)
  → suc α ∈ mem S
α∈decS→sα∈S {α} {zero ∷ S} a∈decS = there (α∈decS→sα∈S a∈decS)
α∈decS→sα∈S {α} {suc x ∷ S} (here refl) = here refl
α∈decS→sα∈S {α} {suc x ∷ S} (there a∈decS) = there (α∈decS→sα∈S a∈decS)

dec-map-extr : ∀ ρ ls → dec (map (extrᵗ ρ) ls) ≡ map ρ (dec ls)
dec-map-extr ρ [] = refl
dec-map-extr ρ (zero ∷ ls) = dec-map-extr ρ ls
dec-map-extr ρ (suc x ∷ ls) = cong₂ _∷_ refl (dec-map-extr ρ ls)

{-
FV-ren-map : ∀ {A}{ρ} → FV (⟪ renᵗ ρ ⟫ᵗ A) ≡ map ρ (FV A)
FV-ren-map {^ x}{ρ} rewrite sub-varᵗ (renᵗ ρ) x | ren-defᵗ ρ x = refl
FV-ren-map {Nat}{ρ} = refl
FV-ren-map {★}{ρ} = refl
FV-ren-map {A ⇒ B}{ρ} rewrite FV-ren-map{A}{ρ} | FV-ren-map{B}{ρ}
    | map-++-commute ρ (FV A) (FV B) =
    refl
FV-ren-map {∀̇ A}{ρ} rewrite FV-ren-map {A}{extrᵗ ρ} = dec-map-extr ρ (FV A)
-}

⊆-dec : ∀{xs}{ys}
   → mem xs ⊆ mem ys
   → mem (dec xs) ⊆ mem (dec ys)
⊆-dec {[]} {ys} xs⊆ys = λ d ()
⊆-dec {zero ∷ xs} {ys} xs⊆ys = ⊆-dec (λ d z → xs⊆ys d (there z))
⊆-dec {suc x ∷ xs} {ys} xs⊆ys d (here refl) =
    sα∈S→α∈decS (xs⊆ys (suc x) (here refl))
⊆-dec {suc x ∷ xs} {ys} xs⊆ys d (there d∈) =
    ⊆-dec (λ d z → xs⊆ys d (there z)) d d∈

FV⊑ : ∀{Ψ}{A}{B}
   → Ψ ⊢ A ⊑ B
   → FV A ⊆ FV B
FV⊑ {ψ}{Nat}{B} A⊑B = λ d ()
FV⊑ {ψ}{★}{B} A⊑B = λ d ()
FV⊑ {ψ} {^ α} {.(^ α)} var⊑var = λ d z → z
FV⊑ {ψ} {^ α} {∀̇ B} (any⊑all ⊑B) d refl rewrite sub-varᵗ (renᵗ suc) α
    | ren-defᵗ suc α =
    inj₁ (FV⊑ ⊑B (suc α) refl)
FV⊑ {ψ}{A₁ ⇒ A₂}{B₁ ⇒ B₂} (fun⊑fun A₁⊑B₁ A₂⊑B₂) d (inj₁ d∈A₁) =
    inj₁ (FV⊑ A₁⊑B₁ d d∈A₁)
FV⊑ {ψ}{A₁ ⇒ A₂}{B₁ ⇒ B₂} (fun⊑fun A₁⊑B₁ A₂⊑B₂) d (inj₂ (inj₁ d∈A₂)) =
    inj₂ (inj₁ (FV⊑ A₂⊑B₂ d d∈A₂ ))
FV⊑ {ψ}{A₁ ⇒ A₂}{B₁ ⇒ B₂} (fun⊑fun A₁⊑B₁ A₂⊑B₂) d (inj₂ (inj₂ ()))
FV⊑ {ψ}{A₁ ⇒ A₂}{∀̇ B} (any⊑all A⊑B) d (inj₁ d∈A₁) =
  let IH = FV⊑ A⊑B in
  let sd∈sA₁ = FV-ren-fwdᵗ suc A₁ d d∈A₁ in
  let sd∈B = IH (suc d) (inj₁ sd∈sA₁) in
  inj₁ sd∈B
FV⊑ {ψ}{A₁ ⇒ A₂}{∀̇ B} (any⊑all A⊑B) d (inj₂ (inj₁ d∈A₂)) =
  let IH = FV⊑ A⊑B in
  let sd∈sA₂ = FV-ren-fwdᵗ suc A₂ d d∈A₂ in
  let sd∈B = IH (suc d) (inj₂ (inj₁ sd∈sA₂)) in
  inj₁ sd∈B
FV⊑ {ψ}{A₁ ⇒ A₂}{∀̇ B} (any⊑all A⊑B) d (inj₂ (inj₂ ()))
FV⊑ {ψ}{∀̇ A}{∀̇ B} (all⊑all A⊑B) d (inj₁ sd∈A) =
  let sd∈B = FV⊑ A⊑B (suc d) sd∈A in
  inj₁ sd∈B
FV⊑ {ψ}{∀̇ A}{∀̇ B} (all⊑all A⊑B) d (inj₂ ())
FV⊑ {ψ}{∀̇ A}{∀̇ B} (any⊑all A⊑B) d (inj₁ sd∈A) =
  let ssd∈sA = FV-ren-fwdᵗ (extrᵗ suc) A (suc d) sd∈A in
  inj₁ (FV⊑ A⊑B (suc d) (inj₁ ssd∈sA))
FV⊑ {ψ}{∀̇ A}{∀̇ B} (any⊑all A⊑B) d (inj₂ ())

ren~-inv : ∀ ρ Ψ A B
  → (∀ x y → ρ x ≡ ρ y → x ≡ y)
  → map ρ Ψ ⊢ ⟪ renᵗ ρ ⟫ᵗ A ~ ⟪ renᵗ ρ ⟫ᵗ B
  → Ψ ⊢ A ~ B
ren~-inv ρ Ψ A B ρsurj ρA~ρB = {!!}

A⊑C×B⊑C⇒A~B : ∀{A}{B}{C}{Ψ}
   → Ψ ⊢ A ⊑ C
   → Ψ ⊢ B ⊑ C
   → Ψ ⊢ A ~ B
A⊑C×B⊑C⇒A~B {.Nat} {.Nat} {.Nat} nat⊑nat nat⊑nat = nat~nat
A⊑C×B⊑C⇒A~B {.Nat} {.★} {.Nat} nat⊑nat (unk⊑any m sub) = any~unk λ d ()
A⊑C×B⊑C⇒A~B var⊑var var⊑var = var~var
A⊑C×B⊑C⇒A~B {Ψ = Ψ} var⊑var (unk⊑any m sub) = any~unk sub
A⊑C×B⊑C⇒A~B {.★} {.Nat} {.Nat} (unk⊑any m sub) nat⊑nat = unk~any λ d ()
A⊑C×B⊑C⇒A~B {Ψ = Ψ} (unk⊑any m sub) var⊑var = unk~any sub
A⊑C×B⊑C⇒A~B {.★} {.★} {C} (unk⊑any m sub) (unk⊑any m′ x) = unk~any λ d ()
A⊑C×B⊑C⇒A~B {.★} {Ψ = Ψ} (unk⊑any m sub) (fun⊑fun{A = A}{B}{C}{D} A⊑C B⊑D) =
  unk~any Goal
  where
  Goal : FV (A ⇒ B) ⊆ mem Ψ
  Goal d (inj₁ d∈A) = sub d (inj₁ (FV⊑ A⊑C d d∈A))
  Goal d (inj₂ (inj₁ d∈B)) = sub d (inj₂ (inj₁ (FV⊑ B⊑D d d∈B)))
  Goal d (inj₂ (inj₂ ()))
A⊑C×B⊑C⇒A~B {.★} {∀̇ A} {∀̇ B}{Ψ} (unk⊑any m sub) (all⊑all A⊑B) =
    unk~any Goal
    where
    Goal : FV (∀̇ A) ⊆ mem Ψ
    Goal d (inj₁ sd∈A) = sub d (inj₁ (FV⊑ A⊑B (suc d) sd∈A))
    Goal d (inj₂ ())
A⊑C×B⊑C⇒A~B {.★} {B} {∀̇ C}{Ψ} (unk⊑any m sub) (any⊑all B⊑C) =
    unk~any Goal
    where
    Goal : FV B ⊆ mem Ψ
    Goal d d∈B = sub d (inj₁ (FV⊑ B⊑C (suc d) (FV-ren-fwdᵗ suc B d d∈B)))
A⊑C×B⊑C⇒A~B {A ⇒ A′} {.★} {C ⇒ C′}{Ψ}  (fun⊑fun A⊑C A⊑C₁) (unk⊑any m sub) =
    any~unk Goal
    where
    Goal : FV (A ⇒ A′) ⊆ mem Ψ
    Goal d (inj₁ d∈A) = sub d (inj₁ (FV⊑ A⊑C d d∈A))
    Goal d (inj₂ (inj₁ d∈A′)) = sub d (inj₂ (inj₁ (FV⊑ A⊑C₁ d d∈A′))) 
A⊑C×B⊑C⇒A~B (fun⊑fun A⊑C A⊑C₁) (fun⊑fun B⊑C B⊑C₁) =
    fun~fun (A⊑C×B⊑C⇒A~B A⊑C B⊑C) (A⊑C×B⊑C⇒A~B A⊑C₁ B⊑C₁)
A⊑C×B⊑C⇒A~B {∀̇ A} {.★} {∀̇ C} (all⊑all A⊑C) (unk⊑any () _)
A⊑C×B⊑C⇒A~B {∀̇ A} {∀̇ B} {∀̇ C} (all⊑all A⊑C) (all⊑all B⊑C) =
    all~all (A⊑C×B⊑C⇒A~B A⊑C B⊑C)
A⊑C×B⊑C⇒A~B {∀̇ A} {B} {∀̇ C} (all⊑all A⊑C) (any⊑all B⊑C) =
    all~any (A⊑C×B⊑C⇒A~B (weaken⊑ A⊑C λ d → there) B⊑C)
A⊑C×B⊑C⇒A~B {A} {.★} {.(∀̇ _)} (any⊑all A⊑C) (unk⊑any () x₁)
A⊑C×B⊑C⇒A~B {A} {.(∀̇ _)} {.(∀̇ _)} (any⊑all A⊑C) (all⊑all B⊑C) =
    any~all (A⊑C×B⊑C⇒A~B A⊑C (weaken⊑ B⊑C λ d → there))
A⊑C×B⊑C⇒A~B {A} {B} {∀̇ C}{Ψ} (any⊑all A⊑C) (any⊑all B⊑C) =
  let IH : 0 ∷ map suc Ψ ⊢ ⟪ renᵗ suc ⟫ᵗ A ~ ⟪ renᵗ suc ⟫ᵗ B
      IH = A⊑C×B⊑C⇒A~B A⊑C B⊑C in
  let IH₂ : map suc Ψ ⊢ ⟪ renᵗ suc ⟫ᵗ A ~ ⟪ renᵗ suc ⟫ᵗ B
      IH₂ = weaken~₂ IH Goal in
  ren~-inv suc Ψ A B (λ { x .x refl → refl}) IH₂
  where
  Goal : (d : Var)
         → d ∈ (FV (⟪ renᵗ suc ⟫ᵗ A) ∪ FV (⟪ renᵗ suc ⟫ᵗ B))
         → d ∈ mem (0 ∷ map suc Ψ)
         → d ∈ mem (map suc Ψ)
  Goal .0 (inj₁ z∈sA) (here refl) = ⊥-elim (FV-suc-0 A z∈sA)
  Goal .0 (inj₂ z∈sB) (here refl) = ⊥-elim (FV-suc-0 B z∈sB)
  Goal d d∈A∪B (there d∈sucΨ) = d∈sucΨ
   
