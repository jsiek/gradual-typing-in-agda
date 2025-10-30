module PolyBlame.PolyBlame where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List hiding ([_])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)

postulate
  extensionality : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁ }{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Variables are de Bruijn indices
Var = ℕ

{-- Renaming (Language Independent Stuff) --}
Rename : Set
Rename = Var → Var

infixr 6 _•ᵣ_
_•ᵣ_ : Var → Rename → Rename
(y •ᵣ ρ) 0 = y
(y •ᵣ ρ) (suc x) = ρ x

⟰ᵣ : Rename → Rename
⟰ᵣ ρ x = suc (ρ x)

extr : Rename → Rename
extr ρ = 0 •ᵣ ⟰ᵣ ρ

idr : Rename
idr x = x

-- Syntax of Polymorphic Cast Calculus

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infixl 7 _◯_
infix  9 `_
infix  9 #_

data Grnd : Set where
  ★⇒★ : Grnd
  `ℕ  : Grnd
  `_ : Var → Grnd
  
data Type : Set where
  `ℕ  : Type
  ★   : Type
  `_ : Var → Type
  _⇒_ : Type → Type → Type
  `∀_  : Type → Type

data Crcn : Set where
 id : Crcn
 _↦_ : Crcn → Crcn → Crcn
 _⨟_ : Crcn → Crcn → Crcn
 `∀_ : Crcn → Crcn
 𝒢_ : Crcn → Crcn
 ℐ_ : Crcn → Crcn
 _↓ : Var → Crcn
 _↑ : Var → Crcn
 _! : Grnd → Crcn
 _`? : Grnd → Crcn

data Expr : Set where
  `_ : Var → Expr
  #_ : ℕ → Expr
  ƛ_ : Expr → Expr
  _·_ : Expr → Expr → Expr
  Λ_ : Expr → Expr
  _◯_ : Expr → Var → Expr
  ν_·_ : Type → Expr → Expr
  _⟨_⟩ : Expr → Crcn → Expr
  blame : Expr

-- Type Renaming in Type
ren-ty : Rename → Type → Type
ren-ty ρ (A ⇒ B) = (ren-ty ρ A) ⇒ (ren-ty ρ B)
ren-ty ρ `ℕ = `ℕ
ren-ty ρ ★ = ★
ren-ty ρ (`∀ A) = `∀ (ren-ty (extr ρ) A)
ren-ty ρ (` X) = ` (ρ X)

-- Type Renaming in Grnd
rename-grnd : Rename → Grnd → Grnd
rename-grnd ρ ★⇒★ = ★⇒★
rename-grnd ρ `ℕ = `ℕ
rename-grnd ρ (` X) = ` ρ X

-- Type Renaming in Crcn
rename-crcn : Rename → Crcn → Crcn
rename-crcn ρ id = id
rename-crcn ρ (c ↦ d) = (rename-crcn ρ c) ↦ (rename-crcn ρ d)
rename-crcn ρ (c ⨟ d) = (rename-crcn ρ c) ⨟ (rename-crcn ρ d)
rename-crcn ρ (`∀ c) = `∀ (rename-crcn (extr ρ) c)
rename-crcn ρ (𝒢 c) = 𝒢 (rename-crcn (extr ρ) c)
rename-crcn ρ (ℐ c) = ℐ (rename-crcn (extr ρ) c)
rename-crcn ρ (X ↓) = (ρ X) ↓
rename-crcn ρ (X ↑) = (ρ X) ↑
rename-crcn ρ (G !) = (rename-grnd ρ G) !
rename-crcn ρ (G `?) = (rename-grnd ρ G) `?

-- Type Renaming in Expr
rename-ty : Rename → Expr → Expr
rename-ty ρ (` x) = ` ρ x
rename-ty ρ (# k) = # k
rename-ty ρ (ƛ M) = rename-ty (extr ρ) M
rename-ty ρ (L · M) = (rename-ty ρ L) · (rename-ty ρ M)
rename-ty ρ (Λ N) = Λ (rename-ty ρ N)
rename-ty ρ (L ◯ X) = (rename-ty ρ L) ◯ (ρ X)
rename-ty ρ (ν A · N) = ν A · (rename-ty ρ N)
rename-ty ρ (M ⟨ c ⟩) = (rename-ty ρ M) ⟨ rename-crcn ρ c ⟩
rename-ty ρ blame = blame

-- Term Renaming
rename : Rename → Expr → Expr
rename ρ (` x) = ` ρ x
rename ρ (# k) = # k
rename ρ (ƛ M) = ƛ (rename (extr ρ) M)
rename ρ (L · M) = (rename ρ L) · (rename ρ M)
rename ρ (Λ N) = Λ (rename ρ N)
rename ρ (L ◯ X) = (rename ρ L) ◯ X
rename ρ (ν A · N) = ν A · (rename ρ N)
rename ρ (M ⟨ c ⟩) = (rename ρ M) ⟨ c ⟩
rename ρ blame = blame

{--- Term Substitution --}
Subst : Set
Subst = Var → Expr

infixr 6 _•_
_•_ : Expr → Subst → Subst
(M • σ) 0 = M
(M • σ) (suc x) = σ x

⟰ : Subst → Subst
⟰ σ x = rename suc (σ x)

exts : Subst → Subst
exts σ = ` 0 • ⟰ σ

⟰ᵗ : Subst → Subst
⟰ᵗ σ x = rename-ty suc (σ x)

sub : Subst → Expr → Expr
sub σ (` x) = σ x
sub σ (# k) = # k
sub σ (ƛ N) = ƛ (sub (exts σ) N)
sub σ (L · M) = (sub σ L) · (sub σ M)
sub σ (Λ N) = Λ (sub (⟰ᵗ σ) N)
sub σ (M ◯ X) = (sub σ M) ◯ X
sub σ (ν A · N) = ν A · (sub (⟰ᵗ σ) N)
sub σ (M ⟨ c ⟩) = (sub σ M) ⟨ c ⟩
sub σ blame = blame

infixr 5 _;_
_;_ : Subst → Subst → Subst
(σ ; τ) x = sub τ (σ x)

ids : Subst
ids x = ` x

_[_] : Expr → Expr → Expr
N [ M ] =  sub (M • ids) N

{--- Values ---}

data Value : Expr → Set where
  V-ƛ : ∀{N} → Value (ƛ N)
  V-# : ∀{k} → Value (# k)
  V-Λ : ∀{V} → Value V → Value (Λ V)
  V-! : ∀{V G} → Value V → Value (V ⟨ G ! ⟩)
  V-↦ : ∀{V c d} → Value V → Value (V ⟨ c ↦ d ⟩)
  V-𝒢 : ∀{V c} → Value V → Value (V ⟨ 𝒢 c ⟩)
  V-∀ : ∀{V c} → Value V → Value (V ⟨ `∀ c ⟩)

{--- Frames ---}

data Frame : Set where
  □·_ : Expr → Frame
  _·□ : Expr → Frame
  □⟨_⟩ : Crcn → Frame
  □◯_ : Var → Frame
  ν_·□ : Type → Frame

plug : Frame → Expr → Expr
plug (□· M) L = L · M
plug (L ·□) M = L · M
plug □⟨ c ⟩ M = M ⟨ c ⟩
plug (□◯ X) M = M ◯ X
plug ν A ·□ N = ν A · N

rename-frame : Rename → Frame → Frame
rename-frame ρ (□· M) = □· (rename-ty ρ M)
rename-frame ρ (L ·□) = (rename-ty ρ L) ·□
rename-frame ρ □⟨ c ⟩ = □⟨ rename-crcn ρ c ⟩
rename-frame ρ (□◯ X) = □◯ (ρ X)
rename-frame ρ ν A ·□ = ν (ren-ty ρ A) ·□

{--- Reduction ---}

infix 2 _—→_

data _—→_ : Expr → Expr → Set where

  ξ : ∀{F M N}
    → M —→ N
      ---------------------
    → plug F M —→ plug F N

  β-ƛ : ∀{N W}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀{V X}
      -----------------------------------
    → (Λ V) ◯ X —→ rename-ty (X •ᵣ idr) V

  β-↦ : ∀{V W c d}
      ----------------------------------------
    → V ⟨ c ↦ d ⟩ · W —→ (V · (W ⟨ c ⟩)) ⟨ d ⟩
    
  β-∀ : ∀{V c X}
      ------------------------------------------------------
    → V ⟨ `∀ c ⟩ ◯ X —→ (V ◯ X) ⟨ rename-crcn (X •ᵣ idr) c ⟩

  β-𝒢 : ∀{V c X}
      -----------------------------------------------
    → V ⟨ 𝒢 c ⟩ ◯ X —→ V ⟨ rename-crcn (X •ᵣ idr) c ⟩

  cast-ℐ : ∀{V c}
      -----------------------------------------------------
    → (V ⟨ ℐ c ⟩) —→ ν ★ · (((rename-ty suc V) ◯ 0) ⟨ c ⟩)

  cast-id : ∀ {V}
      -------------
    → V ⟨ id ⟩ —→ V

  cast-collapse : ∀{V G}
      -----------------------
    → V ⟨ G ! ⟩ ⟨ G `? ⟩ —→ V

  cast-conflict : ∀{V G H}
    → G ≢ H
      ---------------------------
    → V ⟨ G ! ⟩ ⟨ H `? ⟩ —→ blame

  cast-⨟ : ∀{V c d}
      ----------------------------
    → V ⟨ c ⨟ d ⟩ —→ V ⟨ c ⟩ ⟨ d ⟩

{- TODO: add non-pure reduction that handles nu binders -}

⌈_⌉ : Grnd → Type
⌈ ★⇒★ ⌉ = ★ ⇒ ★
⌈ `ℕ ⌉ = `ℕ
⌈ ` X ⌉ = ` X

data Cat : Set where
  typ : Cat
  bind : Type → Cat

ren-cat : Rename → Cat → Cat
ren-cat ρ typ = typ
ren-cat ρ (bind A) = bind (ren-ty ρ A)

Context : Set
Context = List Cat × List Type

nth : ∀{A : Set} → List A → Var → Maybe A
nth [] zero = nothing
nth (A ∷ Γ) zero = just A
nth [] (suc x) = nothing
nth (A ∷ Γ) (suc x) = nth Γ x

{-- Lookup a term variable --}

infix 4 _∋_⦂_

_∋_⦂_ : List Type → Var → Type → Set 
Γ ∋ x ⦂ A = (nth Γ x ≡ just A)

data _∋_:=_ : List Cat → Var → Cat → Set where
  catZ : ∀ {Δ C} → (C ∷ Δ) ∋ 0 := C
  castS : ∀ {Δ C C′ C↑ X}
    → Δ ∋ X := C
    → C↑ ≡ ren-cat suc C
    → (C′ ∷ Δ) ∋ suc X := C↑

{-- Well-Formed Types --}

infix 4 _⊢_

data _⊢_ : List Cat → Type → Set where
  ⊢-ℕ : ∀{Δ} → Δ ⊢ `ℕ
  ⊢-★ : ∀{Δ} → Δ ⊢ ★
  ⊢-X :  ∀{Δ X C} → Δ ∋ X := C → Δ ⊢ ` X
  ⊢-⇒ : ∀{Δ A B} → Δ ⊢ A → Δ ⊢ B → Δ ⊢ (A ⇒ B)
  ⊢-∀ : ∀{Δ A} → typ ∷ Δ ⊢ A → Δ ⊢ `∀ A

{-- Well-Typed Coercions --}

infix 4 _⊢_⦂_⇨_

data _⊢_⦂_⇨_ : List Cat → Crcn → Type → Type → Set where
  ⊢-id : ∀{Δ A}
    → Δ ⊢ A
    → Δ ⊢ id ⦂ A ⇨ A
  ⊢-! : ∀{Δ G} → Δ ⊢ G ! ⦂ ⌈ G ⌉ ⇨ ★
  ⊢-? : ∀{Δ G} → Δ ⊢ G `? ⦂ ★ ⇨ ⌈ G ⌉
  ⊢-↦ : ∀{Δ c d A B C D}
    → Δ ⊢ c ⦂ C ⇨ A
    → Δ ⊢ d ⦂ B ⇨ D
      -------------------------------
    → Δ ⊢ (c ↦ d) ⦂ (A ⇒ B) ⇨ (C ⇒ D)
  ⊢-⨟ : ∀{Δ c d A B C}
    → Δ ⊢ c ⦂ A ⇨ B
    → Δ ⊢ d ⦂ B ⇨ C
      -----------------
    → Δ ⊢ c ⨟ d ⦂ A ⇨ C
  ⊢-↓ : ∀{Δ X A}
    → Δ ∋ X := bind A
      -------------------
    → Δ ⊢ X ↓ ⦂ A ⇨ (` X)
  ⊢-↑ : ∀{Δ X A}
    → Δ ∋ X := bind A
      -------------------
    → Δ ⊢ X ↑ ⦂ (` X) ⇨ A
  ⊢-𝒢 : ∀{Δ c A B}
    → (typ ∷ Δ) ⊢ c ⦂ ren-ty suc A ⇨ B
      --------------------------------
    → Δ ⊢ (𝒢 c) ⦂ A ⇨ (`∀ B)
  ⊢-ℐ : ∀{Δ c A B}
    → (bind ★ ∷ Δ) ⊢ c ⦂ A ⇨ ren-ty suc B
      ------------------------------------
    → Δ ⊢ (ℐ c) ⦂ (`∀ A) ⇨ B
  ⊢-∀ : ∀{Δ c A B}
    → (typ ∷ Δ) ⊢ c ⦂ A ⇨ B
      -----------------------------
    → Δ ⊢ (`∀ c) ⦂ (`∀ A) ⇨ (`∀ B)


{----- Type System --------}

infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Expr → Type → Set where

  ⊢-⟨⟩ : ∀{Δ Γ M c A B}
    → (Δ , Γ) ⊢ M ⦂ A
    → Δ ⊢ c ⦂ A ⇨ B
      ---------------------
    → (Δ , Γ) ⊢ M ⟨ c ⟩ ⦂ B

  ⊢-var : ∀{Δ Γ x A}
    → Γ ∋ x ⦂ A
      -----------------
    → (Δ , Γ) ⊢ ` x ⦂ A

  ⊢-Λ : ∀{Δ Γ V A}
    → (typ ∷ Δ , map (ren-ty suc) Γ) ⊢ V ⦂ A
    → Value V
      --------------------
    → (Δ , Γ) ⊢ Λ V ⦂ `∀ A
  
  ⊢-◯ : ∀{Γ M X A}
    → Γ ⊢ M ⦂ `∀ A
      -------------------------------
    → Γ ⊢ M ◯ X ⦂ ren-ty (X •ᵣ idr) A

  ⊢-ν : ∀{Δ Γ A N B}
    → (bind A ∷ Δ , map (ren-ty suc) Γ) ⊢ N ⦂ ren-ty suc B
      ----------------------------------------------------
    → (Δ , Γ) ⊢ ν A · N ⦂ B

  ⊢-ƛ : ∀{Δ Γ N A B}
    → (Δ , A ∷ Γ) ⊢ N ⦂ B
      ---------------------
    → (Δ , Γ) ⊢ ƛ N ⦂ A ⇒ B

  ⊢-· : ∀{Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

rename-val : ∀ {V ρ}
  → Value V
  → Value (rename ρ V)
rename-val V-ƛ = V-ƛ
rename-val V-# = V-#
rename-val (V-Λ v) = V-Λ (rename-val v)
rename-val (V-! v) = V-! (rename-val v)
rename-val (V-↦ v) = V-↦ (rename-val v)
rename-val (V-𝒢 v) = V-𝒢 (rename-val v)
rename-val (V-∀ v) = V-∀ (rename-val v)

-- Well-typed Term Variable Renaming
_⦂_⇒_ : Rename → List Type  → List Type → Set
ρ ⦂ Γ₁ ⇒ Γ₂ = ∀ x A → Γ₁ ∋ x ⦂ A → Γ₂ ∋ ρ x ⦂ A

extr-pres : ∀ {ρ Γ₁ Γ₂ A}
  → ρ ⦂ Γ₁ ⇒ Γ₂
  → extr ρ ⦂ (A ∷ Γ₁) ⇒ (A ∷ Γ₂)
extr-pres ρ⦂ zero B refl = refl
extr-pres ρ⦂ (suc x) B ∋x = ρ⦂ x B ∋x

nth-just-map : ∀ {A : Set}{xs : List A}{i : ℕ}{x : A}{f : A → A}
  → nth xs i ≡ just x
  → nth (map f xs) i ≡ just (f x)
nth-just-map {xs = []} {zero} ()
nth-just-map {xs = []} {suc i} ()
nth-just-map {xs = x ∷ xs} {zero} refl = refl
nth-just-map {xs = x ∷ xs} {suc i} nth-xs = nth-just-map{xs = xs}{i} nth-xs

just-injective : ∀{A : Set}{x y : A}
  → just x ≡ just y
  → x ≡ y
just-injective refl = refl

id-type : (A : Type) → Type
id-type A = A

var-injective : ∀{x y : ℕ}
  → ` x ≡ id-type (` y)
  → x ≡ y
var-injective refl = refl

fun-injective : ∀{A₁ A₂ B₁ B₂}
  → A₁ ⇒ A₂ ≡ B₁ ⇒ B₂
  → A₁ ≡ B₁ × A₂ ≡ B₂
fun-injective refl = refl , refl

all-injective : ∀{A B}
  → `∀ A ≡ id-type (`∀ B)
  → A ≡ B
all-injective refl = refl

nth-map-just2 : ∀ {A : Set}{xs : List A}{i : ℕ}{y : A}{f : A → A}
  → nth (map f xs) i ≡ just y
  → Σ[ x ∈ A ] nth xs i ≡ just x × f x ≡ y
nth-map-just2 {xs = []} {zero} ()
nth-map-just2 {xs = []} {suc i} ()
nth-map-just2 {xs = x ∷ xs} {zero} refl = x , refl , refl
nth-map-just2 {xs = x ∷ xs} {suc i} eq = nth-map-just2{xs = xs} eq
  
nth-map-just : ∀ {A : Set}{xs : List A}{i : ℕ}{x : A}{f : A → A}
  → nth (map f xs) i ≡ just (f x)
  → (∀ a b → f a ≡ f b → a ≡ b)
  → nth xs i ≡ just x
nth-map-just {xs = []} {zero} () f-inj
nth-map-just {xs = []} {suc i} () f-inj
nth-map-just {A}{xs = x ∷ xs} {zero}{y}{f} nth-map f-inj =
  let fxy : f x ≡ f y
      fxy = just-injective nth-map in
  cong just (f-inj _ _ fxy)
nth-map-just {xs = x ∷ xs} {suc i} nth-map f-inj =
  nth-map-just{xs = xs}{i} nth-map f-inj

⟰ᵣ-injective : ∀ ρ
  → (∀ x y → ρ x ≡ ρ y → x ≡ y)
  → (∀ x y → ⟰ᵣ ρ x ≡ ⟰ᵣ ρ y → x ≡ y)
⟰ᵣ-injective ρ ρ-inj x y eq =
  let ρx=ρy = suc-injective eq in
  ρ-inj x y ρx=ρy

extr-injective : ∀ ρ
  → (∀ x y → ρ x ≡ ρ y → x ≡ y)
  → (∀ x y → extr ρ x ≡ extr ρ y → x ≡ y)
extr-injective ρ ρ-inj zero zero eq = refl
extr-injective ρ ρ-inj (suc x) (suc y) eq =
  cong suc (⟰ᵣ-injective ρ ρ-inj x y eq)

ren-ty-inj : ∀ ρ {A B}
  → (∀ x y → ρ x ≡ ρ y → x ≡ y)
  → ren-ty ρ A ≡ ren-ty ρ B
  → A ≡ B
ren-ty-inj ρ {`ℕ} {`ℕ} inj refl = refl
ren-ty-inj ρ {★} {★} inj refl = refl
ren-ty-inj ρ {` x} {` y} inj eq = cong `_ (inj x y (var-injective eq))
ren-ty-inj ρ {A₁ ⇒ A₂} {B₁ ⇒ B₂} inj eq
  with fun-injective eq
... | eq1 , eq2
  with ren-ty-inj ρ inj eq1 | ren-ty-inj ρ inj eq2
... | refl | refl = refl
ren-ty-inj ρ {`∀ A} {`∀ B} inj eq =
  let extr-inj = extr-injective ρ inj in
  let AB = all-injective eq in
  let IH = ren-ty-inj (extr ρ) {A}{B} extr-inj AB in
  cong `∀_ IH

ren-ty-suc-inj : ∀ {A B}
  → ren-ty suc A ≡ ren-ty suc B
  → A ≡ B
ren-ty-suc-inj {A}{B} eq =
  ren-ty-inj suc {A}{B} (λ x y eq → suc-injective eq) eq

rename-typ-pres : ∀ {ρ Γ₁ Γ₂}
  → ρ ⦂ Γ₁ ⇒ Γ₂
  → ρ ⦂ map (ren-ty suc) Γ₁ ⇒ map (ren-ty suc) Γ₂
rename-typ-pres {ρ} {Γ₁} {Γ₂} ρ⦂ x A ∋x
    with nth-map-just2{xs = Γ₁} ∋x
... | A , nth-x , refl =
    let nth-ρx = ρ⦂ x A nth-x in
    let nth-ren-ρx = nth-just-map{xs = Γ₂} {f = ren-ty suc} nth-ρx in
    nth-ren-ρx

rename-pres : ∀ Γ₁ Γ₂ Δ ρ M A
  → ρ ⦂ Γ₁ ⇒ Γ₂
  → (Δ , Γ₁) ⊢ M ⦂ A
  → (Δ , Γ₂) ⊢ rename ρ M ⦂ A
rename-pres Γ₁ Γ₂ Δ ρ (` x) A ρ⦂ (⊢-var ∋x) = ⊢-var (ρ⦂ x A ∋x)
rename-pres Γ₁ Γ₂ Δ ρ (ƛ N) C ρ⦂ (⊢-ƛ{A = A}{B} N⦂A) =
  let IH = rename-pres (A ∷ Γ₁) (A ∷ Γ₂) Δ (extr ρ) N B (extr-pres ρ⦂) N⦂A in
  ⊢-ƛ IH
rename-pres Γ₁ Γ₂ Δ ρ (L · M) B ρ⦂ (⊢-·{A = A}{B} L⦂AB M⦂B) =
  ⊢-· (rename-pres Γ₁ Γ₂ Δ ρ L (A ⇒ B) ρ⦂ L⦂AB)
      (rename-pres Γ₁ Γ₂ Δ ρ M A ρ⦂ M⦂B)
rename-pres Γ₁ Γ₂ Δ ρ (Λ N) A ρ⦂ (⊢-Λ{A = B} N⦂A v) = 
 let IH = rename-pres (map (ren-ty suc) Γ₁) (map (ren-ty suc) Γ₂) (typ ∷ Δ) ρ N B
           (rename-typ-pres{ρ = ρ}{Γ₁}{Γ₂} ρ⦂) N⦂A
 in ⊢-Λ IH (rename-val v)
rename-pres Γ₁ Γ₂ Δ ρ (M ◯ X) A ρ⦂ (⊢-◯ M⦂A) = ⊢-◯ (rename-pres Γ₁ Γ₂ Δ ρ M (`∀ _) ρ⦂ M⦂A)
rename-pres Γ₁ Γ₂ Δ ρ (ν B · N) A ρ⦂ (⊢-ν N⦂A) =
  let IH = rename-pres (map (ren-ty suc) Γ₁) (map (ren-ty suc) Γ₂) (bind B ∷ Δ) ρ N (ren-ty suc A)
            (rename-typ-pres{ρ = ρ}{Γ₁}{Γ₂} ρ⦂) N⦂A in
  ⊢-ν IH
rename-pres Γ₁ Γ₂ Δ ρ (M ⟨ c ⟩) B ρ⦂ (⊢-⟨⟩{A = A} M⦂A c⦂) =
  ⊢-⟨⟩ (rename-pres Γ₁ Γ₂ Δ ρ M A ρ⦂ M⦂A) c⦂

-- Well-typed Term Variable Substitution
_⊢_⦂_⤇_ : List Cat → Subst → List Type  → List Type → Set
Δ ⊢ σ ⦂ Γ₁ ⤇ Γ₂ = ∀ x A → Γ₁ ∋ x ⦂ A → (Δ , Γ₂) ⊢ σ x ⦂ A

exts-pres : ∀ {σ Δ Γ₁ Γ₂ A}
  → Δ ⊢ σ ⦂ Γ₁ ⤇ Γ₂
  → Δ ⊢ exts σ ⦂ (A ∷ Γ₁) ⤇ (A ∷ Γ₂)
exts-pres σ⦂ zero A ∋x = ⊢-var ∋x
exts-pres {σ}{Δ}{Γ₁}{Γ₂}{A} σ⦂ (suc x) B ∋x =
  let σx⦂A = σ⦂ x B ∋x in
  rename-pres Γ₂ (A ∷ Γ₂) Δ suc (σ x) B (λ x₁ A₁ z → z) σx⦂A

-- Well-typed Type Variable Renaming
{-
data ⊢_⦂_⇒_ : Rename → List Cat → List Cat → Set where
  ⊢idr : ∀ {Δ₂} → ⊢ idr ⦂ [] ⇒ Δ₂
  ⊢extr : ∀ {ρ Δ₁ Δ₂ C}
    → ⊢ ρ ⦂ Δ₁ ⇒ Δ₂
    → ⊢ extr ρ ⦂ (C ∷ Δ₁) ⇒ (C ∷ Δ₂)
  ⊢cons : ∀{ρ Δ₁ Δ₂ Y}
    → ⊢ ρ ⦂ Δ₁ ⇒ Δ₂
    → Δ₂ ⊢ ` Y
    → ⊢ Y •ᵣ ρ ⦂ (typ ∷ Δ₁) ⇒ Δ₂
-}
⊢_⦂_⇒_ : Rename → List Cat → List Cat → Set
⊢ ρ ⦂ Δ₁ ⇒ Δ₂ = ∀ x C → Δ₁ ∋ x := C → Δ₂ ∋ ρ x := ren-cat ρ C

postulate extr-suc-commute : ∀{ρ B} → (ren-ty (extr ρ) (ren-ty suc B)) ≡ (ren-ty suc (ren-ty ρ B))

postulate extr-typ-pres : ∀ {ρ Δ₁ Δ₂} → ⊢ ρ ⦂ Δ₁ ⇒ Δ₂ → ⊢ extr ρ ⦂ (typ ∷ Δ₁) ⇒ (typ ∷ Δ₂)
-- extr-typ-pres ρ⦂ = ?
-- extr-typ-pres ρ⦂ zero C catZ = catZ
-- extr-typ-pres ρ⦂ (suc X) typ (castS {C = typ} ∋X eq) =
--   castS (ρ⦂ X typ ∋X) eq
-- extr-typ-pres {ρ} ρ⦂ (suc X) (bind A) (castS {C = bind B} ∋X refl) =
--   castS (ρ⦂ X (bind B) ∋X) (cong bind (extr-suc-commute{ρ}{B}))

postulate extr-cat-pres : ∀ {ρ Δ₁ Δ₂ C} → ⊢ ρ ⦂ Δ₁ ⇒ Δ₂ → ⊢ extr ρ ⦂ (C ∷ Δ₁) ⇒ (C ∷ Δ₂)
-- extr-cat-pres ρ⦂ zero typ catZ = catZ
-- extr-cat-pres ρ⦂ zero (bind A) catZ =
  
--   {!!}
-- extr-cat-pres ρ⦂ (suc x) C′ ∋x = {!!}

ren-ty-pres  : ∀{ρ Δ₁ Δ₂ A}
  → ⊢ ρ ⦂ Δ₁ ⇒ Δ₂
  → Δ₁ ⊢ A
  → Δ₂ ⊢ ren-ty ρ A
ren-ty-pres {ρ} {Δ₁} {Δ₂} {A} ρ⦂ ⊢-ℕ = ⊢-ℕ
ren-ty-pres {ρ} {Δ₁} {Δ₂} {A} ρ⦂ ⊢-★ = ⊢-★
ren-ty-pres {ρ} {Δ₁} {Δ₂} {A} ρ⦂ (⊢-X{X = X}{C} ∋X) = ⊢-X (ρ⦂ X C ∋X)
ren-ty-pres {ρ} {Δ₁} {Δ₂} {A} ρ⦂ (⊢-⇒ ⊢A ⊢B) = ⊢-⇒ (ren-ty-pres ρ⦂ ⊢A) (ren-ty-pres ρ⦂ ⊢B)
ren-ty-pres {ρ} {Δ₁} {Δ₂} {A} ρ⦂ (⊢-∀ ⊢A) = ⊢-∀ (ren-ty-pres (extr-typ-pres ρ⦂) ⊢A)

rename-crcn-pres : ∀{ρ Δ₁ Δ₂ c A B}
  → ⊢ ρ ⦂ Δ₁ ⇒ Δ₂
  → Δ₁ ⊢ c ⦂ A ⇨ B
  → Δ₂ ⊢ rename-crcn ρ c ⦂ (ren-ty ρ A) ⇨ (ren-ty ρ B)
rename-crcn-pres ρ⦂ (⊢-id wf) = ⊢-id (ren-ty-pres ρ⦂ wf)
rename-crcn-pres ρ⦂ (⊢-! {G = ★⇒★}) = ⊢-!
rename-crcn-pres ρ⦂ (⊢-! {G = `ℕ}) = ⊢-!
rename-crcn-pres ρ⦂ (⊢-! {G = ` X}) = ⊢-!
rename-crcn-pres ρ⦂ (⊢-? {G = ★⇒★}) = ⊢-?
rename-crcn-pres ρ⦂ (⊢-? {G = `ℕ}) = ⊢-?
rename-crcn-pres ρ⦂ (⊢-? {G = ` x}) = ⊢-?
rename-crcn-pres ρ⦂ (⊢-↦ c⦂ d⦂) = ⊢-↦ (rename-crcn-pres ρ⦂ c⦂) (rename-crcn-pres ρ⦂ d⦂)
rename-crcn-pres ρ⦂ (⊢-⨟ c⦂ d⦂) = ⊢-⨟ (rename-crcn-pres ρ⦂ c⦂) (rename-crcn-pres ρ⦂ d⦂)
rename-crcn-pres ρ⦂ (⊢-↓{X = X}{A} ∋X) =
  let ∋ρX = ρ⦂ X (bind A) ∋X in
  ⊢-↓ ∋ρX
rename-crcn-pres ρ⦂ (⊢-↑{X = X}{A} ∋X) =
  let ∋ρX = ρ⦂ X (bind A) ∋X in
  ⊢-↑ ∋ρX
rename-crcn-pres {ρ}{Δ₁}{Δ₂} ρ⦂ (⊢-𝒢{A = A} c⦂)
    with rename-crcn-pres {extr ρ}{typ ∷ Δ₁}{typ ∷ Δ₂} (extr-typ-pres ρ⦂) c⦂
... | IH rewrite extr-suc-commute{ρ}{A} =
     ⊢-𝒢 IH
rename-crcn-pres {ρ}{Δ₁}{Δ₂} ρ⦂ (⊢-ℐ{A = A} c⦂)
    with rename-crcn-pres {extr ρ}{bind ★ ∷ Δ₁}{bind ★ ∷ Δ₂} {!!} c⦂
... | IH =
    ⊢-ℐ {!!}
rename-crcn-pres ρ⦂ (⊢-∀ c⦂) = ⊢-∀ {!!}

rename-ty-pres : ∀{ρ Δ₁ Δ₂ Γ M A}
  → ⊢ ρ ⦂ Δ₁ ⇒ Δ₂
  → (Δ₁ , Γ) ⊢ M ⦂ A
  → (Δ₂ , map (ren-ty ρ) Γ) ⊢ rename-ty ρ M ⦂ ren-ty ρ A
rename-ty-pres ρ⦂ (⊢-⟨⟩{A = A}{B} M⦂A c⦂) = ⊢-⟨⟩ (rename-ty-pres ρ⦂ M⦂A) {!!}
rename-ty-pres ρ⦂ (⊢-var x) = {!!}
rename-ty-pres ρ⦂ (⊢-Λ M⦂A x) = {!!}
rename-ty-pres ρ⦂ (⊢-◯ M⦂A) = {!!}
rename-ty-pres ρ⦂ (⊢-ν M⦂A) = {!!}
rename-ty-pres ρ⦂ (⊢-ƛ M⦂A) = {!!}
rename-ty-pres ρ⦂ (⊢-· M⦂A M⦂A₁) = {!!}


⟰ᵗ-pres : ∀ {σ Δ Γ₁ Γ₂}
  → Δ ⊢ σ ⦂ Γ₁ ⤇ Γ₂
  → (typ ∷ Δ) ⊢ ⟰ᵗ σ ⦂ map (ren-ty suc) Γ₁ ⤇ map (ren-ty suc) Γ₂
  -- ⟰ᵗ σ x = rename-ty suc (σ x)
⟰ᵗ-pres {σ}{Δ}{Γ₁}{Γ₂} σ⦂ x A ∋x = {!!}

sub-pres : ∀ Γ₁ Γ₂ Δ σ M A
  → Δ ⊢ σ ⦂ Γ₁ ⤇ Γ₂
  → (Δ , Γ₁) ⊢ M ⦂ A
  → (Δ , Γ₂) ⊢ sub σ M ⦂ A
sub-pres Γ₁ Γ₂ Δ σ (` x) A σ⦂ (⊢-var ∋x) = σ⦂ x A ∋x
sub-pres Γ₁ Γ₂ Δ σ (ƛ N) (A ⇒ B) σ⦂ (⊢-ƛ{A = A} N⦂B) =
    ⊢-ƛ (sub-pres (A ∷ Γ₁) (A ∷ Γ₂) Δ (exts σ) N B (exts-pres σ⦂) N⦂B)
sub-pres Γ₁ Γ₂ Δ σ (L · M) B σ⦂ (⊢-·{A = A} L⦂A→B M⦂A) =
    ⊢-· (sub-pres Γ₁ Γ₂ Δ σ L (A ⇒ B) σ⦂ L⦂A→B) (sub-pres Γ₁ Γ₂ Δ σ M A σ⦂ M⦂A)
sub-pres Γ₁ Γ₂ Δ σ (Λ V) (`∀ A) σ⦂ (⊢-Λ V⦂A v) =
  let IH = sub-pres {!!} {!!} (typ ∷ Δ) {!!} V A {!!} V⦂A in
  ⊢-Λ IH {!!}
sub-pres Γ₁ Γ₂ Δ σ (M ◯ X) A σ⦂ (⊢-◯ M⦂A) = {!!}
sub-pres Γ₁ Γ₂ Δ σ (ν X · N) A σ⦂ M⦂A = {!!}
sub-pres Γ₁ Γ₂ Δ σ (M ⟨ c ⟩) A σ⦂ M⦂A = {!!}


preservation : ∀ Γ M N A
  → M —→ N
  → Γ ⊢ M ⦂ A
  → Γ ⊢ N ⦂ A
preservation Γ M N A (ξ M→N) M⦂A = {!!}
preservation Γ M N A (β-ƛ w) M⦂A = {!!}
preservation Γ M N A β-Λ M⦂A = {!!}
preservation Γ M N A β-↦ M⦂A = {!!}
preservation Γ M N A β-∀ M⦂A = {!!}
preservation Γ M N A β-𝒢 M⦂A = {!!}
preservation Γ M N A cast-ℐ M⦂A = {!!}
preservation Γ M N A cast-id M⦂A = {!!}
preservation Γ M N A cast-collapse M⦂A = {!!}
preservation Γ M N A (cast-conflict x) M⦂A = {!!}
preservation Γ M N A cast-⨟ M⦂A = {!!}

