Phil's revision of Jeremy's work on System S.

  (Original is EfficientGroundCoercions.agda)

  This module formalizes the λS calculus (Siek, Thiemann, Wadler 2015)
  and proves type safety via progress and preservation. The calculus
  uses Henglein's coercions to represent casts, and acheive space
  efficiency.

  This module is relatively small because it reuses the definitions
  and proofs from the Efficient Parameterized Cast Calculus. This
  module just has to provide the appropriate parameters, the most
  important of which is the compose function, written ⨟.

## Imports

\begin{code}
module CoercionsS where

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
    using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
\end{code}

## Types

\begin{code}
  infix  7 _⇒_
  infix  6 `_
  infix  5 _⨟_


  data Type : Set where
    ★ : Type
    ι : Type
    _⇒_ : Type → Type → Type

  data Ground : Type → Set where
    G-Base : Ground ι
    G-Fun : Ground (★ ⇒ ★)

  data Base : Type → Set where
    B-Base : Base ι

\end{code}

## Labels

\begin{code}
  data Label : Set where
    pos : ℕ → Label
    neg : ℕ → Label

  flip : Label → Label
  flip (pos ℓ) = (neg ℓ)
  flip (neg ℓ) = (pos ℓ)
\end{code}

## Syntax of casts

The mutually recursive data types sCast, iCast, and gCast define a
normal form for coercions, following the grammar in Figure 5 of Siek,
Thiemann, and Wadler (2015).  Each cast is indexed by a pair of source
and target types, called SrcTrg.

\begin{code}
  infix 6 _——→_

  data SrcTrg : Set where
    _——→_ : Type → Type → SrcTrg

  data sCast : SrcTrg → Set
  data iCast : SrcTrg → Set
  data gCast : SrcTrg → Set

  data sCast where

    id★ :
         --------------
         sCast (★ ——→ ★)

    _??_⨟_ : ∀{B}
       → (G : Type)
       → Label
       → iCast (G ——→ B) 
       → {_ : Ground G}
         --------------
       → sCast (★ ——→ B)

    `_ : ∀{A B}
       → iCast (A ——→ B)
         ---------------
       → sCast (A ——→ B)

  data iCast where

    _⨟_!! : ∀{A}
       → (G : Type)
       → gCast (A ——→ G)
       → {_ : Ground G}
         ---------------
       → iCast (A ——→ ★)

    `_ : ∀{A B}
       → gCast (A ——→ B)
         ---------------
       → iCast (A ——→ B)

    ⊥_⟨_⟩_ :
         (G : Type)
       → (H : Type)
       → Label
       → {_ : Ground G}
       → {_ : Ground H}
         ---------------
       → iCast (G ——→ H)

  data gCast where

    idι : ∀ {ι : Type}
       → {_ : Base ι}
         ---------------
       → gCast (ι ——→ ι)

    _⇒_ : ∀ {A B A′ B′}
      → sCast (A′ ——→ A)
      → sCast (B ——→ B′)
        -------------------------
      → gCast (A ⇒ B ——→ A′ ⇒ B′)

\end{code}

## Composition

\begin{code}
  _⨟_ : ∀ {A B C}
    → sCast (A ——→ B)
    → sCast (B ——→ C)
      ---------------
    → sCast (A ——→ C)
  ` ` idι ⨟ ` ` idι =  ` ` idι
  _  = {!!}
\end{code}
