\begin{code}[hide]
{-# OPTIONS --rewriting #-}
module LogRel.PeterPrecision where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Var
open import Sig
open import LogRel.PeterCastCalculus
open import StepIndexedLogic
\end{code}

\section{Precision on Types and Terms}
\label{sec:precision}

To talk about the gradual guarantee, we first define when one type is
less precise than another one. The following definition says that the
unknown type ★ is less precise than any other type.

\begin{code}
infixr 6 _⊑_
data _⊑_ : Type → Type → Set where
  unk⊑unk : ★ ⊑ ★
  unk⊑ : ∀{G}{B} → ⌈ G ⌉ ⊑ B → ★ ⊑ B
  base⊑ : ∀{ι} → $ₜ ι ⊑ $ₜ ι
  fun⊑ : ∀{A B C D}  →  A ⊑ C  →  B ⊑ D  →  A ⇒ B ⊑ C ⇒ D
\end{code}

The first two rules for precision are usually presented as a single
rule that says ★ is less precise than any type.  Instead we have
separated out the case for when both types are ★ from the case when
only the less-precise type is ★.  Also, for the rule \textsf{unk⊑},
instead of writing $B ≢ ★$ we have written $⌈ G ⌉ ⊑ B$, which turns
out to be important later when we define the logical relation and use
recursion on the precision relation.
%
The \textsf{Prec} type bundles two types in the precision relation and
of course, precision is reflexive.

\begin{code}
Prec : Set
Prec = (∃[ A ] ∃[ B ] A ⊑ B)

Refl⊑ : ∀{A} → A ⊑ A
\end{code}
\begin{code}[hide]
Refl⊑ {★} = unk⊑unk
Refl⊑ {$ₜ ι} = base⊑
Refl⊑ {A ⇒ B} = fun⊑ Refl⊑ Refl⊑
\end{code}

\begin{code}[hide]
unk⊑gnd-inv : ∀{G}
   → (c : ★ ⊑ ⌈ G ⌉)
   → ∃[ d ] c ≡ unk⊑{G}{⌈ G ⌉} d
unk⊑gnd-inv {$ᵍ ι} (unk⊑ {$ᵍ .ι} base⊑) = base⊑ , refl
unk⊑gnd-inv {★⇒★} (unk⊑ {★⇒★} (fun⊑ c d)) = fun⊑ c d , refl

dyn-prec-unique : ∀{A}
  → (c : ★ ⊑ A)
  → (d : ★ ⊑ A)
  → c ≡ d
dyn-prec-unique {★} unk⊑unk unk⊑unk = refl
dyn-prec-unique {★} unk⊑unk (unk⊑ {$ᵍ ι} ())
dyn-prec-unique {★} unk⊑unk (unk⊑ {★⇒★} ())
dyn-prec-unique {★} (unk⊑ {$ᵍ ι} ()) d
dyn-prec-unique {★} (unk⊑ {★⇒★} ()) d
dyn-prec-unique {$ₜ ι} (unk⊑ {$ᵍ .ι} base⊑) (unk⊑ {$ᵍ .ι} base⊑) = refl
dyn-prec-unique {A ⇒ A₁} (unk⊑ {★⇒★} (fun⊑ c c₁)) (unk⊑ {★⇒★} (fun⊑ d d₁))
    with dyn-prec-unique c d | dyn-prec-unique c₁ d₁
... | refl | refl = refl

gnd-prec-unique : ∀{G A}
   → (c : ⌈ G ⌉ ⊑ A)
   → (d : ⌈ G ⌉ ⊑ A)
   → c ≡ d
gnd-prec-unique {$ᵍ ι} {.($ₜ ι)} base⊑ base⊑ = refl
gnd-prec-unique {★⇒★} {.(_ ⇒ _)} (fun⊑ c c₁) (fun⊑ d d₁)
    with dyn-prec-unique c d | dyn-prec-unique c₁ d₁
... | refl | refl = refl
\end{code}

Figure~\ref{fig:term-precision} defines the precision relation on
terms.  The judgment has the form $Γ ⊩ M ⊑ M′ ⦂ c$ where Γ is a list
of precision-related types and $c : A ⊑ A′$ is a precision derivation
for the types of $M$ and $M′$. There are two rules for injection and
also for projection, allowing either to appear on the left or right
across from an arbitrary term. However, when injection is on the
right, the term on the left must have type ★ (rule
\textsf{⊑-inj-R}).  Similarly, when projection is on the right, the
term on the left must have type ★ (rule \textsf{⊑-proj-R}).

\begin{figure}[tbp]
\begin{code}
infix 3 _⊩_⊑_⦂_
data _⊩_⊑_⦂_ : List Prec → Term → Term → ∀{A B : Type} → A ⊑ B → Set  where
  ⊑-var : ∀ {Γ x A⊑B}  →  Γ ∋ x ⦂ A⊑B  →  Γ ⊩ (` x) ⊑ (` x) ⦂ proj₂ (proj₂ A⊑B)
  ⊑-lit : ∀ {Γ c} →  Γ ⊩ ($ c) ⊑ ($ c) ⦂ base⊑{typeof c}
  ⊑-app : ∀{Γ L M L′ M′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → Γ ⊩ L ⊑ L′ ⦂ fun⊑ c d  →  Γ ⊩ M ⊑ M′ ⦂ c
     → Γ ⊩ L · M ⊑ L′ · M′ ⦂ d
  ⊑-lam : ∀{Γ N N′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → (A , C , c) ∷ Γ ⊩ N ⊑ N′ ⦂ d  →  Γ ⊩ ƛ N ⊑ ƛ N′ ⦂ fun⊑ c d
  ⊑-inj-L : ∀{Γ M M′}{G B}{c : ⌈ G ⌉ ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ c  →  Γ ⊩ M ⟨ G !⟩ ⊑ M′ ⦂ unk⊑{G}{B} c
  ⊑-inj-R : ∀{Γ M M′}{G}{c : ★ ⊑ ⌈ G ⌉}
     → Γ ⊩ M ⊑ M′ ⦂ c  →  Γ ⊩ M ⊑ M′ ⟨ G !⟩ ⦂ unk⊑unk
  ⊑-proj-L : ∀{Γ M M′ H B}{c : ⌈ H ⌉ ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑ c  →  Γ ⊩ M ⟨ H ?⟩ ⊑ M′ ⦂ c
  ⊑-proj-R : ∀{Γ M M′ H}{c : ★ ⊑ ⌈ H ⌉}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑unk  →  Γ ⊩ M ⊑ M′ ⟨ H ?⟩  ⦂ c
  ⊑-blame : ∀{Γ M A}  →  map proj₁ Γ ⊢ M ⦂ A  →  Γ ⊩ M ⊑ blame ⦂ Refl⊑{A}
\end{code}
\caption{Precision Relation on Terms}
\label{fig:term-precision}
\end{figure}

With precision defined, we are ready to discuss the gradual guarantee.
It states that if $M$ is less precise than $M′$, then $M$ and $M′$
behave in a similar way, as defined below by the predicate
$\mathsf{gradual}\,M\,M′$. In particular, it says that the
less-precise term behaves exactly like the more-precise term. On the
other hand the more-precise term may reduce to \textsf{blame} even
though the less-precise term does not.

\begin{code}
gradual : (M M′ : Term) → Set
gradual M M′ = (M′ ⇓ → M ⇓) × (M′ ⇑ → M ⇑) × (M ⇓ → M′ ⇓ ⊎ M′ ↠ blame)
    × (M ⇑ → M′ ⇑⊎blame) × (M ↠ blame → M′ ↠ blame)
\end{code}
