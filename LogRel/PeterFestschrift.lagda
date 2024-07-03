\begin{code}[hide]
{-# OPTIONS --rewriting #-}
module LogRel.PeterFestschrift where

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
terms.  The judgement has the form $Γ ⊩ M ⊑ M′ ⦂ c$ where Γ is a list
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
gradual M M′ = (M′ ⇓ → M ⇓) × (M′ ⇑ → M ⇑)
    × (M ⇓ → M′ ⇓ ⊎ M′ ↠ blame) × (M ⇑ → M′ ⇑⊎blame) × (M ↠ blame → M′ ↠ blame)
\end{code}

\section{Step-Indexed Logic}
\label{sec:SIL}

The Step-Indexed Logic (SIL) library~\cite{Siek:2023aa} is a shallow
embedding of a modal logic into Agda. The formulas of this logic have
type \textsf{Setᵒ}, which is a record with three fields, the most
important of which is named \textsf{\#} and is a function from ℕ to
\textsf{Set} which expresses the meaning of the formula in Agda.
Think of the ℕ as a count-down clock, with smaller numbers
representing later points in time. The other two fields of the record
contain proofs of the LSLR invariants: (1) that the formula is true at
0, and (2) if the formula is true at some number, then it is true at
all smaller numbers.

SIL includes the connectives of first-order logic (conjunction,
disjunction, existential and universal quantification, etc.).

What makes SIL special is that it includes an operator μᵒ for defining
recursive predicates. In the body of the μᵒ, de Bruijn index 0 refers
to itself, that is, the entire μᵒ. However, variable 0 may only be
used ``later'', that is, underneath at least one use of the modal
operator ▷ᵒ.  The formula in the body of a μᵒ has type
$\mathsf{Set}ˢ\,Γ\,Δ$, where $Γ$ gives the type for each recursive
predicate in scope and $Δ$ records when each recursive predicate is
used (now or later). \textsf{Setˢ} is a record whose field \textsf{\#}
is a function from a list of step-indexed predicates to \textsf{Setᵒ}.
The majority of the lines of code in the SIL library are dedicated to
proving the \textsf{fixpointᵒ} theorem, which states that a recursive
predicate is equivalent to one unrolling of itself. The proof of
\textsf{fixpointᵒ}is an adaptation of the fixpoint theorem of Appel
and McAllester~\cite{Appel:2001aa}.

\begin{code}
_ : ∀(A : Set) (P : A → Setˢ (A ∷ []) (cons Later ∅)) (a : A)
    → μᵒ P a ≡ᵒ # (P a) (μᵒ P , ttᵖ)
_ = λ A P a → fixpointᵒ P a
\end{code}


\section{A Logical Relation for Precision}
\label{sec:log-rel}

To define a logical relation for precision, we adapt the logical
relation of New~\cite{New:2020ab}, which used explicit step indexing,
into the Step-Indexed Logic. So the logical relation has two directions:
the ≼ direction has the less-precise term taking the lead whereas the
≽ direction has the more-precise term in the lead.

\begin{code}
data Dir : Set where
  ≼ : Dir
  ≽ : Dir
\end{code}

In addition, the logical relation consists of mutually-recursive
relations on both terms and values. SIL does not directly support
mutual recursion, but that can be expressed by combining the two
relations into a single relation whose input is a disjoint sum.  The
formula for expressing membership in these recursive relations is
verbose, so we define the below shorthands.

\begin{code}
LR-type : Set
LR-type = (Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)

LR-ctx : Context
LR-ctx = LR-type ∷ []

_∣_ˢ⊑ᴸᴿₜ_⦂_ : Dir → Term → Term → ∀{A}{A′} (c : A ⊑ A′) → Setˢ LR-ctx (cons Now ∅)
dir ∣ M ˢ⊑ᴸᴿₜ M′ ⦂ c = (inj₂ ((_ , _ , c) , dir , M , M′)) ∈ zeroˢ

_∣_ˢ⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A}{A′} (c : A ⊑ A′) → Setˢ LR-ctx (cons Now ∅)
dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ c = (inj₁ ((_ , _ , c) , dir , V , V′)) ∈ zeroˢ
\end{code}
\begin{code}[hide]
instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }
\end{code}

\begin{figure}[tbp]
\begin{code}
LRₜ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)
LRᵥ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)

LRₜ (A , A′ , c) ≼ M M′ =
   (∃ˢ[ N ] (M ⟶ N)ˢ ×ˢ ▷ˢ (≼ ∣ N ˢ⊑ᴸᴿₜ M′ ⦂ c))
   ⊎ˢ (M′ ↠ blame)ˢ
   ⊎ˢ ((Value M)ˢ ×ˢ (∃ˢ[ V′ ] (M′ ↠ V′)ˢ ×ˢ (Value V′)ˢ ×ˢ (LRᵥ (_ , _ , c) ≼ M V′)))
LRₜ (A , A′ , c) ≽ M M′ =
   (∃ˢ[ N′ ] (M′ ⟶ N′)ˢ ×ˢ ▷ˢ (≽ ∣ M ˢ⊑ᴸᴿₜ N′ ⦂ c))
   ⊎ˢ (Blame M′)ˢ
   ⊎ˢ ((Value M′)ˢ ×ˢ (∃ˢ[ V ] (M ↠ V)ˢ ×ˢ (Value V)ˢ ×ˢ (LRᵥ (_ , _ , c) ≽ V M′)))

LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir ($ c) ($ c′) = (c ≡ c′) ˢ
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir V V′ = ⊥ ˢ
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir (ƛ N)(ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (dir ∣ W ˢ⊑ᴸᴿᵥ W′ ⦂ A⊑A′)
                  →ˢ ▷ˢ (dir ∣ (N [ W ]) ˢ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′) 
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir V V′ = ⊥ ˢ
LRᵥ (.★ , .★ , unk⊑unk) dir (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (▷ˢ (dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ Refl⊑{⌈ G ⌉}))
... | no neq = ⊥ ˢ
LRᵥ (.★ , .★ , unk⊑unk) dir V V′ = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≼ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ ▷ˢ (≼ ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ d)
... | no neq = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≽ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (LRᵥ (⌈ G ⌉ , A′ , d) ≽ V V′)
... | no neq = ⊥ ˢ
LRᵥ (★ , .A′ , unk⊑{H}{A′} d) dir V V′ = ⊥ ˢ
\end{code}

\caption{Logical Relation for Precision on Terms $\mathsf{LR}_t$
  and Values $\mathsf{LR}_v$}
\label{fig:log-rel-precision}
\end{figure}

The logical relation is defined in Figure~\ref{fig:log-rel-precision}
and explained in the following paragraphs.  The definition of the
logical relation for terms is based on the requirements of the gradual
guarantee, but it only talks about one step at a time of the leading
term. In the ≼ direction, the first clause says that the less-precise
$M$ takes a step to $N$ and that $N$ is related to $M′$ at one tick
later in time. The second clause allows the more-precise $M′$ to
reduce to an error. The third clause says that the less-precise $M$ is
already a value, and requires $M′$ to reduce to a value that is
related to $M$. The other direction ≽ is defined in a similar way,
but with the more precise term $M′$ taking one step at a time.

The following definitions combine the LRᵥ and LRₜ functions into a
single function, pre-LRₜ⊎LRᵥ, and than applies the μᵒ operator to
produce the recursive relation LRₜ⊎LRᵥ. Finally, we define some
shorthand for the logical relation on values, written ⊑ᴸᴿᵥ, and the
logical relation on terms, ⊑ᴸᴿₜ.

\begin{code}
pre-LRₜ⊎LRᵥ : LR-type → Setˢ LR-ctx (cons Later ∅)
pre-LRₜ⊎LRᵥ (inj₁ (c , dir , V , V′)) = LRᵥ c dir V V′
pre-LRₜ⊎LRᵥ (inj₂ (c , dir , M , M′)) = LRₜ c dir M M′

LRₜ⊎LRᵥ : LR-type → Setᵒ
LRₜ⊎LRᵥ X = μᵒ pre-LRₜ⊎LRᵥ X

_∣_⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ = LRₜ⊎LRᵥ (inj₁ ((_ , _ , A⊑A′) , dir , V , V′))

_∣_⊑ᴸᴿₜ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = LRₜ⊎LRᵥ (inj₂ ((_ , _ , A⊑A′) , dir , M , M′))

_⊑ᴸᴿₜ_⦂_ : Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = (≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) ×ᵒ (≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′)
\end{code}

The relations that we have defined so far, ⊑ᴸᴿᵥ and ⊑ᴸᴿₜ, only apply
to closed terms, that is, terms with no free variables.  We also need
to relate open terms. The standard way to do that is to apply two
substitutions to the two terms, replacing each free variable with
related values. We relate a pair of substitutions γ and γ′ with the
following definition, which says that the substitutions must be
pointwise related using the logical relation for values.

\begin{code}
_∣_⊨_⊑ᴸᴿ_ : (Γ : List Prec) → Dir → Subst → Subst → List Setᵒ
[] ∣ dir ⊨ γ ⊑ᴸᴿ γ′ = []
((_ , _ , A⊑A′) ∷ Γ) ∣ dir ⊨ γ ⊑ᴸᴿ γ′ =
    (dir ∣ (γ 0) ⊑ᴸᴿᵥ (γ′ 0) ⦂ A⊑A′) ∷ (Γ ∣ dir ⊨ (λ x → γ (suc x)) ⊑ᴸᴿ (λ x → γ′ (suc x)))
\end{code}

We then define two open terms $M$ and $M′$ to be logically related
if there are a pair of related subtitutions $γ$ and $γ′$ such that
applying them to $M$ and $M′$ produces related terms.

\begin{code}
_∣_⊨_⊑ᴸᴿ_⦂_ : List Prec → Dir → Term → Term → Prec → Set
Γ ∣ dir ⊨ M ⊑ᴸᴿ M′ ⦂ (_ , _ , A⊑A′) = ∀ (γ γ′ : Subst)
   → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′) ⦂ A⊑A′
\end{code}

We use the following notation for the conjunction of the two
directions and define the \textsf{proj} function for accessing each
direction.

\begin{code}
_⊨_⊑ᴸᴿ_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ᴸᴿ M′ ⦂ c = (Γ ∣ ≼ ⊨ M ⊑ᴸᴿ M′ ⦂ c) × (Γ ∣ ≽ ⊨ M ⊑ᴸᴿ M′ ⦂ c)

proj : ∀ {Γ}{c} → (dir : Dir) → (M M′ : Term) → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ c → Γ ∣ dir ⊨ M ⊑ᴸᴿ M′ ⦂ c
proj ≼ M M′ M⊑M′ = proj₁ M⊑M′
proj ≽ M M′ M⊑M′ = proj₂ M⊑M′
\end{code}

\begin{code}[hide]
LRₜ-def : ∀{A}{A′} → (A⊑A′ : A ⊑ A′) → Dir → Term → Term → Setᵒ
LRₜ-def A⊑A′ ≼ M M′ =
   (∃ᵒ[ N ] (M ⟶ N)ᵒ ×ᵒ ▷ᵒ (≼ ∣ N ⊑ᴸᴿₜ M′ ⦂ A⊑A′))
   ⊎ᵒ (M′ ↠ blame)ᵒ
   ⊎ᵒ ((Value M)ᵒ ×ᵒ (∃ᵒ[ V′ ] (M′ ↠ V′)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (≼ ∣ M ⊑ᴸᴿᵥ V′ ⦂ A⊑A′)))
LRₜ-def A⊑A′ ≽ M M′ =
   (∃ᵒ[ N′ ] (M′ ⟶ N′)ᵒ ×ᵒ ▷ᵒ (≽ ∣ M ⊑ᴸᴿₜ N′ ⦂ A⊑A′))
   ⊎ᵒ (Blame M′)ᵒ
   ⊎ᵒ ((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M ↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ (≽ ∣ V ⊑ᴸᴿᵥ M′ ⦂ A⊑A′)))
\end{code}
\begin{code}[hide]
LRₜ-stmt : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}
   → dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ ≡ᵒ LRₜ-def A⊑A′ dir M M′
\end{code}
\begin{code}[hide]
LRₜ-stmt {A}{A′}{A⊑A′}{dir}{M}{M′} =
  dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′                   ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-LRₜ⊎LRᵥ (X₂ dir)                  ⩦⟨ fixpointᵒ pre-LRₜ⊎LRᵥ (X₂ dir) ⟩
  # (pre-LRₜ⊎LRᵥ (X₂ dir)) (LRₜ⊎LRᵥ , ttᵖ) ⩦⟨ EQ{dir} ⟩
  LRₜ-def A⊑A′ dir M M′                    ∎
  where
  c = (A , A′ , A⊑A′)
  X₁ : Dir → LR-type
  X₁ = λ dir → inj₁ (c , dir , M , M′)
  X₂ = λ dir → inj₂ (c , dir , M , M′)
  EQ : ∀{dir} → # (pre-LRₜ⊎LRᵥ (X₂ dir)) (LRₜ⊎LRᵥ , ttᵖ) ≡ᵒ LRₜ-def A⊑A′ dir M M′
  EQ {≼} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl) 
             (cong-∃ λ V′ → cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
              ((≡ᵒ-sym (fixpointᵒ pre-LRₜ⊎LRᵥ (inj₁ (c , ≼ , M , V′)))))))))
  EQ {≽} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ λ V → cong-×ᵒ (≡ᵒ-refl refl)
              (cong-×ᵒ (≡ᵒ-refl refl)
               (≡ᵒ-sym (fixpointᵒ pre-LRₜ⊎LRᵥ (inj₁ (c , ≽ , V , M′))))))))
\end{code}
\begin{code}[hide]
LRₜ-suc : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}{k}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k) ⇔ #(LRₜ-def A⊑A′ dir M M′) (suc k)
\end{code}
\begin{code}[hide]
LRₜ-suc {A}{A′}{A⊑A′}{dir}{M}{M′}{k} =
   ≡ᵒ⇒⇔{k = suc k} (LRₜ-stmt{A}{A′}{A⊑A′}{dir}{M}{M′})
\end{code}

The definition of ⊑ᴸᴿᵥ included several clauses that ensured that the
related values are indeed syntactic values. Here we make use of that
to prove that indeed, logically related values are syntactic values.

\begin{code}
LRᵥ⇒Value : ∀ {k}{dir}{A}{A′} (A⊑A′ : A ⊑ A′) M M′
   → # (dir ∣ M ⊑ᴸᴿᵥ M′ ⦂ A⊑A′) (suc k)  →  Value M × Value M′
\end{code}
\begin{code}[hide]
LRᵥ⇒Value {k}{dir} unk⊑unk (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
LRᵥ⇒Value {k}{≼} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    with G ≡ᵍ H
... | yes refl
    with 𝒱VGV′
... | v , v′ , _ = (v 〈 _ 〉) , v′
LRᵥ⇒Value {k}{≽} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    with G ≡ᵍ H
... | yes refl
    with 𝒱VGV′
... | v , v′ , _ = (v 〈 _ 〉) , v′
LRᵥ⇒Value {k}{dir} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    | no neq = ⊥-elim 𝒱VGV′
LRᵥ⇒Value {k}{dir} (base⊑{ι}) ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
LRᵥ⇒Value {k}{dir} (fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱VV′ =
    (ƛ̬ N) , (ƛ̬ N′)
\end{code}

If two values are related via ⊑ᴸᴿᵥ, then they are also related via
⊑ᴸᴿₜ.

\begin{code}[hide]
LRᵥ⇒LRₜ-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{V V′}{dir}{k}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′) k  →  #(dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′) k
LRᵥ⇒LRₜ-step {A}{A′}{A⊑A′}{V} {V′} {dir} {zero} 𝒱VV′k =
   tz (dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′)
LRᵥ⇒LRₜ-step {A}{A′}{A⊑A′}{V} {V′} {≼} {suc k} 𝒱VV′sk =
  ⇔-fro (LRₜ-suc{dir = ≼})
  (let (v , v′) = LRᵥ⇒Value A⊑A′ V V′ 𝒱VV′sk in
  (inj₂ (inj₂ (v , (V′ , (V′ END) , v′ , 𝒱VV′sk)))))
LRᵥ⇒LRₜ-step {A}{A′}{A⊑A′}{V} {V′} {≽} {suc k} 𝒱VV′sk =
  ⇔-fro (LRₜ-suc{dir = ≽})
  (let (v , v′) = LRᵥ⇒Value A⊑A′ V V′ 𝒱VV′sk in
  inj₂ (inj₂ (v′ , V , (V END) , v , 𝒱VV′sk)))
\end{code}
\begin{code}
LRᵥ⇒LRₜ : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{𝒫}{V V′}{dir}
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′  →  𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′
\end{code}
\begin{code}[hide]
LRᵥ⇒LRₜ {A}{A′}{A⊑A′}{𝒫}{V}{V′}{dir} ⊢𝒱VV′ = ⊢ᵒ-intro λ k 𝒫k →
  LRᵥ⇒LRₜ-step{V = V}{V′}{dir}{k} (⊢ᵒ-elim ⊢𝒱VV′ k 𝒫k)
\end{code}

