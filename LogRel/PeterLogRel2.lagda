\begin{code}[hide]
{-# OPTIONS --rewriting --prop #-}
module LogRel.PeterLogRel2 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (true; false; _≟_) renaming (Bool to 𝔹)
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
open import LogRel.PeterPrecision
open import StepIndexedLogic2
open import Exists using (cong-∃)
open import PropP
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
all smaller numbers (monotonicity). Each of the constructors for SIL
formulas proves these two properties, thereby saving the client of SIL
from these tedious proofs.

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
\textsf{fixpointᵒ} is an adaptation of the fixpoint theorem of Appel
and McAllester~\cite{Appel:2001aa}.

\begin{code}
_ : ∀(A : Set) (P : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A)
    → μᵒ P a ≡ᵒ letᵒ (μᵒ P) (P a)
_ = λ A P a → fixpointᵒ P a
\end{code}


\section{A Logical Relation for Precision}
\label{sec:log-rel}

\begin{code}[hide]
data Dir : Set where
  ≼ : Dir
  ≽ : Dir
\end{code}

To define a logical relation for precision, we adapt the logical
relation of New~\cite{New:2020ab}, which used explicit step indexing,
into the Step-Indexed Logic. So the logical relation has two
directions (of type \textsf{Dir}): the ≼ direction has the
less-precise term taking the lead whereas the ≽ direction has the
more-precise term in the lead.
%
In addition, the logical relation consists of mutually-recursive
relations on both terms and values. SIL does not directly support
mutual recursion, but it can be expressed by combining the two
relations into a single relation whose input is a disjoint sum.  The
formula for expressing membership in these recursive relations is
verbose, so we define the below shorthands.

\begin{code}
Γ₁ : Context
Γ₁ = ((Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)) ∷ []

_∣_ᵒ⊑ᴸᴿᵀ_⦂_ : Dir → Term → Term → ∀{A}{A′} (c : A ⊑ A′) → Setᵒ Γ₁ (Now ∷ [])
dir ∣ M ᵒ⊑ᴸᴿᵀ M′ ⦂ c = (inj₂ ((_ , _ , c) , dir , M , M′)) ∈ recᵒ

_∣_ᵒ⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A}{A′} (c : A ⊑ A′) → Setᵒ Γ₁ (Now ∷ [])
dir ∣ V ᵒ⊑ᴸᴿᵥ V′ ⦂ c = (inj₁ ((_ , _ , c) , dir , V , V′)) ∈ recᵒ
\end{code}
\begin{code}[hide]
instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

eqLit : (c : Lit) → (c′ : Lit) → Dec (c ≡ c′)
eqLit (Num x) (Num y)
    with Data.Nat._≟_ x y
... | yes refl = yes refl
... | no neq  = no λ {refl → neq refl}
eqLit (Num x) (Bool b) = no (λ ())
eqLit (Bool b) (Num x) = no (λ ())
eqLit (Bool b) (Bool b′)
    with Data.Bool._≟_ b b′
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
\end{code}

\begin{code}
data LRᵥCases : {A A′ : Type} → (c : A ⊑ A′) → Term → Term → Set where
  LRᵥ-base⊑ : ∀{ι c} → LRᵥCases (base⊑{ι}) ($ c) ($ c)
  LRᵥ-fun⊑ : ∀{A B A′ B′}{c d}{N N′} → LRᵥCases (fun⊑{A}{B}{A′}{B′} c d) (ƛ N) (ƛ N′)
  LRᵥ-unk⊑unk : ∀{G V V′} → LRᵥCases unk⊑unk (V ⟨ G !⟩) (V′ ⟨ G !⟩)
  LRᵥ-unk⊑ : ∀{G A′ V V′}{c : ⌈ G ⌉ ⊑ A′} → LRᵥCases (unk⊑ c) (V ⟨ G !⟩) V′

dec-LRᵥCases : ∀ {A A′ : Type} → (c : A ⊑ A′) → (M M′ : Term) → Dec (LRᵥCases c M M′)
\end{code}
\begin{code}[hide]
dec-LRᵥCases unk⊑unk ($ k) M = no λ { ()}
dec-LRᵥCases unk⊑unk (` x) M′ = no λ { ()}
dec-LRᵥCases unk⊑unk (ƛ N) M′ = no λ { ()}
dec-LRᵥCases unk⊑unk (L · M) M′ = no λ { ()}
dec-LRᵥCases unk⊑unk (M ⟨ G !⟩) ($ k) = no λ { ()}
dec-LRᵥCases unk⊑unk (M ⟨ G !⟩) (` x) = no λ { ()}
dec-LRᵥCases unk⊑unk (M ⟨ G !⟩) (ƛ N) = no λ { ()}
dec-LRᵥCases unk⊑unk (M ⟨ G !⟩) (L′ · M′) = no λ { ()}
dec-LRᵥCases unk⊑unk (M ⟨ G !⟩) (M′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = yes LRᵥ-unk⊑unk
... | no neq = no λ { LRᵥ-unk⊑unk → neq refl}
dec-LRᵥCases unk⊑unk (M ⟨ G !⟩) (M′ ⟨ H ?⟩) = no λ { ()}
dec-LRᵥCases unk⊑unk (M ⟨ G !⟩) blame = no λ { ()}
dec-LRᵥCases unk⊑unk (M ⟨ H ?⟩) M′ = no λ { ()}
dec-LRᵥCases unk⊑unk blame M′ = no λ { ()}

dec-LRᵥCases (unk⊑ c) ($ k) M′ = no λ { ()}
dec-LRᵥCases (unk⊑ c) (` x) M′ = no λ { ()}
dec-LRᵥCases (unk⊑ c) (ƛ N) M′ = no λ { ()}
dec-LRᵥCases (unk⊑ c) (L · M) M′ = no λ { ()}
dec-LRᵥCases (unk⊑{H} c) (M ⟨ G !⟩) M′
    with G ≡ᵍ H
... | yes refl = yes LRᵥ-unk⊑
... | no neq = no λ { LRᵥ-unk⊑ → neq refl}
dec-LRᵥCases (unk⊑ c) (M ⟨ H ?⟩) M′ = no λ { ()}
dec-LRᵥCases (unk⊑ c) blame M′ = no λ { ()}

dec-LRᵥCases base⊑ ($ k) ($ k′)
    with eqLit k k′
... | yes refl  = yes LRᵥ-base⊑
... | no neq = no λ { LRᵥ-base⊑ → neq refl}
dec-LRᵥCases base⊑ ($ k) (` x) = no λ { ()}
dec-LRᵥCases base⊑ ($ k) (ƛ N′) = no λ { ()}
dec-LRᵥCases base⊑ ($ k) (L′ · M′) = no λ { ()}
dec-LRᵥCases base⊑ ($ k) (M′ ⟨ G !⟩) = no λ { ()}
dec-LRᵥCases base⊑ ($ k) (M′ ⟨ H ?⟩) = no λ { ()}
dec-LRᵥCases base⊑ ($ k) blame = no λ { ()}
dec-LRᵥCases base⊑ (` x) M′ = no λ { ()}
dec-LRᵥCases base⊑ (ƛ N) M′ = no λ { ()}
dec-LRᵥCases base⊑ (L · M) M′ = no λ { ()}
dec-LRᵥCases base⊑ (M ⟨ G !⟩) M′ = no λ { ()}
dec-LRᵥCases base⊑ (M ⟨ H ?⟩) M′ = no λ { ()}
dec-LRᵥCases base⊑ blame M′ = no λ { ()}

dec-LRᵥCases (fun⊑ c d) ($ k) M′ = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (` x) M′ = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (ƛ N) ($ k) = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (ƛ N) (` x) = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (ƛ N) (ƛ N′) = yes LRᵥ-fun⊑
dec-LRᵥCases (fun⊑ c d) (ƛ N) (L′ · M′) = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (ƛ N) (M′ ⟨ G !⟩) = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (ƛ N) (M′ ⟨ H ?⟩) = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (ƛ N) blame = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (L · M) M′ = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (M ⟨ G !⟩) M′ = no λ { ()}
dec-LRᵥCases (fun⊑ c d) (M ⟨ H ?⟩) M′ = no λ { ()}
dec-LRᵥCases (fun⊑ c d) blame M′ = no λ { ()}
\end{code}

\begin{figure}[tbp]
\begin{code}
LRᵀ : ∀{A B} → (A ⊑ B) → Dir → Term → Term → Setᵒ Γ₁ (Later ∷ [])
pre-LRᵥ : ∀{A B} → (c : A ⊑ B) → Dir → (V : Term) → (V′ : Term) → LRᵥCases c V V′ → Setᵒ Γ₁ (Later ∷ [])

LRᵥ : ∀{A B} → (c : A ⊑ B) → Dir → (V : Term) → (V′ : Term) → Setᵒ Γ₁ (Later ∷ [])
LRᵥ A⊑B dir V V′
    with dec-LRᵥCases A⊑B V V′
... | yes cs = pre-LRᵥ A⊑B dir V V′ cs
... | no ncs = ⊥ᵒ

LRᵀ A⊑A′ ≼ M M′ =
   (∃ᵒ[ N ] (M ⟶ N)ᵒ ×ᵒ ▷ᵒ (≼ ∣ N ᵒ⊑ᴸᴿᵀ M′ ⦂ A⊑A′))
   ⊎ᵒ (M′ ↠ blame)ᵒ
   ⊎ᵒ ((Value M)ᵒ ×ᵒ (∃ᵒ[ V′ ] (M′ ↠ V′)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ LRᵥ A⊑A′ ≼ M V′))
LRᵀ A⊑A′ ≽ M M′ =
   (∃ᵒ[ N′ ] (M′ ⟶ N′)ᵒ ×ᵒ ▷ᵒ (≽ ∣ M ᵒ⊑ᴸᴿᵀ N′ ⦂ A⊑A′))
   ⊎ᵒ (Blame M′)ᵒ
   ⊎ᵒ ((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M ↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ (LRᵥ A⊑A′ ≽ V M′)))

pre-LRᵥ {.($ᵀ ι)}{.($ᵀ ι)} (base⊑{ι}) dir ($ c) ($ c′) (LRᵥ-base⊑{ι}{c}) = (c ≡ c′) ᵒ
pre-LRᵥ {.(A ⇒ B)} {.(A′ ⇒ B′)} (fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir (ƛ N)(ƛ N′) (LRᵥ-fun⊑{c = A⊑A′}{B⊑B′}{N}{N′}) =
    ∀ᵒ[ W ] ∀ᵒ[ W′ ] ▷ᵒ (dir ∣ W ᵒ⊑ᴸᴿᵥ W′ ⦂ A⊑A′)
                  →ᵒ ▷ᵒ (dir ∣ (N [ W ]) ᵒ⊑ᴸᴿᵀ (N′ [ W′ ]) ⦂ B⊑B′) 
pre-LRᵥ {★}{★} unk⊑unk dir (V ⟨ G !⟩) (V′ ⟨ G !⟩) (LRᵥ-unk⊑unk{G}{V}{V′}) =
    (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (▷ᵒ (dir ∣ V ᵒ⊑ᴸᴿᵥ V′ ⦂ Refl⊑{⌈ G ⌉}))
pre-LRᵥ {★}{A′} (unk⊑{G} G⊑A′) ≼ (V ⟨ G !⟩) V′ (LRᵥ-unk⊑{G}{A′}{V}{V′}{G⊑A′}) =
    (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (≼ ∣ V ᵒ⊑ᴸᴿᵥ V′ ⦂ G⊑A′)
pre-LRᵥ {★}{A′} (unk⊑{G} H⊑A′) ≽ (V ⟨ G !⟩) V′ (LRᵥ-unk⊑{G}{A′}{V}{V′}{G⊑A′}) =
    (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (LRᵥ H⊑A′ ≽ V V′)
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

The following definitions combine the LRᵥ and LRᵀ functions into a
single function, pre-LRᵀ⊎LRᵥ, and than applies the μᵒ operator to
produce the recursive relation LRᵀ⊎LRᵥ. Finally, we define some
shorthand for the logical relation on values, written ⊑ᴸᴿᵥ, and the
logical relation on terms, ⊑ᴸᴿᵀ.

\begin{code}
pre-LRᵀ⊎LRᵥ : ((Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term))
   → Setᵒ Γ₁ (Later ∷ [])
pre-LRᵀ⊎LRᵥ (inj₁ (c , dir , V , V′)) = LRᵥ (proj₂ (proj₂ c)) dir V V′ 
pre-LRᵀ⊎LRᵥ (inj₂ (c , dir , M , M′)) = LRᵀ (proj₂ (proj₂ c)) dir M M′

LRᵀ⊎LRᵥ : ((Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)) → Setᵒ [] []
LRᵀ⊎LRᵥ X = μᵒ pre-LRᵀ⊎LRᵥ X

_∣_⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ [] []
dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ = LRᵀ⊎LRᵥ (inj₁ ((_ , _ , A⊑A′) , dir , V , V′))

_∣_⊑ᴸᴿᵀ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ [] []
dir ∣ M ⊑ᴸᴿᵀ M′ ⦂ A⊑A′ = LRᵀ⊎LRᵥ (inj₂ ((_ , _ , A⊑A′) , dir , M , M′))

_⊑ᴸᴿᵀ_⦂_ : Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ [] []
M ⊑ᴸᴿᵀ M′ ⦂ A⊑A′ = (≼ ∣ M ⊑ᴸᴿᵀ M′ ⦂ A⊑A′) ×ᵒ (≽ ∣ M ⊑ᴸᴿᵀ M′ ⦂ A⊑A′)
\end{code}

The relations that we have defined so far, ⊑ᴸᴿᵥ and ⊑ᴸᴿᵀ, only apply
to closed terms, that is, terms with no free variables.  We also need
to relate open terms. The standard way to do that is to apply two
substitutions to the two terms, replacing each free variable with
related values. We relate a pair of substitutions γ and γ′ with the
following definition, which says that the substitutions must be
point-wise related using the logical relation for values.

\begin{code}
_∣_⊨_⊑ᴸᴿ_ : (Γ : List Prec) → Dir → Subst → Subst → List (Setᵒ [] [])
[] ∣ dir ⊨ γ ⊑ᴸᴿ γ′ = []
((_ , _ , A⊑A′) ∷ Γ) ∣ dir ⊨ γ ⊑ᴸᴿ γ′ =
    (dir ∣ (γ 0) ⊑ᴸᴿᵥ (γ′ 0) ⦂ A⊑A′) ∷ (Γ ∣ dir ⊨ (λ x → γ (suc x)) ⊑ᴸᴿ (λ x → γ′ (suc x)))
\end{code}

We then define two open terms $M$ and $M′$ to be logically related
if there are a pair of related substitutions $γ$ and $γ′$ such that
applying them to $M$ and $M′$ produces related terms.

\begin{code}
_∣_⊨_⊑ᴸᴿ_⦂_ : List Prec → Dir → Term → Term → Prec → Prop
Γ ∣ dir ⊨ M ⊑ᴸᴿ M′ ⦂ (_ , _ , A⊑A′) = ∀ (γ γ′ : Subst)
   → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿᵀ (⟪ γ′ ⟫ M′) ⦂ A⊑A′
\end{code}

We use the following notation for the conjunction of the two
directions and define the \textsf{proj} function for accessing each
direction.

\begin{code}
_⊨_⊑ᴸᴿ_⦂_ : List Prec → Term → Term → Prec → Prop
Γ ⊨ M ⊑ᴸᴿ M′ ⦂ c = (Γ ∣ ≼ ⊨ M ⊑ᴸᴿ M′ ⦂ c) ×ₚ (Γ ∣ ≽ ⊨ M ⊑ᴸᴿ M′ ⦂ c)

proj : ∀ {Γ}{c} → (dir : Dir) → (M M′ : Term) → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ c → Γ ∣ dir ⊨ M ⊑ᴸᴿ M′ ⦂ c
proj ≼ M M′ M⊑M′ = proj₁ₚ M⊑M′
proj ≽ M M′ M⊑M′ = proj₂ₚ M⊑M′
\end{code}

\begin{code}[hide]
LRᵀ-def : ∀{A}{A′} → (A⊑A′ : A ⊑ A′) → Dir → Term → Term → Setᵒ [] []
LRᵀ-def A⊑A′ ≼ M M′ =
   (∃ᵒ[ N ] (M ⟶ N)ᵒ ×ᵒ ▷ᵒ (≼ ∣ N ⊑ᴸᴿᵀ M′ ⦂ A⊑A′))
   ⊎ᵒ (M′ ↠ blame)ᵒ
   ⊎ᵒ ((Value M)ᵒ ×ᵒ (∃ᵒ[ V′ ] (M′ ↠ V′)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (≼ ∣ M ⊑ᴸᴿᵥ V′ ⦂ A⊑A′)))
LRᵀ-def A⊑A′ ≽ M M′ =
   (∃ᵒ[ N′ ] (M′ ⟶ N′)ᵒ ×ᵒ ▷ᵒ (≽ ∣ M ⊑ᴸᴿᵀ N′ ⦂ A⊑A′))
   ⊎ᵒ (Blame M′)ᵒ
   ⊎ᵒ ((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M ↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ (≽ ∣ V ⊑ᴸᴿᵥ M′ ⦂ A⊑A′)))
\end{code}
\begin{code}[hide]
LRᵀ-stmt : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}
   → dir ∣ M ⊑ᴸᴿᵀ M′ ⦂ A⊑A′ ≡ᵒ LRᵀ-def A⊑A′ dir M M′
\end{code}
\begin{code}[hide]
LRᵀ-stmt {A}{A′}{A⊑A′}{dir}{M}{M′} =
  dir ∣ M ⊑ᴸᴿᵀ M′ ⦂ A⊑A′                   ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-LRᵀ⊎LRᵥ (X₂ dir)                  ⩦⟨ fixpointᵒ pre-LRᵀ⊎LRᵥ (X₂ dir) ⟩
  letᵒ (μᵒ pre-LRᵀ⊎LRᵥ) (pre-LRᵀ⊎LRᵥ (X₂ dir)) ⩦⟨ EQ {dir} ⟩
  LRᵀ-def A⊑A′ dir M M′                    ∎
  where
  c = (A , A′ , A⊑A′)
  X₂ = λ dir → inj₂ (c , dir , M , M′)
  EQ : ∀{dir} → letᵒ (μᵒ pre-LRᵀ⊎LRᵥ) (pre-LRᵀ⊎LRᵥ (X₂ dir)) ≡ᵒ LRᵀ-def A⊑A′ dir M M′
  EQ {≼} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
           (cong-∃ᵒ λ V′ → cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
           ((≡ᵒ-sym (fixpointᵒ pre-LRᵀ⊎LRᵥ (inj₁ (c , ≼ , M , V′))))))))) 
  EQ {≽} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
             (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ᵒ λ V → cong-×ᵒ (≡ᵒ-refl refl)
              (cong-×ᵒ (≡ᵒ-refl refl)
                (≡ᵒ-sym (fixpointᵒ pre-LRᵀ⊎LRᵥ (inj₁ (c , ≽ , V , M′))))))))
\end{code}

The definition of \textsf{pre-LRᵥ} included several clauses that
ensured that the related values are indeed syntactic values. Here we
make use of that to prove that indeed, logically related values are
syntactic values.

\begin{code}
LRᵥ⇒Valueᵒ : ∀ {dir}{A}{A′}{𝒫} (A⊑A′ : A ⊑ A′) M M′
   → 𝒫 ⊢ᵒ (dir ∣ M ⊑ᴸᴿᵥ M′ ⦂ A⊑A′) → 𝒫 ⊢ᵒ (Value M)ᵒ ×ᵒ (Value M′)ᵒ
\end{code}
\begin{code}[hide]
LRᵥ⇒Valueᵒ {dir}{A}{A′}{𝒫} A⊑A′ M M′ M⊑M′ = aux{A = A}{A′}{A⊑A′} un-M⊑M′
  where
  un-M⊑M′ : 𝒫 ⊢ᵒ letᵒ (μᵒ pre-LRᵀ⊎LRᵥ) (LRᵥ A⊑A′ dir M M′)
  un-M⊑M′ = unfoldᵒ pre-LRᵀ⊎LRᵥ (inj₁ ((A , A′ , A⊑A′) , dir , M , M′)) M⊑M′

  aux : ∀ {𝒫}{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}{dir} → 𝒫 ⊢ᵒ letᵒ (μᵒ pre-LRᵀ⊎LRᵥ) (LRᵥ{A}{A′} A⊑A′ dir M M′)
      → 𝒫 ⊢ᵒ (Value M)ᵒ ×ᵒ (Value M′)ᵒ
  aux{𝒫}{A}{A′}{A⊑A′}{M}{M′}{dir} M⊑M′
      with dec-LRᵥCases A⊑A′ M M′
  ... | no ncs = ⊥-elimᵒ M⊑M′ ((Value M ᵒ) ×ᵒ (Value M′ ᵒ))
  ... | yes LRᵥ-base⊑ = pureᵒI ($̬ _) ,ᵒ pureᵒI ($̬ _)
  ... | yes LRᵥ-fun⊑ = pureᵒI (ƛ̬ _) ,ᵒ pureᵒI (ƛ̬ _)
  ... | yes LRᵥ-unk⊑unk = pureᵒE (proj₁ᵒ M⊑M′) λ v →
                          pureᵒE (proj₁ᵒ (proj₂ᵒ M⊑M′)) λ w →
                          pureᵒI (v 〈 _ 〉) ,ᵒ pureᵒI (w 〈 _ 〉)
  ... | yes LRᵥ-unk⊑
      with dir
  ... | ≼ = pureᵒE (proj₁ᵒ M⊑M′) λ v →
            pureᵒE (proj₁ᵒ (proj₂ᵒ M⊑M′)) λ w →
            pureᵒI (v 〈 _ 〉) ,ᵒ pureᵒI w
  ... | ≽ = pureᵒE (proj₁ᵒ M⊑M′) λ v →
            pureᵒE (proj₁ᵒ (proj₂ᵒ M⊑M′)) λ w →
            pureᵒI (v 〈 _ 〉) ,ᵒ pureᵒI w
\end{code}


If two values are related via ⊑ᴸᴿᵥ, then they are also related via
⊑ᴸᴿᵀ.

\begin{code}
LRᵥ⇒LRᵀ : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{𝒫}{V V′}{dir}
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′  →  𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿᵀ V′ ⦂ A⊑A′
\end{code}
\begin{code}[hide]
LRᵥ⇒LRᵀ {A}{A′}{A⊑A′}{𝒫}{V}{V′}{dir} ⊢𝒱VV′ =
    foldᵒ pre-LRᵀ⊎LRᵥ (inj₂ ((A , A′ , A⊑A′) , dir , V , V′)) (aux ⊢𝒱VV′)
  where
  VV : 𝒫 ⊢ᵒ (Value V ᵒ) ×ᵒ (Value V′ ᵒ)
  VV = LRᵥ⇒Valueᵒ A⊑A′ V V′ ⊢𝒱VV′
  
  aux : ∀{dir} → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′
      → 𝒫 ⊢ᵒ letᵒ (μᵒ pre-LRᵀ⊎LRᵥ) (LRᵀ A⊑A′ dir V V′)
  aux {≼} ⊢𝒱VV′ =
    inj₂ᵒ (inj₂ᵒ ((proj₁ᵒ VV) ,ᵒ ∃ᵒI V′ (pureᵒI (V′ END) ,ᵒ ((proj₂ᵒ VV) ,ᵒ
    unfoldᵒ pre-LRᵀ⊎LRᵥ (inj₁ ((A , A′ , A⊑A′) , ≼ , V , V′)) ⊢𝒱VV′))))
  aux {≽} ⊢𝒱VV′ =
    inj₂ᵒ (inj₂ᵒ (proj₂ᵒ VV ,ᵒ ∃ᵒI V (pureᵒI (V END) ,ᵒ (proj₁ᵒ VV ,ᵒ
    unfoldᵒ pre-LRᵀ⊎LRᵥ (inj₁ ((A , A′ , A⊑A′) , ≽ , V , V′)) ⊢𝒱VV′))))
\end{code}

