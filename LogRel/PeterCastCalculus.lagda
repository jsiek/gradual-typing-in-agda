\begin{code}[hide]
{-# OPTIONS --rewriting #-}
module LogRel.PeterCastCalculus where

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
\end{code}

\section{Cast Calculus}
\label{sec:cast-calculus}

\begin{code}[hide]
{- Base types -}

data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base

_≡$?_ : (ι : Base) → (ι′ : Base) → Dec (ι ≡ ι′)
′ℕ  ≡$? ′ℕ  =  yes refl
′ℕ  ≡$? ′𝔹  =  no (λ ())
′𝔹  ≡$? ′ℕ  =  no (λ ())
′𝔹  ≡$? ′𝔹  =  yes refl

infixr 7 _⇒_
infix  8 $ₜ_
infix  8 $ᵍ_
\end{code}

The type structure of the Cast Calculus includes base types (integer and Boolean),
function types, and the unknown type ★. The \emph{ground types} include
just the base types and function types from ★ to ★.

\begin{minipage}{0.5\textwidth}
\begin{code}
data Type : Set where
  ★ : Type
  $ₜ_ : (ι : Base) → Type
  _⇒_ : (A : Type) → (B : Type) → Type
\end{code}
\end{minipage}
\begin{minipage}{0.3\textwidth}
\begin{code}
data Ground : Set where
  $ᵍ_  : (ι : Base)  → Ground
  ★⇒★ : Ground

⌈_⌉ : Ground → Type
⌈ $ᵍ ι ⌉ = $ₜ ι
⌈ ★⇒★ ⌉ = ★ ⇒ ★
\end{code}
\end{minipage}

\begin{code}[hide]
_≡ᵍ_ : ∀ (G : Ground) (H : Ground) → Dec (G ≡ H)
($ᵍ ι) ≡ᵍ ($ᵍ ι′)
    with ι ≡$? ι′
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
($ᵍ ι) ≡ᵍ ★⇒★ = no λ ()
★⇒★ ≡ᵍ ($ᵍ ι) = no λ ()
★⇒★ ≡ᵍ ★⇒★ = yes refl
\end{code}

There are three special features in the Cast Calculus:
\begin{enumerate}
\item injection $M ⟨ G !⟩$, for casting from a ground type $G$
  to the unknown type ★,
\item projection $M ⟨ H ?⟩$, for casting from the unknown type ★
  to a ground type $H$, and
\item \textsf{blame} which represents a runtime exception if
  a projection fails.
\end{enumerate}
This Cast Calclulus differs from many of those in the literature in
that it does not include casts from one function type to another, a
choice that reduces the number of reduction rules and simplifies the
technical development.  However, casts from one function type to
another can be compiled into a combination of lambda abstractions,
injections, and projections.

We define the terms of the Cast Calculus in Agda using the Abstract
Binding Tree (ABT) library by instantiating it with an appropriate set
of operators together with a description of their arity and
variable-binding structure. To that end, the following \texttt{Op}
data type includes one constructor for each term constructor that we
have in mind for the Cast Calculus, except for variables which are
always present. The \texttt{sig} function, shown below, specifies the
variable binding structure for each operator. It returns a list of
natural numbers where ■ represents zero and ν represents
successor. The list includes one number for each subterm; the number
specifices how many variables come into scope for that subterm. Lambda
abstraction (\texttt{op-lam}) has a single subterm and brings one
variable into scope, whereas application (\texttt{op-app}) has two
subterms but does not bind any variables.

\begin{minipage}{0.3\textwidth}
\begin{code}
data Lit : Set where
  Num : ℕ → Lit
  Bool : 𝔹 → Lit
\end{code}
\end{minipage}
\begin{minipage}{0.3\textwidth}
\begin{code}
data Op : Set where
  op-lam : Op
  op-app : Op
  op-lit : Lit → Op
  op-inject : Ground → Op
  op-project : Ground → Op
  op-blame : Op
\end{code}
\end{minipage}
\begin{minipage}{0.3\textwidth}
\begin{code}
sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit c) = []
sig (op-inject G) = ■ ∷ []
sig (op-project H) = ■ ∷ []
sig (op-blame) = []
\end{code}
\end{minipage}

\noindent We instantiate the ABT library as follows, by applying it to
\texttt{Op} and \texttt{sig}. We rename the resulting \texttt{ABT}
type to \texttt{Term}.

\begin{code}
open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public
\end{code}

\noindent We define Agda patterns to give succinct syntax to the
construction of abstract binding trees.

\begin{code}
pattern ƛ N = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $ c = (op-lit c) ⦅ nil ⦆
pattern _⟨_!⟩ M G = (op-inject G) ⦅ cons (ast M) nil ⦆
pattern _⟨_?⟩ M H = (op-project H) ⦅ cons (ast M) nil ⦆
pattern blame = op-blame ⦅ nil ⦆
\end{code}

\begin{code}[hide]
{-# REWRITE sub-var #-}
\end{code}

The ABT library represents variables with de Bruijn indices and
provides a definition of parallel substitution and many theorems about
substitution. The de Bruijn indices are represented directly as
natural numbers in Agda, with the constructors \texttt{0} and
\texttt{suc} for zero and successor. It is helpful to think of a
parallel substitution as an infinite stream, or equivalently, as a
function from natural numbers (de Bruijn indices) to terms. The •
operator is stream cons, that is, it adds a term to the front of the
stream.

\begin{code}
sub-zero : ∀ {V σ} → (V • σ) 0 ≡ V
sub-zero = refl
sub-suc : ∀ {V x σ} → (V • σ) (suc x) ≡ σ x
sub-suc {V}{x}{σ} = refl
\end{code}

\noindent The ABT library provides the operator $⟪ σ ⟫ M$ for applying
a substitution to a term. Here are the equations for substitution
applied to variables, application, and lambda abstraction. The
\textsf{ext} operator transports a substitution over one variable
binder.

\begin{code}
_ : ∀ (σ : Subst) (x : ℕ) → ⟪ σ ⟫ (` x) ≡ σ x
_ = λ σ x → refl
_ : ∀ (σ : Subst) (L M : Term) → ⟪ σ ⟫ (L · M) ≡ ⟪ σ ⟫ L · ⟪ σ ⟫ M
_ = λ σ L M → refl
_ : ∀ (σ : Subst) (N : Term) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ ext σ ⟫ N)
_ = λ σ N → refl
\end{code}

\noindent The bracket notation $M [ N ]$ is defined to replace the
occurrences of variable 0 in $M$ with $N$ and decrement the other free
variables. For example,

\begin{code}
_ : ∀ (N : Term) → (` 1 · ` 0) [ N ] ≡ (` 0 · N)
_ = λ N → refl
\end{code}

\noindent Most importantly, the ABT library provides the following
theorem which is both difficult to prove and needed later for the
Compatibility Lemma for lambda abstraction.

\begin{code}
ext-sub-cons : ∀ {σ N V} → (⟪ ext σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
ext-sub-cons = refl
\end{code}

\begin{code}[hide]
{- Phil: consider ditching this and use M ≡ blame -}
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

typeof : Lit → Base
typeof (Num n) = ′ℕ
typeof (Bool b) = ′𝔹

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
\end{code}
\begin{code}[hide]
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

infixr 1 _++_
--infix  1 begin_
infix  2 _↠_
infixr 2 _⟶⟨_⟩_
infixr 2 _↠⟨_⟩_
infix  3 _END
\end{code}

Figure~\ref{fig:cast-calculus} defines the type system and reduction
for the Cast Calculus. The two rules specific to gradual typing are
\textsf{collapse} and \textsf{collide}. The \textsf{collapse} rule
states that when an injected value encounters a matching projection,
the result is the underlying value.  The \textsf{collide} says that if
the injection and projection do not match, the result is
\textsf{blame}. The reason we introduce the $M$ variable and the
equation $M ≡ V ⟨ G !⟩$ in those rules is that we ran into
difficulties with Agda when doing case analysis on reductions.  The
same is true for the ξξ and \textsf{ξξ-blame} rules.  The ξξ and
\textsf{ξξ-blame} rules handle the usual congruence rules that are
needed for reduction. The \textsf{Frame} type is a shallow
non-recursive evaluation context, representing just a single term
constructor with a hole. The notation $F[M]$ plugs term $M$ into the
hole inside $F$.

Figure~\ref{fig:cast-calculus} defines $M ⇓$ to mean that $M$
reduces to a value, $M ⇑$ to mean $M$ diverges, and $M ⇑⊎blame$
to mean that $M$ either diverges or reduces to \textsf{blame}.
(We ran into difficulties with the alternate formulation
of $(M ⇑) ⊎ (M ↠ \mathsf{blame})$ and could not prove them
equivalent.)

\begin{figure}[tbp]
\begin{code}
infix 3 _⊢_⦂_
data _⊢_⦂_ : List Type → Term → Type → Set where
  ⊢` : ∀ {Γ x A} → Γ ∋ x ⦂ A → Γ ⊢ ` x ⦂ A
  ⊢$ : ∀ {Γ} (l : Lit) → Γ ⊢ $ l ⦂ $ₜ (typeof l)
  ⊢· : ∀ {Γ L M A B} → Γ ⊢ L ⦂ (A ⇒ B) → Γ ⊢ M ⦂ A → Γ ⊢ L · M ⦂ B
  ⊢ƛ : ∀ {Γ N A B} → (A ∷ Γ) ⊢ N ⦂ B → Γ ⊢ ƛ N ⦂ (A ⇒ B)
  ⊢⟨!⟩ : ∀{Γ M G} → Γ ⊢ M ⦂ ⌈ G ⌉ → Γ ⊢ M ⟨ G !⟩ ⦂ ★
  ⊢⟨?⟩ : ∀{Γ M} → Γ ⊢ M ⦂ ★ → (H : Ground) → Γ ⊢ M ⟨ H ?⟩ ⦂ ⌈ H ⌉
  ⊢blame : ∀{Γ A} → Γ ⊢ blame ⦂ A
  
infix 2 _⟶_
data _⟶_ : Term → Term → Set where
  β : ∀ {N W} → Value W  →  (ƛ N) · W ⟶ N [ W ]
  collapse : ∀{G M V} → Value V → M ≡ V ⟨ G !⟩  →  M ⟨ G ?⟩ ⟶ V
  collide  : ∀{G H M V} → Value V → G ≢ H → M ≡ V ⟨ G !⟩ → M ⟨ H ?⟩ ⟶ blame
  ξξ : ∀ {M N M′ N′} → (F : Frame)
    → M′ ≡ F ⟦ M ⟧ → N′ ≡ F ⟦ N ⟧ → M ⟶ N → M′ ⟶ N′
  ξξ-blame : ∀ {M′} → (F : Frame) → M′ ≡ F ⟦ blame ⟧ → M′ ⟶ blame

data _↠_ : Term → Term → Set where
  _END : (M : Term)  →  M ↠ M
  _⟶⟨_⟩_ : (L : Term) {M N : Term}  →  L ⟶ M  →  M ↠ N  →  L ↠ N

len : ∀{M N : Term} → (M→N : M ↠ N) → ℕ
len (_ END) = 0
len (_ ⟶⟨ step ⟩ mstep) = suc (len mstep)

_⇓ : Term → Set
M ⇓ = ∃[ V ] (M ↠ V) × Value V
_⇑ : Term → Set
M ⇑ = ∀ k → ∃[ N ] Σ[ r ∈ M ↠ N ] k ≡ len r
_⇑⊎blame : Term → Set
M ⇑⊎blame = ∀ k → ∃[ N ] Σ[ r ∈ M ↠ N ] ((k ≡ len r) ⊎ (N ≡ blame))
\end{code}
\caption{Type System and Reduction for the Cast Calculus}
\label{fig:cast-calculus}
\end{figure}

\begin{code}[hide]
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


--begin_ : ∀ {M N : Term} → (M ↠ N) → (M ↠ N)
--begin M↠N = M↠N

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

len-concat : ∀ {L}{M}{N} (s : L ↠ M) (r : M ↠ N)
  → len (s ++ r) ≡ len s + len r
len-concat (_ END) r = refl
len-concat (_ ⟶⟨ x ⟩ s) r rewrite len-concat s r = refl


{-
would prefer to say
(M ⇑) ⊎ (M ↠ blame)
but I'm having trouble showing

lemma : ∀ M → M ⇑⊎blame → (M ⇑) ⊎ (M ↠ blame)
lemma M M⇑blame = {!!}

-}

halt : Term → Set
halt M  = (M ↠ blame) ⊎ (M ⇓)
\end{code}

\begin{code}[hide]
blame-not-value : ∀{V} → Value V → V ≡ blame → ⊥
blame-not-value {.blame} () refl

value-irreducible : ∀ {V M : Term} → Value V → ¬ (V ⟶ M)
value-irreducible v V⟶M = nope V⟶M v
   where
   nope : ∀ {V M : Term} → V ⟶ M → Value V → ⊥
   nope (ξξ (□· M) () x₁ V→M) (ƛ̬ N)
   nope (ξξ (v ·□) () x₁ V→M) (ƛ̬ N)
   nope (ξξ □⟨ G !⟩ () x₁ V→M) (ƛ̬ N)
   nope (ξξ □⟨ H ?⟩ () x₁ V→M) (ƛ̬ N)
   nope (ξξ-blame (□· M) ()) (ƛ̬ N)
   nope (ξξ-blame (v ·□) ()) (ƛ̬ N)
   nope (ξξ-blame □⟨ G !⟩ ()) (ƛ̬ N)
   nope (ξξ-blame □⟨ H ?⟩ ()) (ƛ̬ N)
   nope (ξξ (□· M) () x₁ V→M) ($̬ c)
   nope (ξξ (v ·□) () x₁ V→M) ($̬ c)
   nope (ξξ □⟨ G !⟩ () x₁ V→M) ($̬ c)
   nope (ξξ □⟨ H ?⟩ () x₁ V→M) ($̬ c)
   nope (ξξ-blame (□· M) ()) ($̬ c)
   nope (ξξ-blame (v ·□) ()) ($̬ c)
   nope (ξξ-blame □⟨ G !⟩ ()) ($̬ c)
   nope (ξξ-blame □⟨ H ?⟩ ()) ($̬ c)
   nope (ξ □⟨ G !⟩ V→M) (v 〈 g 〉) = nope V→M v
   nope (ξ-blame □⟨ _ !⟩) (() 〈 g 〉)

value-irred : ∀{V : Term} → Value V → irred V
value-irred {V} v (N , V→N) = value-irreducible v V→N

value↠ : ∀{V N : Term}
    → Value V
    → V ↠ N
    → N ≡ V
value↠ v (_ END) = refl
value↠ v (_ ⟶⟨ V⟶M ⟩ M↠N) = ⊥-elim (value-irreducible v V⟶M)

blame↠ : ∀{N}
   → blame ↠ N
   → N ≡ blame
blame↠ {.blame} (.blame END) = refl
blame↠ {N} (.blame ⟶⟨ ξξ (□· M) () x₁ x₂ ⟩ red)
blame↠ {N} (.blame ⟶⟨ ξξ (v ·□) () x₁ x₂ ⟩ red)
blame↠ {N} (.blame ⟶⟨ ξξ □⟨ G !⟩ () x₁ x₂ ⟩ red)
blame↠ {N} (.blame ⟶⟨ ξξ □⟨ H ?⟩ () x₁ x₂ ⟩ red)
blame↠ {N} (.blame ⟶⟨ ξξ-blame (□· M) () ⟩ red)
blame↠ {N} (.blame ⟶⟨ ξξ-blame (v ·□) () ⟩ red)
blame↠ {N} (.blame ⟶⟨ ξξ-blame □⟨ G !⟩ () ⟩ red)
blame↠ {N} (.blame ⟶⟨ ξξ-blame □⟨ H ?⟩ () ⟩ red)

blame-irreducible : ∀{M} → ¬ (blame ⟶ M)
blame-irreducible {M} (ξξ (□· M₁) () x₁ blame→M)
blame-irreducible {M} (ξξ (v ·□) () x₁ blame→M)
blame-irreducible {M} (ξξ □⟨ G !⟩ () x₁ blame→M)
blame-irreducible {M} (ξξ □⟨ H ?⟩ () x₁ blame→M)
blame-irreducible {.blame} (ξξ-blame (□· M) ())
blame-irreducible {.blame} (ξξ-blame (v ·□) ())
blame-irreducible {.blame} (ξξ-blame □⟨ G !⟩ ())
blame-irreducible {.blame} (ξξ-blame □⟨ H ?⟩ ())

blame-irred : ∀{M}{N}
   → Blame M
   → M ⟶ N
   → ⊥
blame-irred isBlame red = blame-irreducible red

app-multi-inv : ∀{L M N}
  → (r1 : L · M ↠ N)
  → (∃[ L′ ] (Σ[ r2 ∈ (L ↠ L′) ] (N ≡ L′ · M × len r1 ≡ len r2)))
    ⊎ (∃[ V ] ∃[ M′ ] Σ[ r2 ∈ (L ↠ V) ] (Value V × Σ[ r3 ∈ (M ↠ M′) ]
        (N ≡ V · M′ × len r1 ≡ len r2 + len r3)))
    ⊎ (∃[ V ] ∃[ W ] Σ[ r2 ∈ (L ↠ V) ] (Value V × Σ[ r3 ∈ (M ↠ W) ]
        (Value W × Σ[ r4 ∈ (V · W ↠ N) ] len r1 ≡ len r2 + len r3 + len r4)))
    ⊎ N ≡ blame
app-multi-inv {L}{M}{N} ((L · M) END) = inj₁ (L , (_ END) , refl , refl)
app-multi-inv {L} {M} {N} (.(L · M) ⟶⟨ ξξ {L}{L′} (□· _) refl refl L⟶L′ ⟩ rs)
    with app-multi-inv rs
... | inj₁ (L″ , L′→L″ , refl , eq) = inj₁ (L″ , (L ⟶⟨ L⟶L′ ⟩ L′→L″) , refl , cong suc eq)
... | inj₂ (inj₁ (V , M′ , L′→V , v , M→M′ , refl , eq)) =
      inj₂ (inj₁ (V , M′ , (L ⟶⟨ L⟶L′ ⟩ L′→V) , v , M→M′ , refl , cong suc eq))
... | inj₂ (inj₂ (inj₁ (V , W , L′→V , v , M→W , w , →N , eq))) =
      inj₂ (inj₂ (inj₁ (V , W , (L ⟶⟨ L⟶L′ ⟩ L′→V) , v , M→W , w , →N , cong suc eq)))
... | inj₂ (inj₂ (inj₂ refl)) = inj₂ (inj₂ (inj₂ refl))
app-multi-inv {V} {M} {N} (.(V · M) ⟶⟨ ξξ {N = M′} (v ·□) refl refl M⟶M′ ⟩ V·M′↠N)
    with app-multi-inv V·M′↠N
... | inj₁ (L′ , V→L′ , refl , eq)
    with value↠ v V→L′
... | refl =
    inj₂ (inj₁ (V , M′ , V→L′ , v , (M ⟶⟨ M⟶M′ ⟩ M′ END) , refl , EQ))
    where EQ : suc (len V·M′↠N) ≡ len V→L′ + 1
          EQ = trans (cong suc eq) (sym (trans (+-suc _ _) (+-identityʳ _)))
app-multi-inv {V} {M} {N} (.(V · M) ⟶⟨ ξξ (v ·□) refl refl M⟶M′ ⟩ V·M′↠N)
    | inj₂ (inj₁ (V′ , M″ , V→V′ , v′ , M′→M″ , refl , eq)) =
      inj₂ (inj₁ (V′ , M″ , V→V′ , v′ , (M ⟶⟨ M⟶M′ ⟩ M′→M″) , refl , EQ))
    where EQ : suc (len V·M′↠N) ≡ len V→V′ + suc (len M′→M″)
          EQ rewrite eq = sym (+-suc _ _)
app-multi-inv {V} {M} {N} (.(V · M) ⟶⟨ ξξ (v ·□) refl refl M⟶M′ ⟩ V·M′↠N)
    | inj₂ (inj₂ (inj₁ (V′ , W , V→V′ , v′ , M′→W , w , V′·W→N , eq ))) =
      inj₂ (inj₂ (inj₁ (V′ , W , V→V′ , v′ , (M ⟶⟨ M⟶M′ ⟩ M′→W) , w , V′·W→N , EQ)))
    where EQ : suc (len V·M′↠N) ≡ len V→V′ + suc (len M′→W) + len V′·W→N
          EQ = trans (cong suc eq) (sym (cong (λ X → X + len V′·W→N)
                                       (+-suc (len V→V′) (len M′→W))))
app-multi-inv {V} {M} {N} (.(V · M) ⟶⟨ ξξ (v ·□) refl refl M⟶M′ ⟩ V·M′↠N)
    | inj₂ (inj₂ (inj₂ refl)) = inj₂ (inj₂ (inj₂ refl))
app-multi-inv {L} {M} {N} (.(L · M) ⟶⟨ ξξ-blame (□· _) refl ⟩ rs)
    with blame↠ rs
... | refl = inj₂ (inj₂ (inj₂ refl))
app-multi-inv {L} {M} {N} (.(L · M) ⟶⟨ ξξ-blame (v ·□) refl ⟩ rs)
    with blame↠ rs
... | refl = inj₂ (inj₂ (inj₂ refl))
app-multi-inv {.(ƛ _)} {M} {N} (.(ƛ _ · M) ⟶⟨ β v ⟩ M′↠N) =
  inj₂ (inj₂ (inj₁ (ƛ _ , M , (_ END) , ƛ̬ _ , (M END) , v , (_ ⟶⟨ β v ⟩ M′↠N) , refl)))

inject-multi-inv : ∀{M N}{G}
  → (red : M ⟨ G !⟩ ↠ N)
  → (∃[ M′ ] Σ[ r1 ∈ M ↠ M′ ] (N ≡ M′ ⟨ G !⟩ × len r1 ≡ len red))
    ⊎ (∃[ V ] Σ[ r1 ∈ M ↠ V ] Value V × Σ[ r2 ∈ V ⟨ G !⟩ ↠ N ] len red ≡ len r1 + len r2)
    ⊎ N ≡ blame
inject-multi-inv {M} (.(_ ⟨ _ !⟩) END) = inj₁ (M , (_ END) , refl , refl)
inject-multi-inv (.(_ ⟨ _ !⟩) ⟶⟨ ξξ □⟨ G !⟩ refl refl r1 ⟩ r2)
    with inject-multi-inv r2
... | inj₁ (M′ , →M′ , eq , eqlen) = inj₁ (_ , (_ ⟶⟨ r1 ⟩ →M′) , eq , cong suc eqlen)
... | inj₂ (inj₁ (V , →V , v , →N , eqlen)) = inj₂ (inj₁ (_ , (_ ⟶⟨ r1 ⟩ →V) , v , →N , cong suc eqlen))
... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
inject-multi-inv (.(_ ⟨ _ !⟩) ⟶⟨ ξξ-blame □⟨ G !⟩ x ⟩ red)
    with blame↠ red
... | refl = inj₂ (inj₂ refl)

project-multi-inv2 : ∀{M N}{G}
  → (red : M ⟨ G ?⟩ ↠ N)
  → (∃[ M′ ] Σ[ r1 ∈ M ↠ M′ ] (N ≡ M′ ⟨ G ?⟩ × len r1 ≡ len red))
    ⊎ (∃[ V ] Σ[ r1 ∈ M ↠ V ] Value V × Σ[ r2 ∈ V ⟨ G ?⟩ ↠ N ] len red ≡ len r1 + len r2)
    ⊎ N ≡ blame
project-multi-inv2 (.(_ ⟨ _ ?⟩) END) = inj₁ (_ , (_ END) , refl , refl)
project-multi-inv2 (.(_ ⟨ _ ?⟩) ⟶⟨ ξξ □⟨ H ?⟩ refl refl r ⟩ rs)
    with project-multi-inv2 rs
... | inj₁ (M′ , M→M′ , refl , eq) = inj₁ (M′ , (_ ⟶⟨ r ⟩ M→M′) , refl , cong suc eq)
... | inj₂ (inj₁ (V , M→V , v , Vg→N , eq)) = inj₂ (inj₁ (V , (_ ⟶⟨ r ⟩ M→V ) , v , Vg→N , cong suc eq))
... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
project-multi-inv2 (.(_ ⟨ _ ?⟩) ⟶⟨ ξξ-blame □⟨ H ?⟩ refl ⟩ rs)
    with blame↠ rs
... | refl = inj₂ (inj₂ refl)
project-multi-inv2 (.(_ ⟨ _ ?⟩) ⟶⟨ collapse v refl ⟩ rs) =
    inj₂ (inj₁ ((_ ⟨ _ !⟩) , (_ END) , (v 〈 _ 〉) , (_ ⟶⟨ collapse v refl ⟩ rs) , refl))
project-multi-inv2 (.(_ ⟨ _ ?⟩) ⟶⟨ collide v neq refl ⟩ rs) =
    inj₂ (inj₁ ((_ ⟨ _ !⟩) , (_ END) , (v 〈 _ 〉) , (_ ⟶⟨ collide v neq refl ⟩ rs) , refl))

app-inv-left : ∀{L M N}
  → (r1 : L · M ↠ N)
  → irred N
    --------------------------
  → (∃[ L′ ] Σ[ r2 ∈ (L ↠ L′) ] irred L′
        × Σ[ r3 ∈ (L′ · M ↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
app-inv-left {L} {M} {.(L · M)} (.(L · M) END) irredN =
    inj₁ (L , (_ END) , IL , (_ END) , refl)
    where IL : irred L
          IL (L′ , L→L′) = ⊥-elim (irredN (_ , (ξ (□· M) L→L′)))
app-inv-left {L} {M} {N} (.(L · M) ⟶⟨ ξ (□· M₁) r1 ⟩ r2) irredN
    with app-inv-left r2 irredN
... | inj₁ (L′ , L→L′ , IL′ , r3 , eq) =
      inj₁ (L′ , (L ⟶⟨ r1 ⟩ L→L′) , IL′ , r3 , cong suc eq)
... | inj₂ refl = inj₂ refl
app-inv-left {L} {M} {N} (.(L · M) ⟶⟨ ξ (v ·□) r1 ⟩ r2) irredN =
    inj₁ (value v , (_ END) , value-irred v ,
          ((value v · M) ⟶⟨ ξ (v ·□) r1 ⟩ r2) , refl)
app-inv-left {L} {M} {N} (.(L · M) ⟶⟨ ξ-blame (□· M₁) ⟩ r2) irredN
    with blame↠ r2
... | refl = inj₂ refl
app-inv-left {L} {M} {N} (.(L · M) ⟶⟨ ξ-blame (v ·□) ⟩ r2) irredN
    with blame↠ r2
... | refl = inj₂ refl
app-inv-left {.(ƛ _)} {M} {N} (.(ƛ _ · M) ⟶⟨ β v ⟩ r2) irredN =
    inj₁ (_ , (_ END) , value-irred (ƛ̬ _) , (_ ⟶⟨ β v ⟩ r2) , refl)

app-inv-right : ∀{V M N}
  → (r1 : V · M ↠ N)
  → Value V
  → irred N
  → (∃[ M′ ] Σ[ r2 ∈ (M ↠ M′) ] irred M′
       × Σ[ r3 ∈ (V · M′ ↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
app-inv-right {V}{M}{N} (.(_ · _) END) v irredN =
    inj₁ (M , (_ END) , irredM , (_ END) , refl)
    where irredM : irred M
          irredM (M′ , M→M′) = irredN ((V · M′) , (ξ (v ·□) M→M′))
app-inv-right {V} {M} {N} (.(V · M) ⟶⟨ ξ (□· M) r1 ⟩ r2) v irredN =
    ⊥-elim (value-irreducible v r1)
app-inv-right {V} {M} {N} (.(V · M) ⟶⟨ ξ (v′ ·□) r1 ⟩ r2) v irredN
    with app-inv-right r2 v′ irredN
... | inj₁ (M′ , M→M′ , iM′ , →N , eq) =
      inj₁ (M′ , (M ⟶⟨ r1 ⟩ M→M′) , iM′ , →N , cong suc eq)
... | inj₂ refl = inj₂ refl
app-inv-right {.blame} {M} {N} (.(blame · M) ⟶⟨ ξ-blame (□· M) ⟩ r2) () irredN
app-inv-right {V} {M} {N} (.(V · M) ⟶⟨ ξ-blame (v₁ ·□) ⟩ r2) v irredN
    with blame↠ r2
... | refl = inj₂ refl
app-inv-right {.(ƛ _)} {M} {N} (.(ƛ _ · M) ⟶⟨ β w ⟩ r2) v irredN =
    inj₁ (M , (_ END) , value-irred w , (_ ⟶⟨ β w ⟩ r2) , refl)

frame-inv : ∀{F M N}
  → (r1 : F ⟦ M ⟧ ↠ N)
  → irred N
  → (∃[ M′ ] Σ[ r2 ∈ (M ↠ M′) ] irred M′
        × Σ[ r3 ∈ (F ⟦ M′ ⟧ ↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
frame-inv {□· M} {L} {N} r1 irN = app-inv-left r1 irN 
frame-inv {v ·□} {M} {N} r1 irN = app-inv-right r1 v irN
frame-inv {□⟨ G !⟩} {M} (_ END) irN = inj₁ (_ , (_ END) , irM , (_ END) , refl)
    where irM : irred M
          irM (M′ , M→M′) = irN (_ , (ξ □⟨ G !⟩ M→M′))
frame-inv {□⟨ G !⟩} {M} {N} (.(□⟨ G !⟩ ⟦ M ⟧) ⟶⟨ ξ □⟨ _ !⟩ r1 ⟩ r2) irN
    with frame-inv{□⟨ G !⟩} r2 irN
... | inj₁ (M′ , r3 , irM′ , r4 , eq) = inj₁ (_ , (_ ⟶⟨ r1 ⟩ r3) , irM′ , r4 , cong suc eq)
... | inj₂ refl = inj₂ refl
frame-inv {□⟨ G !⟩} {M} {N} (.(□⟨ G !⟩ ⟦ M ⟧) ⟶⟨ ξ-blame □⟨ _ !⟩ ⟩ r2) irN
    with blame↠ r2
... | refl = inj₂ refl
frame-inv {□⟨ H ?⟩} {M} (_ END) irN = inj₁ (_ , (_ END) , irM , (_ END) , refl)
    where irM : irred M
          irM (M′ , M→M′) = irN (_ , (ξ □⟨ H ?⟩ M→M′))
frame-inv {□⟨ H ?⟩} {M} {N} (.(□⟨ H ?⟩ ⟦ M ⟧) ⟶⟨ ξ □⟨ _ ?⟩ r1 ⟩ r2) irN
    with frame-inv{□⟨ H ?⟩} r2 irN
... | inj₁ (M′ , r3 , irM′ , r4 , eq) = inj₁ (_ , (_ ⟶⟨ r1 ⟩ r3) , irM′ , r4 , cong suc eq)
... | inj₂ refl = inj₂ refl
frame-inv {□⟨ H ?⟩} {M} {N} (.(□⟨ H ?⟩ ⟦ M ⟧) ⟶⟨ ξ-blame □⟨ _ ?⟩ ⟩ r2) irN
    with blame↠ r2
... | refl = inj₂ refl
frame-inv {□⟨ H ?⟩} {M} {N} (.(□⟨ H ?⟩ ⟦ M ⟧) ⟶⟨ collapse v refl ⟩ r2) irN =
  inj₁ (M , (_ END) , value-irred (v 〈 _ 〉) , (_ ⟶⟨ collapse v refl ⟩ r2) , refl)
frame-inv {□⟨ H ?⟩} {M} {N} (.(□⟨ H ?⟩ ⟦ M ⟧) ⟶⟨ collide v eq refl ⟩ r2) irN =
  inj₁ (M , (_ END) , value-irred (v 〈 _ 〉) , (_ ⟶⟨ collide v eq refl ⟩ r2) , refl)

frame-blame : ∀{F}{M}{N}
   → M ↠ N
   → M ≡ F ⟦ blame ⟧
   → irred N
   → N ≡ blame
frame-blame {F} {N} (.N END) refl irN = ⊥-elim (irN (_ , (ξ-blame F)))
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) ⟶⟨ ξξ (□· M₁) refl x₁ r ⟩ M→N) refl irN =
  ⊥-elim (blame-irreducible r)
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) ⟶⟨ ξξ (() ·□) refl x₁ r ⟩ M→N) refl irN
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) ⟶⟨ ξξ-blame F x ⟩ M→N) refl irN
    with blame↠ M→N
... | refl = refl
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) ⟶⟨ ξξ (□· M) refl refl r ⟩ M→N) refl irN =
    ⊥-elim (value-irreducible v r)
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) ⟶⟨ ξξ (v₁ ·□) refl refl r ⟩ M→N) refl irN =
    ⊥-elim (blame-irreducible r)
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) ⟶⟨ ξξ-blame F x ⟩ M→N) refl irN 
    with blame↠ M→N
... | refl = refl
frame-blame {□⟨ G !⟩} {.(□⟨ G !⟩ ⟦ blame ⟧)} (.(□⟨ G !⟩ ⟦ blame ⟧) ⟶⟨ ξξ □⟨ _ !⟩ refl refl r ⟩ M→N) refl irN =
  ⊥-elim (blame-irreducible r)
frame-blame {□⟨ G !⟩} {.(□⟨ G !⟩ ⟦ blame ⟧)} (.(□⟨ G !⟩ ⟦ blame ⟧) ⟶⟨ ξξ-blame F x ⟩ M→N) refl irN
    with blame↠ M→N
... | refl = refl
frame-blame {□⟨ H ?⟩} {.(□⟨ H ?⟩ ⟦ blame ⟧)} (.(□⟨ H ?⟩ ⟦ blame ⟧) ⟶⟨ ξξ □⟨ _ ?⟩ refl refl r ⟩ M→N) refl irN = 
  ⊥-elim (blame-irreducible r)
frame-blame {□⟨ H ?⟩} {.(□⟨ H ?⟩ ⟦ blame ⟧)} (.(□⟨ H ?⟩ ⟦ blame ⟧) ⟶⟨ ξξ-blame □⟨ _ ?⟩ x ⟩ M→N) refl irN
    with blame↠ M→N
... | refl = refl

app-invL : ∀{L M N : Term}
   → reducible L
   → L · M  ⟶ N
   → ∃[ L′ ] ((L ⟶ L′) × (N ≡ L′ · M))
app-invL rl (ξ (□· M) L→L′) = _ , (L→L′ , refl)
app-invL (L′ , L→L′) (ξ (v ·□) M→M′) = ⊥-elim (value-irreducible v L→L′)
app-invL (L′ , L→L′) (ξ-blame (□· M)) = ⊥-elim (blame-irreducible L→L′)
app-invL (L′ , L→L′) (ξ-blame (v ·□)) = ⊥-elim (value-irreducible v L→L′)
app-invL (L′ , L→L′) (β v) = ⊥-elim (value-irreducible (ƛ̬ _) L→L′)

blame-frame : ∀{F}{N}
   → (F ⟦ blame ⟧) ⟶ N
   → N ≡ blame
blame-frame {□· M} {.((□· M₁) ⟦ _ ⟧)} (ξξ (□· M₁) refl refl Fb→N) =
    ⊥-elim (blame-irreducible Fb→N)
blame-frame {□· M} (ξξ (() ·□) refl refl Fb→N)
blame-frame {□· M} {.blame} (ξξ-blame (□· M₁) refl) = refl
blame-frame {□· M} {.blame} (ξξ-blame (() ·□) refl)
blame-frame {v ·□} {N} (ξξ (□· M) refl refl Fb→N) =
    ⊥-elim (value-irreducible v Fb→N)
blame-frame {v ·□} {N} (ξξ (v₁ ·□) refl refl Fb→N) =
    ⊥-elim (blame-irreducible Fb→N)
blame-frame {v ·□} {.blame} (ξξ-blame F x) = refl
blame-frame {□⟨ G !⟩} {_} (ξξ □⟨ _ !⟩ refl refl Fb→N) =
    ⊥-elim (blame-irreducible Fb→N)
blame-frame {□⟨ G !⟩} {.blame} (ξξ-blame F x) = refl
blame-frame {□⟨ H ?⟩} {N} (ξξ □⟨ _ ?⟩ refl refl Fb→N) =
    ⊥-elim (blame-irreducible Fb→N)
blame-frame {□⟨ H ?⟩} {.blame} (ξξ-blame □⟨ _ ?⟩ x) = refl

collapse-inv : ∀{V}{N}{G}
   → Value V
   → ((V ⟨ G !⟩) ⟨ G ?⟩) ⟶ N
   → N ≡ V
collapse-inv {V} {N} v (ξξ □⟨ G ?⟩ refl x₁ r) =
  ⊥-elim (value-irreducible (v 〈 G 〉) r)
collapse-inv {V} {.blame} v (ξξ-blame (□· M) ())
collapse-inv {V} {.blame} v (ξξ-blame (v₁ ·□) ())
collapse-inv {V} {.blame} v (ξξ-blame □⟨ G !⟩ ())
collapse-inv {V} {.blame} v (ξξ-blame □⟨ H ?⟩ ())
collapse-inv {V} {.V} v (collapse x refl) = refl
collapse-inv {V} {.blame} v (collide x x₁ refl) = ⊥-elim (x₁ refl)

collide-inv : ∀{V}{N}{G}{H}
   → G ≢ H
   → Value V
   → ((V ⟨ G !⟩) ⟨ H ?⟩) ⟶ N
   → N ≡ blame
collide-inv {V} {N} {G} {H} neq v (ξξ □⟨ H₁ ?⟩ refl x₁ red) =
  ⊥-elim (value-irreducible (v 〈 G 〉) red)
collide-inv {V} {.blame} {G} {H} neq v (ξξ-blame (□· M) ())
collide-inv {V} {.blame} {G} {H} neq v (ξξ-blame (v₁ ·□) ())
collide-inv {V} {.blame} {G} {H} neq v (ξξ-blame □⟨ G₁ !⟩ ())
collide-inv {V} {.blame} {G} {H} neq v (ξξ-blame □⟨ H₁ ?⟩ ())
collide-inv {V} {N} {G} {H} neq v (collapse x refl) = ⊥-elim (neq refl)
collide-inv {V} {.blame} {G} {H} neq v (collide x x₁ refl) = refl
\end{code}

\begin{code}[hide]
inject-eq : ∀{G}{N N′}
   → (N ⟨ G !⟩) ≡ (N′ ⟨ G !⟩)
   → N ≡ N′
inject-eq {G} {N} {.N} refl = refl

deterministic : ∀{M N N′}
  → M ⟶ N
  → M ⟶ N′
  → N ≡ N′
deterministic (ξ (□· M) M⟶N) (ξ (□· M₁) M⟶N′)
    with deterministic M⟶N M⟶N′
... | refl = refl
deterministic (ξ (□· M) M⟶N) (ξ (v ·□) M⟶N′) =
    ⊥-elim (value-irreducible v M⟶N)
deterministic (ξ (□· M) M⟶N) (ξ-blame (□· M₁)) =
    ⊥-elim (blame-irreducible M⟶N)
deterministic (ξ (□· M) M⟶N) (ξ-blame (v ·□)) =
    ⊥-elim (value-irreducible v M⟶N)
deterministic (ξ (□· M) M⟶N) (β v) =
    ⊥-elim (value-irreducible (ƛ̬ _) M⟶N)
deterministic (ξ (v ·□) M⟶N) (ξ (□· M) M⟶N′) = 
    ⊥-elim (value-irreducible v M⟶N′)
deterministic (ξ (v ·□) M⟶N) (ξ (v₁ ·□) M⟶N′)
    with deterministic M⟶N M⟶N′
... | refl = refl
deterministic (ξ (() ·□) M⟶N) (ξ-blame (□· M))
deterministic (ξ (v ·□) M⟶N) (ξ-blame (v₁ ·□)) =
    ⊥-elim (blame-irreducible M⟶N)
deterministic (ξ (v ·□) M⟶N) (β x) =
    ⊥-elim (value-irreducible x M⟶N)
deterministic (ξ (□⟨ G !⟩) M⟶N) (ξ (□⟨ _ !⟩) M⟶N′)
    with deterministic M⟶N M⟶N′
... | refl = refl
deterministic (ξ (□⟨ G !⟩) M⟶N) (ξ-blame (□⟨ _ !⟩)) =
    ⊥-elim (blame-irreducible M⟶N)
deterministic (ξ (□⟨ H ?⟩) M⟶N) (ξ (□⟨ _ ?⟩) M⟶N′)
    with deterministic M⟶N M⟶N′
... | refl = refl
deterministic (ξ (□⟨ H ?⟩) M⟶N) (ξ-blame (□⟨ _ ?⟩)) =
    ⊥-elim (blame-irreducible M⟶N)
deterministic (ξ □⟨ H ?⟩ r) (collapse v refl) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (ξ □⟨ H ?⟩ r) (collide v neq refl) = 
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (ξ-blame (□· M)) (ξ (□· M₁) M⟶N′) =
    ⊥-elim (blame-irreducible M⟶N′)
deterministic (ξ-blame (□· M)) (ξ (() ·□) M⟶N′)
deterministic (ξ-blame (□· M)) (ξ-blame (□· M₁)) = refl
deterministic (ξ-blame (□· M)) (ξ-blame (v ·□)) = refl
deterministic (ξ-blame (v ·□)) (ξ (□· M) M⟶N′) =
    ⊥-elim (value-irreducible v M⟶N′)
deterministic (ξ-blame (v ·□)) (ξ (v₁ ·□) M⟶N′) =
    ⊥-elim (blame-irreducible M⟶N′)
deterministic (ξ-blame (() ·□)) (ξ-blame (□· .blame))
deterministic (ξ-blame (v ·□)) (ξ-blame (v₁ ·□)) = refl
deterministic (ξ-blame (□⟨ G !⟩)) (ξ (□⟨ _ !⟩) M⟶N′) =
    ⊥-elim (blame-irreducible M⟶N′)
deterministic (ξ-blame (□⟨ G !⟩)) (ξ-blame (□⟨ _ !⟩)) = refl
deterministic (ξ-blame (□⟨ H ?⟩)) (ξ (□⟨ _ ?⟩) M⟶N′) =
    ⊥-elim (blame-irreducible M⟶N′)
deterministic (ξ-blame (□⟨ H ?⟩)) (ξ-blame (□⟨ _ ?⟩)) = refl
deterministic (β x) (ξ (□· M) M⟶N′) = ⊥-elim (value-irreducible (ƛ̬ _) M⟶N′)
deterministic (β x) (ξ (v ·□) M⟶N′) = ⊥-elim (value-irreducible x M⟶N′)
deterministic (β ()) (ξ-blame (v ·□))
deterministic (β x) (β x₁) = refl
deterministic (collapse v refl) (ξξ □⟨ _ ?⟩ refl refl r) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (collapse v refl) (ξξ-blame (□· M) ())
deterministic (collapse v refl) (ξξ-blame (v₁ ·□) ())
deterministic (collapse v refl) (ξξ-blame □⟨ _ !⟩ ())
deterministic (collapse v refl) (ξξ-blame □⟨ _ ?⟩ ())
deterministic (collapse v refl) (collapse x refl) = refl
deterministic (collapse v refl) (collide x neq refl) =
    ⊥-elim (neq refl)
deterministic (collide v neq refl) (ξξ □⟨ _ ?⟩ refl refl r) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (collide v neq refl) (ξξ-blame (□· M) ())
deterministic (collide v neq refl) (ξξ-blame (v₁ ·□) ())
deterministic (collide v neq refl) (ξξ-blame □⟨ _ !⟩ ())
deterministic (collide v neq refl) (ξξ-blame □⟨ _ ?⟩ ())
deterministic (collide v neq refl) (collapse x refl) =
    ⊥-elim (neq refl)
deterministic (collide v neq refl) (collide x x₁ x₂) = refl

frame-inv2 : ∀{L N : Term}{F}
   → reducible L
   → F ⟦ L ⟧ ⟶ N
   → ∃[ L′ ] ((L ⟶ L′) × (N ≡ F ⟦ L′ ⟧))
frame-inv2{L}{.((□· M₁) ⟦ _ ⟧)}{□· M} (L′ , L→L′) (ξξ (□· M₁) refl refl L→N) =
    L′ , (L→L′ , cong (λ X → X · M) (deterministic L→N L→L′))
frame-inv2 {L} {.((v ·□) ⟦ _ ⟧)} {□· M} (L′ , L→L′) (ξξ (v ·□) refl refl FL→N) =
   ⊥-elim (value-irreducible v L→L′)
frame-inv2 {L} {.blame} {□· M} (L′ , L→L′) (ξξ-blame (□· M₁) refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {.blame} {□· M} (L′ , L→L′) (ξξ-blame (v ·□) refl) =
    ⊥-elim (value-irreducible v L→L′)
frame-inv2 {ƛ N} {_} {□· M} (L′ , L→L′) (β x) =
    ⊥-elim (value-irreducible (ƛ̬ N) L→L′)
frame-inv2 {L} {N} {v ·□} (L′ , L→L′) (ξξ (□· M) refl refl FL→N) =
    ⊥-elim (value-irreducible v FL→N)
frame-inv2 {L} {N} {v ·□} (L′ , L→L′) (ξξ (v₁ ·□) refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {() ·□} (L′ , L→L′) (ξξ-blame (□· M) refl)
frame-inv2 {L} {.blame} {v ·□} (L′ , L→L′) (ξξ-blame (v₁ ·□) refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {_} {v ·□} (L′ , L→L′) (β w) =
    ⊥-elim (value-irreducible w L→L′)
frame-inv2 {L} {N} {□⟨ G !⟩} (L′ , L→L′) (ξξ □⟨ _ !⟩ refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {□⟨ G !⟩} (L′ , L→L′) (ξξ-blame □⟨ _ !⟩ refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {_} {□⟨ H ?⟩} (L′ , L→L′) (ξξ □⟨ _ ?⟩ refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {□⟨ H ?⟩} (L′ , L→L′) (ξξ-blame □⟨ _ ?⟩ refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {N} {□⟨ H ?⟩} (L′ , L→L′) (collapse v refl) = 
    ⊥-elim (value-irreducible (v 〈 _ 〉) L→L′)
frame-inv2 {L} {.blame} {□⟨ H ?⟩} (L′ , L→L′) (collide v neq refl) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) L→L′)

frame-inv3 : ∀{L N : Term}{F : PEFrame}
   → reducible L
   → F ⦉ L ⦊ ⟶ N
   → ∃[ L′ ] ((L ⟶ L′) × (N ≡ F ⦉ L′ ⦊))
frame-inv3 {L}{N}{□} rL FL→N = _ , (FL→N , refl)
frame-inv3 {L}{N}{` F} rL FL→N = frame-inv2 rL FL→N

blame-frame2 : ∀{F}{N}
   → (F ⦉ blame ⦊) ⟶ N
   → N ≡ blame
blame-frame2 {□}{N} Fb→N = ⊥-elim (blame-irreducible Fb→N)
blame-frame2 {` F}{N} Fb→N = blame-frame Fb→N

step-value-plus-one : ∀{M N V}
   → (M→N : M ↠ N)
   → (M→V : M ↠ V)
   → Value V
   → len M→N ≡ suc (len M→V)
   → ⊥
step-value-plus-one (_ ⟶⟨ r ⟩ _ END) (_ END) v eq = value-irreducible v r
step-value-plus-one (_ ⟶⟨ r1 ⟩ M→N) (_ ⟶⟨ r2 ⟩ M→V) v eq
    with deterministic r1 r2
... | refl = step-value-plus-one M→N M→V v (suc-injective eq)

step-blame-plus-one : ∀{M N}
   → (M→N : M ↠ N)
   → (M→b : M ↠ blame)
   → len M→N ≡ suc (len M→b)
   → ⊥
step-blame-plus-one (_ ⟶⟨ r ⟩ _ END) (_ END) eq = blame-irreducible r
step-blame-plus-one (_ ⟶⟨ r1 ⟩ M→N) (_ ⟶⟨ r2 ⟩ M→b) eq
    with deterministic r1 r2
... | refl = step-blame-plus-one M→N M→b (suc-injective eq)

diverge-not-halt : ∀{M}
  → M ⇑
  → ¬ halt M
diverge-not-halt divM (inj₁ M→blame)
    with divM (suc (len M→blame))
... | N , M→N , eq = step-blame-plus-one M→N M→blame (sym eq)    
diverge-not-halt divM (inj₂ (V , M→V , v))
    with divM (suc (len M→V))
... | N , M→N , eq = step-value-plus-one M→N M→V v (sym eq)    
  
cant-reduce-value-and-blame : ∀{M}{V}
   → Value V
   → M ↠ V
   → M ↠ blame
   → ⊥
cant-reduce-value-and-blame v (M END) (M ⟶⟨ M→N ⟩ N→b) =
  ⊥-elim (value-irreducible v M→N)
cant-reduce-value-and-blame v (.blame ⟶⟨ M→N ⟩ N→V) (.blame END) =
  ⊥-elim (blame-irreducible M→N)
cant-reduce-value-and-blame v (M ⟶⟨ M→N ⟩ N→V) (.M ⟶⟨ M→N′ ⟩ N′→b)
  rewrite deterministic M→N M→N′ = cant-reduce-value-and-blame v N→V N′→b
\end{code}

% LocalWords:  LogRel PeterCastCalculus elim Bool proj inj tt Eq Op
% LocalWords:  refl sym cong subst trans Nullary Var Sig ction sec
% LocalWords:  infixr emph minipage textwidth neq Num op lam app de
% LocalWords:  sig AbstractBindingTree ABT ast infixl var arity suc
% LocalWords:  Agda textsf Bruijn ext isBlame val typeof len mstep
% LocalWords:  PEFrame irred concat inv rs eq eqlen Vg irredN IL iM
% LocalWords:  irredM irN irM invL rl Fb FL rL divM
