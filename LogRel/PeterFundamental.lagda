\begin{code}[hide]
{-# OPTIONS --rewriting #-}
module LogRel.PeterFundamental where

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
open import LogRel.PeterPrecision
open import LogRel.PeterLogRel
open import StepIndexedLogic
\end{code}

\section{Fundamental Theorem of the Logical Relation}
\label{sec:fundamental}

The fundamental theorem of the logical relation states that if two
terms are related by precision, then they are in the logical relation.
The fundamental theorem is proved by induction on the term precision
relation. Each case of that proof is split out into a separate lemma,
which by tradition are called Compatibility Lemmas.

\paragraph{Compatibility for Literals, Blame, and Variables}

The proof of compatibility for literals uses the LRᵥ⇒LRₜ lemma.

\begin{code}[hide]
LRᵥ-base-intro : ∀{𝒫}{ι}{c}{dir} → 𝒫 ⊢ᵒ dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}
LRᵥ-base-intro{𝒫}{ι}{c}{dir} = ⊢ᵒ-intro λ k 𝒫k → step {ι}{dir}{c}{k}
  where
  step : ∀{ι}{dir}{c}{k} → # (dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}) k
  step {ι} {dir} {c} {zero} = tt
  step {ι} {dir} {c} {suc k} = refl
\end{code}

\begin{code}
compatible-literal : ∀{Γ}{c}{ι} → Γ ⊨ $ c ⊑ᴸᴿ $ c ⦂ ($ₜ ι , $ₜ ι , base⊑)
\end{code}
\begin{code}[hide]
compatible-literal {Γ}{c}{ι} =
  (λ γ γ′ → LRᵥ⇒LRₜ LRᵥ-base-intro) , (λ γ γ′ → LRᵥ⇒LRₜ LRᵥ-base-intro)
\end{code}

\noindent The proof of compatibility for blame is direct from the definitions.

\begin{code}[hide]
LRₜ-blame-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{k}
   → #(dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′) k
LRₜ-blame-step {A}{A′}{A⊑A′}{dir} {M} {zero} = tz (dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′)
LRₜ-blame-step {A}{A′}{A⊑A′}{≼} {M} {suc k} = inj₂ (inj₁ (blame END))
LRₜ-blame-step {A}{A′}{A⊑A′}{≽} {M} {suc k} = inj₂ (inj₁ isBlame)
\end{code}
\begin{code}[hide]
LRₜ-blame : ∀{𝒫}{A}{A′}{A⊑A′ : A ⊑ A′}{M}{dir} → 𝒫 ⊢ᵒ dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′
LRₜ-blame {𝒫}{A}{A′}{A⊑A′}{M}{dir} = ⊢ᵒ-intro λ n x → LRₜ-blame-step{dir = dir}
\end{code}
\begin{code}
compatible-blame : ∀{Γ}{A}{M} → map proj₁ Γ ⊢ M ⦂ A → Γ ⊨ M ⊑ᴸᴿ blame ⦂ (A , A , Refl⊑)
\end{code}
\begin{code}[hide]
compatible-blame{Γ}{A}{M} ⊢M = (λ γ γ′ → LRₜ-blame) , (λ γ γ′ → LRₜ-blame)
\end{code}

\noindent The proof of compatibility for variables relies on the
following lemma regarding related substitutions.

\begin{code}
lookup-⊑ᴸᴿ : ∀{dir} (Γ : List Prec) → (γ γ′ : Subst) → ∀ {A}{A′}{A⊑A′}{x}
  → Γ ∋ x ⦂ (A , A′ , A⊑A′)  →  (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ γ x ⊑ᴸᴿᵥ γ′ x ⦂ A⊑A′
\end{code}
\begin{code}[hide]
lookup-⊑ᴸᴿ {dir} (.(A , A′ , A⊑A′) ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
lookup-⊑ᴸᴿ {dir} (B ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {suc x} ∋x =
   Sᵒ (lookup-⊑ᴸᴿ Γ (λ z → γ (suc z)) (λ z → γ′ (suc z)) ∋x)
\end{code}

\begin{code}
compatibility-var : ∀ {Γ A A′ A⊑A′ x} → Γ ∋ x ⦂ (A , A′ , A⊑A′)
  → Γ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
\end{code}
\begin{code}[hide]
compatibility-var {Γ}{A}{A′}{A⊑A′}{x} ∋x = LT , GT
  where
  LT : Γ ∣ ≼ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
  LT γ γ′ rewrite sub-var γ x | sub-var γ′ x = LRᵥ⇒LRₜ (lookup-⊑ᴸᴿ Γ γ γ′ ∋x)

  GT : Γ ∣ ≽ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
  GT γ γ′ rewrite sub-var γ x | sub-var γ′ x = LRᵥ⇒LRₜ (lookup-⊑ᴸᴿ Γ γ γ′ ∋x)
\end{code}

\paragraph{Compatibility for Lambda}

The proof of compatibility for lambda abstraction has a premise that
says the bodies of the two lambdas are in the logical relation, which
is the induction hypothesis in this case of the fundamental theorem.
The logical relation for lambda requires us to prove
\begin{center}
\textsf{𝒫 ⊢ᵒ (dir ∣ (⟪ ext γ ⟫ N) [ W ] ⊑ᴸᴿₜ (⟪ ext γ′ ⟫ N′) [ W′ ] ⦂ d)}
\end{center}
Using the premise we obtain
\begin{center}
\textsf{𝒫 ⊢ᵒ (dir ∣ ⟪ W • γ ⟫ N ⊑ᴸᴿₜ ⟪ W′ • γ′ ⟫ N′ ⦂ d)}
\end{center}
which is equivalent to what is required thanks to the
\textsf{ext-sub-cons} theorem from the ABT library. As an example of a
proof using SIL, here is the proof in full of compatibility for
lambda.

\begin{code}[hide]
LRᵥ-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}{dir}
   → (dir ∣ (ƛ N) ⊑ᴸᴿᵥ (ƛ N′) ⦂ fun⊑ A⊑A′ B⊑B′)
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ A⊑A′))
                →ᵒ (▷ᵒ (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′))))
\end{code}
\begin{code}[hide]
LRᵥ-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′}{dir} =
   let X = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , dir , ƛ N , ƛ N′) in
   (dir ∣ (ƛ N) ⊑ᴸᴿᵥ (ƛ N′) ⦂ fun⊑ A⊑A′ B⊑B′)  ⩦⟨ ≡ᵒ-refl refl ⟩
   LRₜ⊎LRᵥ X                                   ⩦⟨ fixpointᵒ pre-LRₜ⊎LRᵥ X ⟩
   # (pre-LRₜ⊎LRᵥ X) (LRₜ⊎LRᵥ , ttᵖ)           ⩦⟨ ≡ᵒ-refl refl ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ A⊑A′))
                   →ᵒ (▷ᵒ (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′)))) ∎
\end{code}
\begin{code}
compatible-lambda : ∀{Γ : List Prec}{A}{B}{C}{D}{N N′ : Term}{c : A ⊑ C}{d : B ⊑ D}
   → ((A , C , c) ∷ Γ) ⊨ N ⊑ᴸᴿ N′ ⦂ (B , D , d)
   → Γ ⊨ (ƛ N) ⊑ᴸᴿ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ =
  (λ γ γ′ → ⊢ℰλNλN′) , (λ γ γ′ → ⊢ℰλNλN′)
 where ⊢ℰλNλN′ : ∀{dir}{γ}{γ′} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
                 ⊢ᵒ (dir ∣ ⟪ γ ⟫ (ƛ N) ⊑ᴸᴿₜ ⟪ γ′ ⟫ (ƛ N′) ⦂ fun⊑ c d)
       ⊢ℰλNλN′ {dir}{γ}{γ′} = LRᵥ⇒LRₜ (substᵒ (≡ᵒ-sym LRᵥ-fun)
         (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI {P = ▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c)}
           let IH = (proj dir N N′ ⊨N⊑N′) (W • γ) (W′ • γ′) in
           (appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI IH)))) Zᵒ)))
\end{code}

We note that the use of SIL in the above proof comes with some
tradeoffs. On the one hand, there is no explicit reasoning about step
indices. On the other hand, there is some added verbosity compared to
a proof in raw Agda such as the use of \textsf{appᵒ} for modus-ponens,
the use of de Bruijn indices \textsf{Zᵒ} to refer to premises,
and extra annotations such as \textsf{{P = ▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c)}}
that are needed when Agda's type inference fails.

However, there is a bigger problem regarding incremental proof
development in SIL. It is common practice to create a partial proof
with a hole, written \textsf{?}, and one can ask Agda to print what
need to be proved in the hole. For example, instead of \textsf{(→ᵒI
IH)} in the above proof, one might have started with \textsf{(→ᵒI ?)}.
Unfortunately, Agda's message describing what needs to be proved fills
an entire computer screen because Agda normalizes the SIL formulas
into their Agda encodings. We are working on new version of SIL that
uses the \texttt{abstract} feature of Agda to hide the internals of
SIL from its clients, but that also has its challenges, such as
requiring the use of the \texttt{prop} extension so that the fields of
\textsf{Setᵒ} that contain proofs are ignored when proving equations
such as \textsf{fixpointᵒ}.


\paragraph{Anti-reduction and Bind Lemmas}

The remaining compatibility lemmas, for function application and for
injections and projections, require several anti-reduction lemmas
which state that if two terms are in the logical relation, then
walking backwards with one or both of them yields terms that are still
in the logical relation. Here we list just one of them.  We formulated
these lemmas with explicit step indices and the meaning function
\textsf{\#} because working with the raw Agda encoding enables the use
of automatic proof search.

\begin{code}[hide]
anti-reduction-≼-R-one : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≼ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i  →  M′ ⟶ N′  →  #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
\end{code}
\begin{code}[hide]
anti-reduction-≼-R-one {c = c}{M}{M′}{N′}{zero} ℰMN′ M′→N′ =
  tz (≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c)
anti-reduction-≼-R-one {c = c}{M}{M′}{N′}{suc i} ℰMN′ M′→N′
    with ℰMN′
... | inj₁ (N , M→N , ▷ℰNN′) =
         let ℰNM′si = anti-reduction-≼-R-one ▷ℰNN′ M′→N′ in
         inj₁ (N , M→N , ℰNM′si)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (unit M′→N′ ++ N′→blame))
... | inj₂ (inj₂ (m , (V′ , N′→V′ , v′ , 𝒱MV′))) =
      inj₂ (inj₂ (m , (V′ , (unit M′→N′ ++ N′→V′) , v′ , 𝒱MV′)))
\end{code}
\begin{code}[hide]
anti-reduction-≼-R : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≼ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i  →  M′ ↠ N′  →  #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
\end{code}
\begin{code}[hide]
anti-reduction-≼-R {M′ = M′} ℰMN′ (.M′ END) = ℰMN′
anti-reduction-≼-R {M′ = M′} {N′} {i} ℰMN′ (.M′ ⟶⟨ M′→L′ ⟩ L′→*N′) =
  anti-reduction-≼-R-one (anti-reduction-≼-R ℰMN′ L′→*N′) M′→L′
\end{code}
\begin{code}[hide]
anti-reduction-≽-R-one : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≽ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i  →  M′ ⟶ N′  →  #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
\end{code}
\begin{code}[hide]
anti-reduction-≽-R-one {c = c} {M} {M′}{N′} {i} ℰ≽MN′ M′→N′ =
  inj₁ (N′ , M′→N′ , ℰ≽MN′)
\end{code}
\begin{code}[hide]
anti-reduction-≽-L-one : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≽ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i  →  M ⟶ N  →  #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
\end{code}
\begin{code}[hide]
anti-reduction-≽-L-one {c = c}{M} {N}{M′} {zero} ℰNM′ M→N =
    tz (≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c)
anti-reduction-≽-L-one {M = M} {N}{M′}  {suc i} ℰNM′ M→N
    with ℰNM′
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      inj₁ (N′ , (M′→N′ , (anti-reduction-≽-L-one ▷ℰMN′ M→N)))
... | inj₂ (inj₁ isBlame) = inj₂ (inj₁ isBlame)
... | inj₂ (inj₂ (m′ , V , N→V , v , 𝒱VM′)) =
      inj₂ (inj₂ (m′ , V , (unit M→N ++ N→V) , v , 𝒱VM′))
\end{code}
\begin{code}[hide]
anti-reduction-≽-L : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≽ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i  →  M ↠ N  →  #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
\end{code}
\begin{code}[hide]
anti-reduction-≽-L {c = c} {M} {.M} {N′} {i} ℰNM′ (.M END) = ℰNM′
anti-reduction-≽-L {c = c} {M} {M′} {N′} {i} ℰNM′ (.M ⟶⟨ M→L ⟩ L→*N) =
  anti-reduction-≽-L-one (anti-reduction-≽-L ℰNM′ L→*N) M→L
\end{code}
\begin{code}[hide]
anti-reduction-≼-L-one : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≼ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i  →  M ⟶ N  →  #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
\end{code}
\begin{code}[hide]
anti-reduction-≼-L-one {c = c} {M} {N} {M′} {i} ℰ≼NM′i M→N = inj₁ (N , M→N , ℰ≼NM′i)
\end{code}
\begin{code}
anti-reduction : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{N′}{i}{dir}
  → #(dir ∣ N ⊑ᴸᴿₜ N′ ⦂ c) i  →  M ⟶ N  →  M′ ⟶ N′
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
\end{code}
\begin{code}[hide]
anti-reduction {c = c} {M} {N} {M′} {N′} {i} {≼} ℰNN′i M→N M′→N′ =
  let ℰMN′si = anti-reduction-≼-L-one ℰNN′i M→N in
  let ℰM′N′si = anti-reduction-≼-R-one ℰMN′si M′→N′ in
  ℰM′N′si
anti-reduction {c = c} {M} {N} {M′} {N′} {i} {≽} ℰNN′i M→N M′→N′ =
  let ℰM′Nsi = anti-reduction-≽-R-one ℰNN′i M′→N′ in
  let ℰM′N′si = anti-reduction-≽-L-one ℰM′Nsi M→N in
  ℰM′N′si
\end{code}

The remaining compatibility lemmas all involve language features with
subexpressions, and one need to reason about the reduction of those
subexpressions down to values. The following \textsf{LRₜ-bind} lemma
performs that reasoning once an for all. It says that if you are
trying to prove that $N$ ⊑ᴸᴿₜ $N′$, if $M$ is a direct subexpression
of $N$ and $M′$ is a direct subexpression of $N′$, so $N = F ⦉ M ⦊$
and $N′ = F′ ⦉ M′ ⦊$, then one can replace $M$ and $M′$ with any
related values $V$ ⊑ᴸᴿᵥ $V′$ and it suffices prove $F ⦉ V ⦊$ ⊑ᴸᴿₜ $F′
⦉ V′ ⦊$.  The proof of the \textsf{LRₜ-bind} lemma relies on two of
the anti-reduction lemmas.

\begin{code}[hide]
bind-premise : Dir → PEFrame → PEFrame → Term → Term → ℕ
   → ∀ {B}{B′}(c : B ⊑ B′) → ∀ {A}{A′} (d : A ⊑ A′) → Set
bind-premise dir F F′ M M′ i c d =
    (∀ j V V′ → j ≤ i → M ↠ V → Value V → M′ ↠ V′ → Value V′
     → # (dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
     → # (dir ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
\end{code}
\begin{code}[hide]
LRᵥ→LRₜ-down-one-≼ : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}{F}{F′}{i}{M}{N}{M′}
   → M ⟶ N
   → (bind-premise ≼ F F′ M M′ (suc i) c d)
   → (bind-premise ≼ F F′ N M′ i c d)
\end{code}
\begin{code}[hide]
LRᵥ→LRₜ-down-one-≼ {B}{B′}{c}{A}{A′}{d}{F}{F′}{i}{M}{N}{M′} M→N LRᵥ→LRₜsi
   j V V′ j≤i M→V v M′→V′ v′ 𝒱j =
   LRᵥ→LRₜsi j V V′ (≤-trans j≤i (n≤1+n i)) (M ⟶⟨ M→N ⟩ M→V) v M′→V′ v′ 𝒱j
\end{code}
\begin{code}[hide]
LRᵥ→LRₜ-down-one-≽ : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}{F}{F′}{i}{M}{M′}{N′}
   → M′ ⟶ N′
   → (bind-premise ≽ F F′ M M′ (suc i) c d)
   → (bind-premise ≽ F F′ M N′ i c d)
\end{code}
\begin{code}[hide]
LRᵥ→LRₜ-down-one-≽ {B}{B′}{c}{A}{A′}{d}{F}{F′}{i}{M}{N}{M′} M′→N′ LRᵥ→LRₜsi
   j V V′ j≤i M→V v M′→V′ v′ 𝒱j =
   LRᵥ→LRₜsi j V V′ (≤-trans j≤i (n≤1+n i)) M→V v (N ⟶⟨ M′→N′ ⟩ M′→V′) v′ 𝒱j
\end{code}
\begin{code}
LRₜ-bind : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}{F}{F′}{M}{M′}{i}{dir}
   → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ d) i
   → (∀ j V V′ → j ≤ i → M ↠ V → Value V → M′ ↠ V′ → Value V′
         → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j → #(dir ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
   → #(dir ∣ (F ⦉ M ⦊) ⊑ᴸᴿₜ (F′ ⦉ M′ ⦊) ⦂ c) i
\end{code}
\begin{code}[hide]
LRₜ-bind {B}{B′}{c}{A}{A′}{d}{F} {F′} {M} {M′} {zero} {dir} ℰMM′sz LRᵥ→LRₜj =
    tz (dir ∣ (F ⦉ M ⦊) ⊑ᴸᴿₜ (F′ ⦉ M′ ⦊) ⦂ c)
LRₜ-bind {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≼} ℰMM′si LRᵥ→LRₜj
    with ⇔-to (LRₜ-suc{dir = ≼}) ℰMM′si
... | inj₁ (N , M→N , ▷ℰNM′) =
     let IH = LRₜ-bind{c = c}{d = d}{F}{F′}{N}{M′}{i}{≼} ▷ℰNM′
                (LRᵥ→LRₜ-down-one-≼{c = c}{d = d}{F}{F′}{i}{M}{N}{M′}
                     M→N LRᵥ→LRₜj) in
      ⇔-fro (LRₜ-suc{dir = ≼}) (inj₁ ((F ⦉ N ⦊) , ξ′ F refl refl M→N , IH))
LRₜ-bind {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≼} ℰMM′si LRᵥ→LRₜj 
    | inj₂ (inj₂ (m , (V′ , M′→V′ , v′ , 𝒱MV′))) =
      let ℰFMF′V′ = LRᵥ→LRₜj (suc i) M V′ ≤-refl (M END) m M′→V′ v′ 𝒱MV′ in
      anti-reduction-≼-R ℰFMF′V′ (ξ′* F′ M′→V′)
LRₜ-bind {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≼} ℰMM′si LRᵥ→LRₜj 
    | inj₂ (inj₁ M′→blame) = inj₂ (inj₁ (ξ-blame₃ F′ M′→blame refl))
LRₜ-bind {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≽} ℰMM′si LRᵥ→LRₜj 
    with ⇔-to (LRₜ-suc{dir = ≽}) ℰMM′si
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      let ℰFMFN′ : # (≽ ∣ (F ⦉ M ⦊) ⊑ᴸᴿₜ (F′ ⦉ N′ ⦊) ⦂ c) i
          ℰFMFN′ = LRₜ-bind{c = c}{d = d}{F}{F′}{M}{N′}{i}{≽} ▷ℰMN′ 
                   (LRᵥ→LRₜ-down-one-≽{c = c}{d = d}{F}{F′} M′→N′ LRᵥ→LRₜj) in
      inj₁ ((F′ ⦉ N′ ⦊) , (ξ′ F′ refl refl M′→N′) , ℰFMFN′)
... | inj₂ (inj₁ isBlame)
    with F′
... | □ = inj₂ (inj₁ isBlame)
... | ` F″ = inj₁ (blame , ξ-blame F″ , LRₜ-blame-step{dir = ≽})
LRₜ-bind {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≽} ℰMM′si LRᵥ→LRₜj 
    | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱VM′)) =
    let xx = LRᵥ→LRₜj (suc i) V M′ ≤-refl M→V v (M′ END) m′ 𝒱VM′ in
    anti-reduction-≽-L xx (ξ′* F M→V)
\end{code}

\paragraph{Compatibility for Application}

Here is where the logical relation demonstrates its worth.
Using the \textsf{LRₜ-bind} lemma twice, we go from needing
to prove $L · M$ ⊑ᴸᴿₜ $L′ · M′$ to 
$V · W$ ⊑ᴸᴿₜ $V′ · W′$. Then because $V$ ⊑ᴸᴿᵥ $V′$ at
function type, the logical relation tells us that
$V = λN$, $V′ = λN′$, and \textsf{N[W]} ⊑ᴸᴿₜ \textsf{N′[W′]}
at one step later in time. So we back up one step of β-reduction
using \textsf{anti-reduction} to show that 
\textsf{(λN) · W} ⊑ᴸᴿₜ \textsf{(λN′) · W′}.

\begin{code}[hide]
LRᵥ-fun-elim-step : ∀{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{dir}{k}{j}
  → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ fun⊑ c d) (suc k)
  → j ≤ k
  → ∃[ N ] ∃[ N′ ] V ≡ ƛ N × V′ ≡ ƛ N′ 
      × (∀{W W′} → # (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c) j
                 → # (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ d) j)
LRᵥ-fun-elim-step {A}{B}{A′}{B′}{c}{d}{ƛ N}{ƛ N′}{dir}{k}{j} 𝒱VV′ j≤k =
  N , N′ , refl , refl , λ {W}{W′} 𝒱WW′ →
    let 𝒱λNλN′sj = down (dir ∣ (ƛ N) ⊑ᴸᴿᵥ (ƛ N′) ⦂ fun⊑ c d)
                        (suc k) 𝒱VV′ (suc j) (s≤s j≤k) in
    let ℰNWN′W′j = 𝒱λNλN′sj W W′ (suc j) ≤-refl 𝒱WW′ in
    ℰNWN′W′j
\end{code}
\begin{code}
compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ᴸᴿ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d) → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (A , A′ , c)
   → Γ ⊨ L · M ⊑ᴸᴿ L′ · M′ ⦂ (B , B′ , d)
\end{code}
\begin{code}[hide]
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′} ⊨L⊑L′ ⊨M⊑M′ =
 (λ γ γ′ → ⊢ℰLM⊑LM′) , λ γ γ′ → ⊢ℰLM⊑LM′
 where
 ⊢ℰLM⊑LM′ : ∀{dir}{γ}{γ′} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
                             ⊢ᵒ dir ∣ ⟪ γ ⟫ (L · M) ⊑ᴸᴿₜ ⟪ γ′ ⟫ (L′ · M′) ⦂ d
 ⊢ℰLM⊑LM′ {dir}{γ}{γ′} = ⊢ᵒ-intro λ n 𝒫n →
  LRₜ-bind{c = d}{d = fun⊑ c d}
               {F = ` (□· (⟪ γ ⟫ M))}{F′ = ` (□· (⟪ γ′ ⟫ M′))}
  (⊢ᵒ-elim ((proj dir L L′ ⊨L⊑L′) γ γ′) n 𝒫n)
  λ j V V′ j≤n L→V v L′→V′ v′ 𝒱VV′j →
  LRₜ-bind{c = d}{d = c}{F = ` (v ·□)}{F′ = ` (v′ ·□)}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) j
   (down (Πᵒ (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)) n 𝒫n j j≤n))
   λ i W W′ i≤j M→W w M′→W′ w′ 𝒱WW′i →
     Goal{v = v}{v′}{w = w}{w′} i≤j 𝒱VV′j 𝒱WW′i
   where
   Goal : ∀{V}{V′}{v : Value V}{v′ : Value V′}
           {W}{W′}{w : Value W}{w′ : Value W′}{i}{j}
     → i ≤ j
     → # (dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ fun⊑ c d) j
     → # (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c) i
     → # (dir ∣ ((` (v ·□)) ⦉ W ⦊) ⊑ᴸᴿₜ ((` (v′ ·□)) ⦉ W′ ⦊) ⦂ d) i
   Goal {V} {V′} {v} {v′} {W} {W′} {w}{w′}{zero} {j} i≤j 𝒱VV′j 𝒱WW′i =
     tz (dir ∣ (value v · W) ⊑ᴸᴿₜ (value v′ · W′) ⦂ d)
   Goal {V} {V′} {v} {v′} {W} {W′} {w}{w′}{suc i} {suc j}
       (s≤s i≤j) 𝒱VV′sj 𝒱WW′si
       with LRᵥ-fun-elim-step{A}{B}{A′}{B′}{c}{d}{V}{V′}{dir}{j}{i} 𝒱VV′sj i≤j
   ... | N , N′ , refl , refl , body =
       let 𝒱WW′i = down (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c)(suc i)𝒱WW′si i (n≤1+n i) in
       let ℰNWNW′i = body{W}{W′} 𝒱WW′i in
       anti-reduction{c = d}{i = i}{dir = dir} ℰNWNW′i (β w) (β w′)
\end{code}

\paragraph{Compatibility for Injections}

We have two cases to deal with, the injection can be on the left or
the right. Starting with a projection on the left, \textsf{LRₜ-bind}
takes us from need to prove $M ⟨ G !⟩$ ⊑ᴸᴿ $M′$ to needing $V ⟨ G !⟩$
⊑ᴸᴿ $V′$, assuming $V$ ⊑ᴸᴿ $V′$. We proceed by case analysis on the
direction (≼ or ≽).  For ≼, we need to prove $▷ᵒ (V$ ⊑ᴸᴿᵥ $V′)$, which
follows from $V$ ⊑ᴸᴿ $V′$ by monotonicity. For ≽, we just need to
prove $V$ ⊑ᴸᴿ $V′$, which we have by the assumption.

\begin{code}[hide]
LRᵥ-inject-L-intro-≽ : ∀{G}{A′}{c : ⌈ G ⌉ ⊑ A′}{V}{V′}{k}
   → #(≽ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≽ ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) k
\end{code}
\begin{code}[hide]
LRᵥ-inject-L-intro-≽ {G}{A′}{c}{V}{V′}{zero} 𝒱VV′k =
    tz (≽ ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c)
LRᵥ-inject-L-intro-≽ {G} {A′} {c} {V} {V′} {suc k} 𝒱VV′sk
    with G ≡ᵍ G
... | no neq = ⊥-elim (neq refl)
... | yes refl =
      let (v , v′) = LRᵥ⇒Value c V V′ 𝒱VV′sk in
      v , v′ , 𝒱VV′sk
\end{code}
\begin{code}[hide]
LRᵥ-inject-L-intro : ∀{G}{A′}{c : ⌈ G ⌉ ⊑ A′}{V}{V′}{dir}{k}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(dir ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) k
\end{code}
\begin{code}[hide]
LRᵥ-inject-L-intro {G} {A′} {c} {V} {V′} {≼} {zero} 𝒱VV′k =
    tz (≼ ∣ V ⟨ G !⟩ ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c)
LRᵥ-inject-L-intro {G} {A′} {c} {V} {V′} {≼} {suc k} 𝒱VV′sk
    with G ≡ᵍ G
... | no neq = ⊥-elim (neq refl)
... | yes refl =
    let (v , v′) = LRᵥ⇒Value c V V′ 𝒱VV′sk in
    let 𝒱VV′k = down (≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) (suc k) 𝒱VV′sk k (n≤1+n k) in
    v , v′ , 𝒱VV′k 
LRᵥ-inject-L-intro {G} {A′} {c} {V} {V′} {≽} {k} 𝒱VV′k =
   LRᵥ-inject-L-intro-≽{G} {A′} {c} {V} {V′} 𝒱VV′k 
\end{code}
\begin{code}
compatible-inj-L : ∀{Γ}{G A′}{c : ⌈ G ⌉ ⊑ A′}{M M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (⌈ G ⌉ , A′ , c)
   → Γ ⊨ M ⟨ G !⟩ ⊑ᴸᴿ M′ ⦂ (★ , A′ , unk⊑{G}{A′} c)
\end{code}
\begin{code}[hide]
compatible-inj-L{Γ}{G}{A′}{c}{M}{M′} ⊨M⊑M′ =
  (λ γ γ′ → ℰMGM′) , (λ γ γ′ → ℰMGM′)
  where
  ℰMGM′ : ∀ {γ}{γ′}{dir}
   → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ (dir ∣ (⟪ γ ⟫ M ⟨ G !⟩) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′) ⦂ unk⊑ c)
  ℰMGM′{γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   LRₜ-bind{c = unk⊑ c}{d = c}{F = ` (□⟨ G !⟩)}{F′ = □}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
   LRᵥ⇒LRₜ-step{★}{A′}{unk⊑ c}{V ⟨ G !⟩}{V′}{dir}{j}
   (LRᵥ-inject-L-intro{G}{A′}{c}{V}{V′}{dir}{j} 𝒱VV′j)
\end{code}

Next consider when the injection is on the right.  The
\textsf{LRₜ-bind} lemma takes us from needing to prove $M$ ⊑ᴸᴿ $M′ ⟨ G !⟩$
to needing $V$ ⊑ᴸᴿ $V′ ⟨ G !⟩$ where $V$ ⊑ᴸᴿᵥ $V′$.
We know that $V$ is of type ★ (rule \textsf{⊑-inj-R})
so $V = W ⟨ G !⟩$ and $W$ ⊑ᴸᴿᵥ $V′$ (the \textsf{unk⊑} clause of \textsf{LRᵥ}).
So we conclude that $W ⟨ G !⟩$ ⊑ᴸᴿ $V′ ⟨ G !⟩$
by the \textsf{unk⊑unk} clause of \textsf{LRᵥ}. 

\begin{code}[hide]
LRᵥ-dyn-any-elim-≽ : ∀{V}{V′}{k}{H}{A′}{c : ⌈ H ⌉ ⊑ A′}
   → #(≽ ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) (suc k)
   → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
             × #(≽ ∣ V₁ ⊑ᴸᴿᵥ V′ ⦂ c) (suc k)
\end{code}
\begin{code}[hide]
LRᵥ-dyn-any-elim-≽ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VGV′
... | yes refl
    with 𝒱VGV′
... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′
\end{code}
\begin{code}[hide]
LRᵥ-inject-R-intro-≽ : ∀{G}{c : ★ ⊑ ⌈ G ⌉}{V}{V′}{k}
   → #(≽ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≽ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
\end{code}
\begin{code}[hide]
LRᵥ-inject-R-intro-≽ {G} {c} {V} {V′} {zero} 𝒱VV′ =
     tz (≽ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk)
LRᵥ-inject-R-intro-≽ {G} {c} {V} {V′} {suc k} 𝒱VV′sk
    with unk⊑gnd-inv c
... | d , refl
    with LRᵥ-dyn-any-elim-≽ {V}{V′}{k}{G}{_}{d} 𝒱VV′sk
... | V₁ , refl , v₁ , v′ , 𝒱V₁V′sk
    with G ≡ᵍ G
... | no neq = ⊥-elim 𝒱VV′sk
... | yes refl
    with gnd-prec-unique d Refl⊑
... | refl =
    let 𝒱V₁V′k = down (≽ ∣ V₁ ⊑ᴸᴿᵥ V′ ⦂ d) (suc k) 𝒱V₁V′sk k (n≤1+n k) in
    v₁ , v′ , 𝒱V₁V′k
\end{code}
\begin{code}[hide]
LRᵥ-dyn-any-elim-≼ : ∀{V}{V′}{k}{H}{A′}{c : ⌈ H ⌉ ⊑ A′}
   → #(≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) (suc k)
   → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′ × #(≼ ∣ V₁ ⊑ᴸᴿᵥ V′ ⦂ c) k
\end{code}
\begin{code}[hide]
LRᵥ-dyn-any-elim-≼ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VGV′
... | yes refl
    with 𝒱VGV′
... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′
\end{code}
\begin{code}[hide]
LRᵥ-inject-R-intro-≼ : ∀{G}{c : ★ ⊑ ⌈ G ⌉}{V}{V′}{k}
   → #(≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≼ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
\end{code}
\begin{code}[hide]
LRᵥ-inject-R-intro-≼ {G} {c} {V} {V′} {zero} 𝒱VV′ =
     tz (≼ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk)
LRᵥ-inject-R-intro-≼ {G} {c} {V} {V′} {suc k} 𝒱VV′sk
    with unk⊑gnd-inv c
... | d , refl
    with LRᵥ-dyn-any-elim-≼ {V}{V′}{k}{G}{_}{d} 𝒱VV′sk
... | V₁ , refl , v₁ , v′ , 𝒱V₁V′k
    with G ≡ᵍ G
... | no neq = ⊥-elim 𝒱VV′sk
... | yes refl
    with gnd-prec-unique d Refl⊑
... | refl = v₁ , v′ , 𝒱V₁V′k
\end{code}
\begin{code}[hide]
LRᵥ-inject-R-intro : ∀{G}{c : ★ ⊑ ⌈ G ⌉}{V}{V′}{k}{dir}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(dir ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
\end{code}
\begin{code}[hide]
LRᵥ-inject-R-intro {G} {c} {V} {V′} {k} {≼} 𝒱VV′ =
   LRᵥ-inject-R-intro-≼{G} {c} {V} {V′} {k} 𝒱VV′ 
LRᵥ-inject-R-intro {G} {c} {V} {V′} {k} {≽} 𝒱VV′ =
   LRᵥ-inject-R-intro-≽{G} {c} {V} {V′} {k} 𝒱VV′
\end{code}
\begin{code}
compatible-inj-R : ∀{Γ}{G}{c : ★ ⊑ ⌈ G ⌉ }{M M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , ⌈ G ⌉ , c)
   → Γ ⊨ M ⊑ᴸᴿ M′ ⟨ G !⟩ ⦂ (★ , ★ , unk⊑unk)
\end{code}
\begin{code}[hide]
compatible-inj-R{Γ}{G}{c}{M}{M′} ⊨M⊑M′
    with unk⊑gnd-inv c
... | d , refl = (λ γ γ′ → ℰMM′G) , λ γ γ′ → ℰMM′G
  where
  ℰMM′G : ∀{γ}{γ′}{dir}
    → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′ ⟨ G !⟩) ⦂ unk⊑unk
  ℰMM′G {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   LRₜ-bind{c = unk⊑unk}{d = unk⊑ d}{F = □}{F′ = ` (□⟨ G !⟩)}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
   LRᵥ⇒LRₜ-step{★}{★}{unk⊑unk}{V}{V′ ⟨ G !⟩}{dir}{j}
   (LRᵥ-inject-R-intro{G}{unk⊑ d}{V}{V′}{j} 𝒱VV′j )
\end{code}

\paragraph{Compatibility for Projections}

We can have a projection on the left (rule \textsf{⊑-proj-L}) or the
right (rule \textsf{⊑-proj-R}).
Starting on the left, 
\textsf{LRₜ-bind} changes the goal to $V ⟨ H ?⟩$ ⊑ᴸᴿₜ $V′$
assuming that $V$ ⊑ᴸᴿ $V′$.
We need to ensure that $V ⟨ H ?⟩$ reduces to a value without error.
Thankfully, \textsf{⊑-proj-L} says the types of $V$ and $V′$ are related
by \textsf{unk⊑ c} with $c : H ⊑ A′$, and that clause of \textsf{LRᵥ}
tells us that $V = W ⟨ H !⟩$ and
$W$ ⊑ᴸᴿᵥ $V′$. So $W ⟨ H !⟩ ⟨ H ?⟩ \longrightarrow W$
and by anti-reduction we conclude that $W ⟨ H !⟩ ⟨ H ?⟩$ ⊑ᴸᴿₜ $V′$.

\begin{code}
compatible-proj-L : ∀{Γ}{H}{A′}{c : ⌈ H ⌉ ⊑ A′}{M}{M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , A′ ,  unk⊑ c)
   → Γ ⊨ M ⟨ H ?⟩ ⊑ᴸᴿ M′ ⦂ (⌈ H ⌉ , A′ , c)
\end{code}
\begin{code}[hide]
compatible-proj-L {Γ}{H}{A′}{c}{M}{M′} ⊨M⊑M′ =
  (λ γ γ′ → ℰMHM′) , λ γ γ′ → ℰMHM′
  where
  ℰMHM′ : ∀{γ}{γ′}{dir} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
       ⊢ᵒ dir ∣ (⟪ γ ⟫ M ⟨ H ?⟩) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′) ⦂ c
  ℰMHM′ {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   LRₜ-bind{c = c}{d = unk⊑ c}{F = ` (□⟨ H ?⟩)}{F′ = □}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j → Goal{j}{V}{V′}{dir} 𝒱VV′j 
   where
   Goal : ∀{j}{V}{V′}{dir}
       → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) j
       → #(dir ∣ (V ⟨ H ?⟩) ⊑ᴸᴿₜ V′ ⦂ c) j
   Goal {zero} {V} {V′}{dir} 𝒱VV′j =
       tz (dir ∣ (V ⟨ H ?⟩) ⊑ᴸᴿₜ V′ ⦂ c)
   Goal {suc j} {V} {V′}{≼} 𝒱VV′sj
       with LRᵥ-dyn-any-elim-≼{V}{V′}{j}{H}{A′}{c} 𝒱VV′sj
   ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′j =
       let V₁HH→V₁ = collapse{H}{V = V₁} v₁ refl in
       let ℰV₁V′j = LRᵥ⇒LRₜ-step{⌈ H ⌉}{A′}{c}{V₁}{V′}{≼}{j} 𝒱V₁V′j in
       anti-reduction-≼-L-one ℰV₁V′j V₁HH→V₁
   Goal {suc j} {V} {V′}{≽} 𝒱VV′sj
       with LRᵥ-dyn-any-elim-≽{V}{V′}{j}{H}{A′}{c} 𝒱VV′sj
   ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′sj =
       let V₁HH→V₁ = collapse{H}{V = V₁} v₁ refl in
       inj₂ (inj₂ (v′ , V₁ , unit V₁HH→V₁ , v₁ , 𝒱V₁V′sj))
\end{code}

When the projection is on the right, there is less to worry about.
\textsf{LRₜ-bind} changes the goal to $V$ ⊑ᴸᴿₜ $V′ ⟨ H ?⟩$
assuming that $V$ ⊑ᴸᴿᵥ $V′$. We have $V′ = W′ ⟨ G !⟩$
and $V$ ⊑ᴸᴿᵥ $W′$.
If $G = H$ then $W′ ⟨ G !⟩⟨H ?⟩ \longrightarrow W′$
and by anti-reduction, $V$ ⊑ᴸᴿₜ $W′ ⟨ G !⟩ ⟨ H ?⟩$.
If $G ≠ H$, then $W′ ⟨ G !⟩⟨H ?⟩ \longrightarrow \textsf{blame}$.
Since $V$ ⊑ᴸᴿₜ \textsf{blame}, we use anti-reduction
to conclude $V$ ⊑ᴸᴿₜ $W′ ⟨ G !⟩⟨H ?⟩$.

\begin{AgdaSuppressSpace}
\begin{code}
compatible-proj-R : ∀{Γ}{H}{c : ★ ⊑ ⌈ H ⌉}{M}{M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , ★ , unk⊑unk)
   → Γ ⊨ M ⊑ᴸᴿ M′ ⟨ H ?⟩ ⦂ (★ , ⌈ H ⌉ , c)
\end{code}
\begin{code}[hide]
compatible-proj-R {Γ}{H}{c}{M}{M′} ⊨M⊑M′
    with unk⊑gnd-inv c
... | d , refl = (λ γ γ′ → ℰMM′H) , λ γ γ′ → ℰMM′H
    where
    ℰMM′H : ∀{γ}{γ′}{dir} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
             ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′ ⟨ H ?⟩) ⦂ unk⊑ d
    ℰMM′H {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
     LRₜ-bind{c = c}{d = unk⊑unk}{F = □}{F′ = ` □⟨ H ?⟩}
                {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
     (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
     λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
     Goal {j}{V}{V′}{dir} 𝒱VV′j 
     where
     Goal : ∀{j}{V}{V′}{dir}
        → # (dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑unk) j
        → # (dir ∣ V ⊑ᴸᴿₜ (V′ ⟨ H ?⟩) ⦂ unk⊑ d) j
     Goal {zero} {V} {V′}{dir} 𝒱VV′j =
         tz (dir ∣ V ⊑ᴸᴿₜ (V′ ⟨ H ?⟩) ⦂ unk⊑ d)
     Goal {suc j} {V₁ ⟨ G !⟩} {V′₁ ⟨ H₂ !⟩}{dir} 𝒱VV′sj
         with G ≡ᵍ H₂ | 𝒱VV′sj
     ... | no neq | ()
     ... | yes refl | v₁ , v′ , 𝒱V₁V′₁j
         with G ≡ᵍ G
     ... | no neq = ⊥-elim (neq refl)
     ... | yes refl
         with G ≡ᵍ H
         {-------- Case G ≢ H ---------}
     ... | no neq
         with dir
         {-------- Subcase ≼ ---------}
     ... | ≼ = inj₂ (inj₁ (unit (collide v′ neq refl)))
         {-------- Subcase ≽ ---------}
     ... | ≽ = anti-reduction-≽-R-one (LRₜ-blame-step{★}{⌈ H ⌉}{unk⊑ d}{≽})
                                      (collide v′ neq refl)
     Goal {suc j} {V₁ ⟨ G !⟩} {V′₁ ⟨ H₂ !⟩}{dir} 𝒱VV′sj
         | yes refl | v₁ , v′ , 𝒱V₁V′₁j | yes refl
         {-------- Case G ≡ H ---------}
         | yes refl 
         with dir
         {-------- Subcase ≼ ---------}
     ... | ≼
         with G ≡ᵍ G
     ... | no neq = ⊥-elim (neq refl)
     ... | yes refl 
         with gnd-prec-unique d Refl⊑
     ... | refl =
           let V₁G⊑V′₁sj = v₁ , v′ , 𝒱V₁V′₁j in
           inj₂ (inj₂ (v₁ 〈 G 〉 ,
                       (V′₁ , unit (collapse v′ refl) , v′ , V₁G⊑V′₁sj)))
     Goal {suc j} {V₁ ⟨ G !⟩} {V′₁ ⟨ H₂ !⟩}{dir} 𝒱VV′sj
         | yes refl | v₁ , v′ , 𝒱V₁V′₁j | yes refl
         | yes refl 
         {-------- Subcase ≽ ---------}
         | ≽
         with gnd-prec-unique d Refl⊑
     ... | refl =
         let 𝒱VGV′j = LRᵥ-inject-L-intro-≽ {G}{⌈ G ⌉}{d} 𝒱V₁V′₁j in
         let ℰVGV′j = LRᵥ⇒LRₜ-step{V = V₁ ⟨ G !⟩}{V′₁}{≽} 𝒱VGV′j in
         anti-reduction-≽-R-one ℰVGV′j (collapse v′ refl)
\end{code}
\end{AgdaSuppressSpace}

\paragraph{Fundamental Theorem}

The proof is by induction on $M ⊑ M′$, using the appropriate
Compatibility Lemma in each case.

\begin{code}
fundamental : ∀ {Γ}{A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
  → Γ ⊩ M ⊑ M′ ⦂ A⊑A′  →  Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (A , A′ , A⊑A′)
\end{code}
\begin{code}[hide]
fundamental {Γ} {A} {A′} {A⊑A′} .(` _) .(` _) (⊑-var ∋x) =
    compatibility-var ∋x
fundamental {Γ} {_} {_} {base⊑} ($ c) ($ c) ⊑-lit =
    compatible-literal
fundamental {Γ} {A} {A′} {A⊑A′} (L · M) (L′ · M′) (⊑-app ⊢L⊑L′ ⊢M⊑M′) =
    compatible-app{L = L}{L′}{M}{M′} (fundamental L L′ ⊢L⊑L′) (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(fun⊑ _ _)} (ƛ N)(ƛ N′) (⊑-lam ⊢N⊑N′) =
    compatible-lambda{N = N}{N′} (fundamental N N′ ⊢N⊑N′)
fundamental {Γ} {★} {A′} {unk⊑ c} (M ⟨ G !⟩) M′ (⊑-inj-L ⊢M⊑M′) =
    compatible-inj-L{G =  G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {★} {★} {.unk⊑unk} M (M′ ⟨ G !⟩) (⊑-inj-R ⊢M⊑M′) =
    compatible-inj-R{Γ}{G = G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {_} {A′} {A⊑A′} (M ⟨ H ?⟩) M′ (⊑-proj-L ⊢M⊑M′) =
    compatible-proj-L{Γ}{H}{A′}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.(⌈ _ ⌉)} {A⊑A′} M (M′ ⟨ H′ ?⟩) (⊑-proj-R ⊢M⊑M′) =
    compatible-proj-R{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.A} {.Refl⊑} M .blame (⊑-blame ⊢M∶A) =
    compatible-blame ⊢M∶A
\end{code}


% LocalWords:  LogRel PeterFundamental elim Bool proj inj tt Eq refl
% LocalWords:  sym cong subst trans Nullary Var Sig PeterCastCalculus
% LocalWords:  PeterFestschrift StepIndexedLogic LR dir suc tz Prec
% LocalWords:  isBlame var LT GT ext ABT SIL fixpoint pre IH app Agda
% LocalWords:  ponens de Bruijn Agda's MN NN si MV VM Nsi PEFrame sz
% LocalWords:  FMF FMFN VV WW sj NWN LM NWNW unk sk neq MGM dyn VGV
% LocalWords:  gnd inv prec MHM HH Subcase lam
