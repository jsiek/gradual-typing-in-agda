\begin{code}[hide]
{-# OPTIONS --rewriting --prop #-}
module LogRel.PeterFundamental2 where

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
open import PropP
open import LogRel.PeterCastCalculus
open import LogRel.PeterPrecision
open import LogRel.PeterLogRel2
open import StepIndexedLogic2
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

\begin{code}
compatible-literal : ∀{Γ}{c}{ι} → Γ ⊨ $ c ⊑ᴸᴿ $ c ⦂ ($ₜ ι , $ₜ ι , base⊑)
\end{code}
\begin{code}[hide]
compatible-literal {Γ}{c}{ι} = (λ γ γ′ → LRᵥ⇒LRₜ c⊑c) ,ₚ (λ γ γ′ → LRᵥ⇒LRₜ c⊑c)
  where
  LRᵥcc : ∀{𝒫}{dir} → 𝒫 ⊢ᵒ letᵒ (μᵒ pre-LRₜ⊎LRᵥ) (LRᵥ (base⊑{ι}) dir ($ c) ($ c))
  LRᵥcc{𝒫}{dir}
      with dec-LRᵥCases (base⊑{ι}) ($ c) ($ c)
  ... | yes (LRᵥ-base⊑{ι}{c}) = pureᵒI refl
  ... | no ncs = ⊥-elimₚ (⊥-elimₛ (ncs LRᵥ-base⊑))
  
  c⊑c : ∀{𝒫}{dir} → 𝒫 ⊢ᵒ dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}
  c⊑c{𝒫}{dir} = foldᵒ pre-LRₜ⊎LRᵥ (inj₁ (($ₜ ι , $ₜ ι , base⊑{ι}) , dir , $ c , $ c)) (LRᵥcc{𝒫}{dir})
\end{code}

\noindent The proof of compatibility for blame is direct from the definitions.

\begin{code}
compatible-blame : ∀{Γ}{A}{M} → map proj₁ Γ ⊢ M ⦂ A → Γ ⊨ M ⊑ᴸᴿ blame ⦂ (A , A , Refl⊑)
\end{code}
\begin{code}[hide]
compatible-blame{Γ}{A}{M} ⊢M = (λ γ γ′ → LRₜ-blame) ,ₚ (λ γ γ′ → LRₜ-blame)
  where
  LRₜ-blame : ∀{𝒫}{A}{A′}{A⊑A′ : A ⊑ A′}{M}{dir} → 𝒫 ⊢ᵒ dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′
  LRₜ-blame {𝒫} {A} {A′} {A⊑A′} {M} {≼} =
      foldᵒ pre-LRₜ⊎LRᵥ (inj₂ ((A , A′ , A⊑A′) , ≼ , M , blame))
      (inj₂ᵒ (inj₁ᵒ (pureᵒI (blame END))))
  LRₜ-blame {𝒫} {A} {A′} {A⊑A′} {M} {≽} =
      foldᵒ pre-LRₜ⊎LRᵥ (inj₂ ((A , A′ , A⊑A′) , ≽ , M , blame))
      (inj₂ᵒ (inj₁ᵒ (pureᵒI isBlame)))
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
compatibility-var {Γ}{A}{A′}{A⊑A′}{x} ∋x = LT ,ₚ GT
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

\begin{code}
compatible-lambda : ∀{Γ : List Prec}{A}{B}{C}{D}{N N′ : Term}{c : A ⊑ C}{d : B ⊑ D}
   → ((A , C , c) ∷ Γ) ⊨ N ⊑ᴸᴿ N′ ⦂ (B , D , d)
   → Γ ⊨ (ƛ N) ⊑ᴸᴿ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ =
  (λ γ γ′ → LRᵥ⇒LRₜ ⊢λN⊑λN′) ,ₚ (λ γ γ′ → LRᵥ⇒LRₜ ⊢λN⊑λN′)
 where ⊢λN⊑λN′ : ∀{dir}{γ}{γ′} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
                 ⊢ᵒ (dir ∣ ⟪ γ ⟫ (ƛ N) ⊑ᴸᴿᵥ ⟪ γ′ ⟫ (ƛ N′) ⦂ fun⊑ c d)
       ⊢λN⊑λN′ {dir}{γ}{γ′} =
         foldᵒ pre-LRₜ⊎LRᵥ (inj₁ ((A ⇒ B , C ⇒ D , fun⊑ c d) , dir , ⟪ γ ⟫ (ƛ N) , ⟪ γ′ ⟫ (ƛ N′)))
         (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI 
           let IH = (proj dir N N′ ⊨N⊑N′) (W • γ) (W′ • γ′) in
           (→ᵒE (Sᵒ (▷→ (monoᵒ (→ᵒI IH)))) Zᵒ))
\end{code}

We note that the use of SIL in the above proof comes with some
tradeoffs. On the one hand, there is no explicit reasoning about step
indices. On the other hand, there is some added verbosity compared to
a proof in raw Agda such as the use of \textsf{appᵒ} for modus-ponens,
the use of de Bruijn indices \textsf{Zᵒ} to refer to premises,
and extra annotations such as \textsf{{P = ▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c)}}
that are needed when Agda's type inference fails.

\paragraph{Anti-reduction and Bind Lemmas}

The remaining compatibility lemmas, for function application and for
injections and projections, require several anti-reduction lemmas
which state that if two terms are in the logical relation, then
walking backwards with one or both of them yields terms that are still
in the logical relation. Here we list just one of them. 

\begin{code}[hide]
anti-reduction-≼-R-one : ∀{𝒫}{A}{A′}{A⊑A′ : A ⊑ A′}{M′}{N′}
  → 𝒫 ⊢ᵒ (∀ᵒ[ M ]  (≼ ∣ M ⊑ᴸᴿₜ N′ ⦂ A⊑A′)  →ᵒ  (M′ ⟶ N′)ᵒ  →ᵒ  (≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′))
anti-reduction-≼-R-one{𝒫}{A}{A′}{A⊑A′}{M′}{N′} =
   lobᵒ
   (Λᵒ[ M ] (→ᵒI (→ᵒI
   (case3ᵒ (unfoldᵒ pre-LRₜ⊎LRᵥ (inj₂ ((A , A′ , A⊑A′) , ≼ , M , N′)) (Sᵒ Zᵒ))
   (∃ᵒE Zᵒ λ N → foldᵒ pre-LRₜ⊎LRᵥ (inj₂ ((A , A′ , A⊑A′) , ≼ , M , M′))
      (inj₁ᵒ (∃ᵒI N (proj₁ᵒ Zᵒ ,ᵒ
      let IH = (Sᵒ (Sᵒ (Sᵒ (Sᵒ Zᵒ)))) in
      let ▷N⊑M′ : _ ⊢ᵒ ▷ᵒ (≼ ∣ N ⊑ᴸᴿₜ M′ ⦂ A⊑A′)
          ▷N⊑M′ = →ᵒE (▷→ (→ᵒE (▷→ (∀ᵒE (▷∀ IH) N)) (proj₂ᵒ Zᵒ))) (monoᵒ (Sᵒ (Sᵒ Zᵒ))) in
      ▷N⊑M′))))
   (pureᵒE (Sᵒ Zᵒ) λ M′→N′ → pureᵒE Zᵒ λ N′→blame →
     foldᵒ pre-LRₜ⊎LRᵥ (inj₂ ((A , A′ , A⊑A′) , ≼ , M , M′))
     (inj₂ᵒ (inj₁ᵒ (pureᵒI (M′ ⟶⟨ M′→N′ ⟩ N′→blame)))))
   (foldᵒ pre-LRₜ⊎LRᵥ (inj₂ ((A , A′ , A⊑A′) , ≼ , M , M′))
    (pureᵒE (Sᵒ Zᵒ) λ M′→N′ →
    (inj₂ᵒ (inj₂ᵒ
    (∃ᵒE (proj₂ᵒ Zᵒ) λ V′ → proj₁ᵒ (Sᵒ Zᵒ) ,ᵒ ∃ᵒI V′
    (pureᵒE (proj₁ᵒ Zᵒ) λ N′→V′ →
      (pureᵒI (M′ ⟶⟨ M′→N′ ⟩ N′→V′) ,ᵒ ((proj₁ᵒ (proj₂ᵒ Zᵒ)) ,ᵒ proj₂ᵒ (proj₂ᵒ Zᵒ)))))))))
    ))))
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

\begin{code}
compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ᴸᴿ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d) → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (A , A′ , c)
   → Γ ⊨ L · M ⊑ᴸᴿ L′ · M′ ⦂ (B , B′ , d)
\end{code}
\begin{code}[hide]
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′} ⊨L⊑L′ ⊨M⊑M′ =
 (λ γ γ′ → ⊢LM⊑LM′) ,ₚ λ γ γ′ → ⊢LM⊑LM′
 where
 ⊢LM⊑LM′ : ∀{dir}{γ}{γ′} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
             ⊢ᵒ dir ∣ ⟪ γ ⟫ (L · M) ⊑ᴸᴿₜ ⟪ γ′ ⟫ (L′ · M′) ⦂ d
 ⊢LM⊑LM′ {dir}{γ}{γ′} =
   foldᵒ pre-LRₜ⊎LRᵥ (inj₂ ((B , B′ , d) , dir , ⟪ γ ⟫ (L · M) , ⟪ γ′ ⟫ (L′ · M′)))
   {!!}
\end{code}
