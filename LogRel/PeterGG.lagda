\begin{code}[hide]
{-# OPTIONS --rewriting #-}
module LogRel.PeterGG where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)

open import LogRel.PeterCastCalculus
open import LogRel.PeterFestschrift
open import LogRel.PeterFundamental
open import StepIndexedLogic
\end{code}

\section{Proof of the Gradual Guarantee}
\label{sec:gradual-guarantee}

\begin{code}[hide]
_⊨_⊑_for_ : Dir → Term → Term → ℕ → Set
≼ ⊨ M ⊑ M′ for k = (M ⇓ × M′ ⇓) ⊎ (M′ ↠ blame) ⊎ ∃[ N ] Σ[ r ∈ M ↠ N ] len r ≡ k
≽ ⊨ M ⊑ M′ for k = (M ⇓ × M′ ⇓) ⊎ (M′ ↠ blame) ⊎ ∃[ N′ ] Σ[ r ∈ M′ ↠ N′ ] len r ≡ k
\end{code}
\begin{code}[hide]
⊨_⊑_for_ : Term → Term → ℕ → Set
⊨ M ⊑ M′ for k = (≼ ⊨ M ⊑ M′ for k) × (≽ ⊨ M ⊑ M′ for k)
\end{code}
\begin{code}[hide]
LR⇒sem-approx : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}{k}{dir}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k)  →  dir ⊨ M ⊑ M′ for k
\end{code}
\begin{code}[hide]
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {zero} {≼} M⊑M′sk =
    inj₂ (inj₂ (M , (M END) , refl))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {suc k} {≼} M⊑M′sk
    with ⇔-to (LRₜ-suc{dir = ≼}) M⊑M′sk
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (m , (V′ , M′→V′ , v′ , 𝒱≼V′M))) =
      inj₁ ((M , (M END) , m) , (V′ , M′→V′ , v′))
... | inj₁ (N , M→N , ▷N⊑M′)
    with LR⇒sem-approx{dir = ≼} ▷N⊑M′
... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
      inj₁ ((V , (M ⟶⟨ M→N ⟩ M→V) , v) , (V′ , M′→V′ , v′))
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (L , N→L , eq)) =
      inj₂ (inj₂ (L , (M ⟶⟨ M→N ⟩ N→L) , cong suc eq))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {zero} {≽} M⊑M′sk =
    inj₂ (inj₂ (M′ , (M′ END) , refl))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {suc k} {≽} M⊑M′sk
    with ⇔-to (LRₜ-suc{dir = ≽}) M⊑M′sk
... | inj₂ (inj₁ isBlame) =
      inj₂ (inj₁ (blame END))
... | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱≽VM′)) =
      inj₁ ((V , M→V , v) , M′ , (M′ END) , m′)
... | inj₁ (N′ , M′→N′ , ▷M⊑N′)
    with LR⇒sem-approx{dir = ≽} ▷M⊑N′
... | inj₁ ((V , M→V , v) , (V′ , N′→V′ , v′)) =
      inj₁ ((V , M→V , v) , V′ , (M′ ⟶⟨ M′→N′ ⟩ N′→V′) , v′)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′ ⟶⟨ M′→N′ ⟩ N′→blame))
... | inj₂ (inj₂ (L′ , N′→L′ , eq)) =
      inj₂ (inj₂ (L′ , (M′ ⟶⟨ M′→N′ ⟩ N′→L′) , cong suc eq))
\end{code}
\begin{code}[hide]
sem-approx⇒GG : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}
   → (∀ k → ⊨ M ⊑ M′ for k)  →  gradual M M′
\end{code}
\begin{code}[hide]
sem-approx⇒GG {A}{A′}{A⊑A′}{M}{M′} ⊨M⊑M′ =
  to-value-right , diverge-right , to-value-left , diverge-left , blame-blame
  where
  to-value-right : M′ ⇓ → M ⇓
  to-value-right (V′ , M′→V′ , v′)
      with proj₂ (⊨M⊑M′ (suc (len M′→V′)))
  ... | inj₁ ((V , M→V , v) , _) = V , M→V , v
  ... | inj₂ (inj₁ M′→blame) =
        ⊥-elim (cant-reduce-value-and-blame v′ M′→V′ M′→blame)
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) =
        ⊥-elim (step-value-plus-one M′→N′ M′→V′ v′ eq)
        
  diverge-right : M′ ⇑ → M ⇑
  diverge-right divM′ k
      with proj₁ (⊨M⊑M′ k)
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
        ⊥-elim (diverge-not-halt divM′ (inj₂ (V′ , M′→V′ , v′)))
  ... | inj₂ (inj₁ M′→blame) =
        ⊥-elim (diverge-not-halt divM′ (inj₁ M′→blame))
  ... | inj₂ (inj₂ (N , M→N , eq)) = N , M→N , sym eq

  to-value-left : M ⇓ → M′ ⇓ ⊎ M′ ↠ blame
  to-value-left (V , M→V , v)
      with proj₁ (⊨M⊑M′ (suc (len M→V)))
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) = inj₁ (V′ , M′→V′ , v′)
  ... | inj₂ (inj₁ M′→blame) = inj₂ M′→blame
  ... | inj₂ (inj₂ (N , M→N , eq)) =
        ⊥-elim (step-value-plus-one M→N M→V v eq)

  diverge-left : M ⇑ → M′ ⇑⊎blame
  diverge-left divM k 
      with proj₂ (⊨M⊑M′ k)
  ... | inj₁ ((V , M→V , v) , _) =
        ⊥-elim (diverge-not-halt divM (inj₂ (V , M→V , v)))
  ... | inj₂ (inj₁ M′→blame) = blame , (M′→blame , (inj₂ refl))
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) = N′ , (M′→N′ , (inj₁ (sym eq))) 

  blame-blame : (M ↠ blame → M′ ↠ blame)
  blame-blame M→blame
      with proj₁ (⊨M⊑M′ (suc (len M→blame)))
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
        ⊥-elim (cant-reduce-value-and-blame v M→V M→blame)
  ... | inj₂ (inj₁ M′→blame) = M′→blame
  ... | inj₂ (inj₂ (N , M→N , eq)) =
        ⊥-elim (step-blame-plus-one M→N M→blame eq)
\end{code}

The last lemma needed to complete the proof of the gradual guarantee
is to connect the logical relation to the behavior that's required by
the gradual guarantee. (Recall the \textsf{gradual} predicate defined
in Section~\ref{sec:precision}.) The proof goes through an
intermediate step that uses a notion of semantic approximation for a
fixed number of reduction steps and that relies on a proof of
determinism for the Cast Calculus.

\begin{code}
LR⇒GG : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}  → [] ⊢ᵒ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′  →  gradual M M′ 
\end{code}
\begin{code}[hide]
LR⇒GG {A}{A′}{A⊑A′}{M}{M′} ⊨M⊑M′ =
  sem-approx⇒GG{A⊑A′ = A⊑A′} (λ k → ≼⊨M⊑M′ , ≽⊨M⊑M′)
  where
  ≼⊨M⊑M′ : ∀{k} → ≼ ⊨ M ⊑ M′ for k
  ≼⊨M⊑M′ {k} = LR⇒sem-approx {k = k}{dir = ≼}
                   (⊢ᵒ-elim (proj₁ᵒ ⊨M⊑M′) (suc k) tt) 
  ≽⊨M⊑M′ : ∀{k} → ≽ ⊨ M ⊑ M′ for k
  ≽⊨M⊑M′ {k} = LR⇒sem-approx {k = k}{dir = ≽}
                   (⊢ᵒ-elim (proj₂ᵒ ⊨M⊑M′) (suc k) tt)
\end{code}

\noindent The gradual guarantee then follows by use of the Fundamental
Lemma to obtain $M$ ⊑ᴸᴿₜ $M′$ and then \textsf{LR⇒GG} to
conclude that \textsf{gradual M M′}.

\begin{code}
gradual-guarantee : ∀ {A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
   → [] ⊩ M ⊑ M′ ⦂ A⊑A′  →  gradual M M′ 
gradual-guarantee {A}{A′}{A⊑A′} M M′ M⊑M′ =
  let (⊨≼M⊑ᴸᴿM′ , ⊨≽M⊑ᴸᴿM′) = fundamental M M′ M⊑M′ in
  LR⇒GG (⊨≼M⊑ᴸᴿM′ id id ,ᵒ ⊨≽M⊑ᴸᴿM′ id id)
\end{code}


% LocalWords:  LogRel PeterGG elim proj inj tt Eq refl sym cong subst
% LocalWords:  trans PeterCastCalculus PeterFestschrift Dir len LR sk
% LocalWords:  PeterFundamental StepIndexedLogic sem approx dir suc
% LocalWords:  eq isBlame VM GG divM
