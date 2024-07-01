\begin{code}[hide]
{-# OPTIONS --rewriting #-}
module LogRel.PeterFestschrift where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Var
open import InjProj.CastCalculus
open import InjProj.CastDeterministic
open import StepIndexedLogic
\end{code}


\begin{code}
infixr 6 _⊑_
data _⊑_ : Type → Type → Set where
  unk⊑unk : ★ ⊑ ★
  unk⊑ : ∀{G}{B} → gnd⇒ty G ⊑ B → ★ ⊑ B
  base⊑ : ∀{ι} → $ₜ ι ⊑ $ₜ ι
  fun⊑ : ∀{A B C D}  →  A ⊑ C  →  B ⊑ D  →  A ⇒ B ⊑ C ⇒ D
\end{code}

\begin{code}
Prec : Set
Prec = (∃[ A ] ∃[ B ] A ⊑ B)
\end{code}

\begin{code}
Refl⊑ : ∀{A} → A ⊑ A
Refl⊑ {★} = unk⊑unk
Refl⊑ {$ₜ ι} = base⊑
Refl⊑ {A ⇒ B} = fun⊑ Refl⊑ Refl⊑
\end{code}

\begin{code}[hide]
unk⊑gnd-inv : ∀{G}
   → (c : ★ ⊑ gnd⇒ty G)
   → ∃[ d ] c ≡ unk⊑{G}{gnd⇒ty G} d
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
   → (c : gnd⇒ty G ⊑ A)
   → (d : gnd⇒ty G ⊑ A)
   → c ≡ d
gnd-prec-unique {$ᵍ ι} {.($ₜ ι)} base⊑ base⊑ = refl
gnd-prec-unique {★⇒★} {.(_ ⇒ _)} (fun⊑ c c₁) (fun⊑ d d₁)
    with dyn-prec-unique c d | dyn-prec-unique c₁ d₁
... | refl | refl = refl
\end{code}

Figure~\ref{fig:term-precision}

\begin{figure}[tbp]
\begin{code}
infix 3 _⊩_⊑_⦂_
data _⊩_⊑_⦂_ : List Prec → Term → Term → ∀{A B : Type} → A ⊑ B → Set  where

  ⊑-var : ∀ {Γ x A⊑B}
      →  Γ ∋ x ⦂ A⊑B
      →  Γ ⊩ (` x) ⊑ (` x) ⦂ proj₂ (proj₂ A⊑B)

  ⊑-lit : ∀ {Γ c} →  Γ ⊩ ($ c) ⊑ ($ c) ⦂ base⊑{typeof c}

  ⊑-app : ∀{Γ L M L′ M′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → Γ ⊩ L ⊑ L′ ⦂ fun⊑ c d  →  Γ ⊩ M ⊑ M′ ⦂ c
     → Γ ⊩ L · M ⊑ L′ · M′ ⦂ d

  ⊑-lam : ∀{Γ N N′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → (A , C , c) ∷ Γ ⊩ N ⊑ N′ ⦂ d
     → Γ ⊩ ƛ N ⊑ ƛ N′ ⦂ fun⊑ c d

  ⊑-inj-L : ∀{Γ M M′}{G B}{c : (gnd⇒ty G) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ c
     → Γ ⊩ M ⟨ G !⟩ ⊑ M′ ⦂ unk⊑{G}{B} c

  ⊑-inj-R : ∀{Γ M M′}{G}{c : ★ ⊑ (gnd⇒ty G)}
     → Γ ⊩ M ⊑ M′ ⦂ c
     → Γ ⊩ M ⊑ M′ ⟨ G !⟩ ⦂ unk⊑unk

  ⊑-proj-L : ∀{Γ M M′ H B}{c : (gnd⇒ty H) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑ c
     → Γ ⊩ M ⟨ H ?⟩ ⊑ M′ ⦂ c

  ⊑-proj-R : ∀{Γ M M′ H}{c : ★ ⊑ (gnd⇒ty H)}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑unk
     → Γ ⊩ M ⊑ M′ ⟨ H ?⟩  ⦂ c

  ⊑-blame : ∀{Γ M A}
     → map proj₁ Γ ⊢ M ⦂ A
     → Γ ⊩ M ⊑ blame ⦂ Refl⊑{A}
\end{code}
\caption{Precision Relation on Terms}
\label{fig:term-precision}
\end{figure}

\begin{code}
data Dir : Set where
  ≼ : Dir
  ≽ : Dir
  
LR-type : Set
LR-type = (Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)

LR-ctx : Context
LR-ctx = LR-type ∷ []

LRᵥ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)
LRₜ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)

_∣_ˢ⊑ᴸᴿₜ_⦂_ : Dir → Term → Term → ∀{A}{A′} (A⊑A′ : A ⊑ A′)
   → Setˢ LR-ctx (cons Now ∅)
dir ∣ M ˢ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = (inj₂ ((_ , _ , A⊑A′) , dir , M , M′)) ∈ zeroˢ

_∣_ˢ⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A}{A′} (A⊑A′ : A ⊑ A′)
   → Setˢ LR-ctx (cons Now ∅)
dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ = (inj₁ ((_ , _ , A⊑A′) , dir , V , V′)) ∈ zeroˢ

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }
\end{code}

Figure~\ref{fig:log-rel-precision}

\begin{figure}[tbp]
\begin{code}
LRₜ (A , A′ , c) ≼ M M′ =
   (∃ˢ[ N ] (M —→ N)ˢ ×ˢ ▷ˢ (≼ ∣ N ˢ⊑ᴸᴿₜ M′ ⦂ c))
   ⊎ˢ (M′ —↠ blame)ˢ
   ⊎ˢ ((Value M)ˢ ×ˢ (∃ˢ[ V′ ] (M′ —↠ V′)ˢ ×ˢ (Value V′)ˢ ×ˢ (LRᵥ (_ , _ , c) ≼ M V′)))
LRₜ (A , A′ , c) ≽ M M′ =
   (∃ˢ[ N′ ] (M′ —→ N′)ˢ ×ˢ ▷ˢ (≽ ∣ M ˢ⊑ᴸᴿₜ N′ ⦂ c))
   ⊎ˢ (Blame M′)ˢ
   ⊎ˢ ((Value M′)ˢ ×ˢ (∃ˢ[ V ] (M —↠ V)ˢ ×ˢ (Value V)ˢ ×ˢ (LRᵥ (_ , _ , c) ≽ V M′)))
\end{code}

\begin{code}
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir ($ c) ($ c′) = (c ≡ c′) ˢ
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir V V′ = ⊥ ˢ
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir (ƛ N)(ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (dir ∣ W ˢ⊑ᴸᴿᵥ W′ ⦂ A⊑A′)
                  →ˢ ▷ˢ (dir ∣ (N [ W ]) ˢ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′) 
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir V V′ = ⊥ ˢ
LRᵥ (.★ , .★ , unk⊑unk) dir (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (▷ˢ (dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ Refl⊑{gnd⇒ty G}))
... | no neq = ⊥ ˢ
LRᵥ (.★ , .★ , unk⊑unk) dir V V′ = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≼ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ ▷ˢ (≼ ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ d)
... | no neq = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≽ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (LRᵥ (gnd⇒ty G , A′ , d) ≽ V V′)
... | no neq = ⊥ ˢ
LRᵥ (★ , .A′ , unk⊑{H}{A′} d) dir V V′ = ⊥ ˢ
\end{code}

\caption{Logical Relation for Precision on Terms $\mathsf{LR}_t$
  and Values $\mathsf{LR}_v$}
\label{fig:log-rel-precision}
\end{figure}

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

The relations that we have defined so far, $⊑^{LR}ᵥ$ and $⊑^{LR}ₜ$, only
apply to closed terms, that is, terms with no free variables.  We also
need to related open terms. The standard way to do that is to apply
two substitutions to the two terms, replacing each free variable with
related values.

We relate a pair of substitutions $γ$ and $γ′$ with the following
definition , which says that the substitutions must be pointwise
related using the logical relation for values.

\begin{code}
_∣_⊨_⊑ᴸᴿ_ : (Γ : List Prec) → Dir → Subst → Subst → List Setᵒ
[] ∣ dir ⊨ γ ⊑ᴸᴿ γ′ = []
((_ , _ , A⊑A′) ∷ Γ) ∣ dir ⊨ γ ⊑ᴸᴿ γ′ = (dir ∣ (γ 0) ⊑ᴸᴿᵥ (γ′ 0) ⦂ A⊑A′)
                     ∷ (Γ ∣ dir ⊨ (λ x → γ (suc x)) ⊑ᴸᴿ (λ x → γ′ (suc x)))
\end{code}


\begin{code}
_∣_⊨_⊑ᴸᴿ_⦂_ : List Prec → Dir → Term → Term → Prec → Set
Γ ∣ dir ⊨ M ⊑ᴸᴿ M′ ⦂ (_ , _ , A⊑A′) = ∀ (γ γ′ : Subst)
   → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′) ⦂ A⊑A′
\end{code}

\begin{code}
_⊨_⊑ᴸᴿ_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ᴸᴿ M′ ⦂ c = (Γ ∣ ≼ ⊨ M ⊑ᴸᴿ M′ ⦂ c) × (Γ ∣ ≽ ⊨ M ⊑ᴸᴿ M′ ⦂ c)

proj : ∀ {Γ}{c} → (dir : Dir) → (M M′ : Term) → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ c → Γ ∣ dir ⊨ M ⊑ᴸᴿ M′ ⦂ c
proj ≼ M M′ M⊑M′ = proj₁ M⊑M′
proj ≽ M M′ M⊑M′ = proj₂ M⊑M′
\end{code}

Reasoning about the logical relation

Unfortunately, there is some overhead to using the StepIndexedLogic to
define the logical relation. One needs to use the `fixpointᵒ` theorem
to obtain usable definitions.

The following states what we would like the `⊑ᴸᴿₜ` relation to look
like.

\begin{code}
LRₜ-def : ∀{A}{A′} → (A⊑A′ : A ⊑ A′) → Dir → Term → Term → Setᵒ
LRₜ-def A⊑A′ ≼ M M′ =
   (∃ᵒ[ N ] (M —→ N)ᵒ ×ᵒ ▷ᵒ (≼ ∣ N ⊑ᴸᴿₜ M′ ⦂ A⊑A′))
   ⊎ᵒ (M′ —↠ blame)ᵒ
   ⊎ᵒ ((Value M)ᵒ ×ᵒ 
              (∃ᵒ[ V′ ] (M′ —↠ V′)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (≼ ∣ M ⊑ᴸᴿᵥ V′ ⦂ A⊑A′)))
LRₜ-def A⊑A′ ≽ M M′ =
   (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (≽ ∣ M ⊑ᴸᴿₜ N′ ⦂ A⊑A′))
   ⊎ᵒ (Blame M′)ᵒ
   ⊎ᵒ ((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ
                               ×ᵒ (≽ ∣ V ⊑ᴸᴿᵥ M′ ⦂ A⊑A′)))
\end{code}

We prove that the above is equivalent to `⊑ᴸᴿₜ` with the following lemma,
using the `fixpointᵒ` theorem in several places.

\begin{code}
LRₜ-stmt : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}
   → dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ ≡ᵒ LRₜ-def A⊑A′ dir M M′
LRₜ-stmt {A}{A′}{A⊑A′}{dir}{M}{M′} =
  dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′
                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-LRₜ⊎LRᵥ (X₂ dir)
                 ⩦⟨ fixpointᵒ pre-LRₜ⊎LRᵥ (X₂ dir) ⟩
  # (pre-LRₜ⊎LRᵥ (X₂ dir)) (LRₜ⊎LRᵥ , ttᵖ)
                 ⩦⟨ EQ{dir} ⟩
  LRₜ-def A⊑A′ dir M M′
  ∎
  where
  c = (A , A′ , A⊑A′)
  X₁ : Dir → LR-type
  X₁ = λ dir → inj₁ (c , dir , M , M′)
  X₂ = λ dir → inj₂ (c , dir , M , M′)
  EQ : ∀{dir} → # (pre-LRₜ⊎LRᵥ (X₂ dir)) (LRₜ⊎LRᵥ , ttᵖ)
                ≡ᵒ LRₜ-def A⊑A′ dir M M′
  EQ {≼} = cong-⊎ᵒ (≡ᵒ-refl refl)
           (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) 
             (cong-∃ λ V′ → cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
              ((≡ᵒ-sym (fixpointᵒ pre-LRₜ⊎LRᵥ (inj₁ (c , ≼ , M , V′)))))))))
  EQ {≽} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ λ V → cong-×ᵒ (≡ᵒ-refl refl)
              (cong-×ᵒ (≡ᵒ-refl refl)
               (≡ᵒ-sym (fixpointᵒ pre-LRₜ⊎LRᵥ (inj₁ (c , ≽ , V , M′))))))))
\end{code}

In situations where we need to reason with an explicit step index `k`,
we use the following corollary.

\begin{code}
LRₜ-suc : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}{k}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k) ⇔ #(LRₜ-def A⊑A′ dir M M′) (suc k)
LRₜ-suc {A}{A′}{A⊑A′}{dir}{M}{M′}{k} =
   ≡ᵒ⇒⇔{k = suc k} (LRₜ-stmt{A}{A′}{A⊑A′}{dir}{M}{M′})
\end{code}

The definitionn of `⊑ᴸᴿᵥ` included several clauses that ensured that
the related values are indeed syntactic values. Here we make use of
that to prove that indeed, logically related values are syntactic
values.

\begin{code}
LRᵥ⇒Value : ∀ {k}{dir}{A}{A′} (A⊑A′ : A ⊑ A′) M M′
   → # (dir ∣ M ⊑ᴸᴿᵥ M′ ⦂ A⊑A′) (suc k)
     ----------------------------
   → Value M × Value M′
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

If two values are related via $⊑^{LR}ᵥ$, then they are also related
via $⊑̂{LR}ₜ$.

\begin{code}
LRᵥ⇒LRₜ-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{V V′}{dir}{k}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′) k
     ---------------------------
   → #(dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′) k
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

LRᵥ⇒LRₜ : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{𝒫}{V V′}{dir}
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′
     ---------------------------
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′
LRᵥ⇒LRₜ {A}{A′}{A⊑A′}{𝒫}{V}{V′}{dir} ⊢𝒱VV′ = ⊢ᵒ-intro λ k 𝒫k →
  LRᵥ⇒LRₜ-step{V = V}{V′}{dir}{k} (⊢ᵒ-elim ⊢𝒱VV′ k 𝒫k)
\end{code}

\begin{code}
LRᵥ-base-intro : ∀{𝒫}{ι}{c}{dir}
   → 𝒫 ⊢ᵒ dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}
LRᵥ-base-intro{𝒫}{ι}{c}{dir} = ⊢ᵒ-intro λ k 𝒫k → step {ι}{dir}{c}{k}
  where
  step : ∀{ι}{dir}{c}{k} → # (dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}) k
  step {ι} {dir} {c} {zero} = tt
  step {ι} {dir} {c} {suc k} = refl
\end{code}

\begin{code}
compatible-literal : ∀{Γ}{c}{ι} → Γ ⊨ $ c ⊑ᴸᴿ $ c ⦂ ($ₜ ι , $ₜ ι , base⊑)
compatible-literal {Γ}{c}{ι} =
  (λ γ γ′ → LRᵥ⇒LRₜ LRᵥ-base-intro) , (λ γ γ′ → LRᵥ⇒LRₜ LRᵥ-base-intro)
\end{code}



\begin{code}
anti-reduction-≼-L-one : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≼ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i
  → (M→N : M —→ N)
    ----------------------------
  → #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
anti-reduction-≼-L-one {c = c} {M} {N} {M′} {i} ℰ≼NM′i M→N =
  inj₁ (N , M→N , ℰ≼NM′i)

anti-reduction-≼-R-one : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≼ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M′→N′ : M′ —→ N′)
  → #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
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

anti-reduction-≽-L-one : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≽ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i
  → (M→N : M —→ N)
  → #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≽-L-one {c = c}{M} {N}{M′} {zero} ℰNM′ M→N =
    tz (≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c)
anti-reduction-≽-L-one {M = M} {N}{M′}  {suc i} ℰNM′ M→N
    with ℰNM′
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      inj₁ (N′ , (M′→N′ , (anti-reduction-≽-L-one ▷ℰMN′ M→N)))
... | inj₂ (inj₁ isBlame) = inj₂ (inj₁ isBlame)
... | inj₂ (inj₂ (m′ , V , N→V , v , 𝒱VM′)) =
      inj₂ (inj₂ (m′ , V , (unit M→N ++ N→V) , v , 𝒱VM′))

anti-reduction-≽-R-one : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≽ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M′→N′ : M′ —→ N′)
  → #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
anti-reduction-≽-R-one {c = c} {M} {M′}{N′} {i} ℰ≽MN′ M′→N′ =
  inj₁ (N′ , M′→N′ , ℰ≽MN′)

anti-reduction : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{N′}{i}{dir}
  → #(dir ∣ N ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M→N : M —→ N)
  → (M′→N′ : M′ —→ N′)
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
anti-reduction {c = c} {M} {N} {M′} {N′} {i} {≼} ℰNN′i M→N M′→N′ =
  let ℰMN′si = anti-reduction-≼-L-one ℰNN′i M→N in
  let ℰM′N′si = anti-reduction-≼-R-one ℰMN′si M′→N′ in
  ℰM′N′si
anti-reduction {c = c} {M} {N} {M′} {N′} {i} {≽} ℰNN′i M→N M′→N′ =
  let ℰM′Nsi = anti-reduction-≽-R-one ℰNN′i M′→N′ in
  let ℰM′N′si = anti-reduction-≽-L-one ℰM′Nsi M→N in
  ℰM′N′si

anti-reduction-≼-R : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≼ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M′→N′ : M′ —↠ N′)
  → #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≼-R {M′ = M′} ℰMN′ (.M′ END) = ℰMN′
anti-reduction-≼-R {M′ = M′} {N′} {i} ℰMN′ (.M′ —→⟨ M′→L′ ⟩ L′→*N′) =
  anti-reduction-≼-R-one (anti-reduction-≼-R ℰMN′ L′→*N′) M′→L′

anti-reduction-≽-L : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≽ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i
  → (M→N : M —↠ N)
  → #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≽-L {c = c} {M} {.M} {N′} {i} ℰNM′ (.M END) = ℰNM′
anti-reduction-≽-L {c = c} {M} {M′} {N′} {i} ℰNM′ (.M —→⟨ M→L ⟩ L→*N) =
  anti-reduction-≽-L-one (anti-reduction-≽-L ℰNM′ L→*N) M→L
\end{code}

\begin{code}
LRₜ-blame-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{k}
   → #(dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′) k
LRₜ-blame-step {A}{A′}{A⊑A′}{dir} {M} {zero} = tz (dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′)
LRₜ-blame-step {A}{A′}{A⊑A′}{≼} {M} {suc k} = inj₂ (inj₁ (blame END))
LRₜ-blame-step {A}{A′}{A⊑A′}{≽} {M} {suc k} = inj₂ (inj₁ isBlame)

LRₜ-blame : ∀{𝒫}{A}{A′}{A⊑A′ : A ⊑ A′}{M}{dir}
   → 𝒫 ⊢ᵒ dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′
LRₜ-blame {𝒫}{A}{A′}{A⊑A′}{M}{dir} = ⊢ᵒ-intro λ n x → LRₜ-blame-step{dir = dir}
\end{code}

\begin{code}
LRᵥ-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}{dir}
   → (dir ∣ (ƛ N) ⊑ᴸᴿᵥ (ƛ N′) ⦂ fun⊑ A⊑A′ B⊑B′)
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ A⊑A′))
                →ᵒ (▷ᵒ (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′))))
LRᵥ-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′}{dir} =
   let X = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , dir , ƛ N , ƛ N′) in
   (dir ∣ (ƛ N) ⊑ᴸᴿᵥ (ƛ N′) ⦂ fun⊑ A⊑A′ B⊑B′)  ⩦⟨ ≡ᵒ-refl refl ⟩
   LRₜ⊎LRᵥ X                                       ⩦⟨ fixpointᵒ pre-LRₜ⊎LRᵥ X ⟩
   # (pre-LRₜ⊎LRᵥ X) (LRₜ⊎LRᵥ , ttᵖ)                          ⩦⟨ ≡ᵒ-refl refl ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ A⊑A′))
                   →ᵒ (▷ᵒ (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′)))) ∎
\end{code}


\begin{code}
LRᵥ-base-elim-step : ∀{ι}{ι′}{c : $ₜ ι ⊑ $ₜ ι′}{V}{V′}{dir}{k}
  → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) (suc k)
  → ∃[ c ] ι ≡ ι′ × V ≡ $ c × V′ ≡ $ c
LRᵥ-base-elim-step {ι} {.ι} {base⊑} {$ c} {$ c′} {dir} {k} refl =
  c , refl , refl , refl

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

LRᵥ-dyn-any-elim-≼ : ∀{V}{V′}{k}{H}{A′}{c : gnd⇒ty H ⊑ A′}
   → #(≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) (suc k)
   → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
             × #(≼ ∣ V₁ ⊑ᴸᴿᵥ V′ ⦂ c) k
LRᵥ-dyn-any-elim-≼ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VGV′
... | yes refl
    with 𝒱VGV′
... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′

LRᵥ-dyn-any-elim-≽ : ∀{V}{V′}{k}{H}{A′}{c : gnd⇒ty H ⊑ A′}
   → #(≽ ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) (suc k)
   → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
             × #(≽ ∣ V₁ ⊑ᴸᴿᵥ V′ ⦂ c) (suc k)
LRᵥ-dyn-any-elim-≽ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VGV′
... | yes refl
    with 𝒱VGV′
... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′
\end{code}

\begin{code}
LRᵥ-inject-R-intro-≽ : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}
   → #(≽ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≽ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
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

LRᵥ-inject-R-intro-≼ : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}
   → #(≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≼ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
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

LRᵥ-inject-R-intro : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}{dir}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(dir ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
LRᵥ-inject-R-intro {G} {c} {V} {V′} {k} {≼} 𝒱VV′ =
   LRᵥ-inject-R-intro-≼{G} {c} {V} {V′} {k} 𝒱VV′ 
LRᵥ-inject-R-intro {G} {c} {V} {V′} {k} {≽} 𝒱VV′ =
   LRᵥ-inject-R-intro-≽{G} {c} {V} {V′} {k} 𝒱VV′

LRᵥ-inject-L-intro-≼ : ∀{G}{A′}{c : gnd⇒ty G ⊑ A′}{V}{V′}{k}
   → Value V
   → Value V′
   → #(≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≼ ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) (suc k)
LRᵥ-inject-L-intro-≼ {G} {A′} {c} {V} {V′} {k} v v′ 𝒱VV′k
    with G ≡ᵍ G
... | no neq = ⊥-elim (neq refl)
... | yes refl =
    v , v′ , 𝒱VV′k

LRᵥ-inject-L-intro-≽ : ∀{G}{A′}{c : gnd⇒ty G ⊑ A′}{V}{V′}{k}
   → #(≽ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≽ ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) k
LRᵥ-inject-L-intro-≽ {G}{A′}{c}{V}{V′}{zero} 𝒱VV′k =
    tz (≽ ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c)
LRᵥ-inject-L-intro-≽ {G} {A′} {c} {V} {V′} {suc k} 𝒱VV′sk
    with G ≡ᵍ G
... | no neq = ⊥-elim (neq refl)
... | yes refl =
      let (v , v′) = LRᵥ⇒Value c V V′ 𝒱VV′sk in
      v , v′ , 𝒱VV′sk

LRᵥ-inject-L-intro : ∀{G}{A′}{c : gnd⇒ty G ⊑ A′}{V}{V′}{dir}{k}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(dir ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) k
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
bind-premise : Dir → PEFrame → PEFrame → Term → Term → ℕ
   → ∀ {B}{B′}(c : B ⊑ B′) → ∀ {A}{A′} (d : A ⊑ A′) → Set
bind-premise dir F F′ M M′ i c d =
    (∀ j V V′ → j ≤ i → M —↠ V → Value V → M′ —↠ V′ → Value V′
     → # (dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
     → # (dir ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)


LRᵥ→LRₜ-down-one-≼ : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}
                      {F}{F′}{i}{M}{N}{M′}
   → M —→ N
   → (bind-premise ≼ F F′ M M′ (suc i) c d)
   → (bind-premise ≼ F F′ N M′ i c d)
LRᵥ→LRₜ-down-one-≼ {B}{B′}{c}{A}{A′}{d}{F}{F′}{i}{M}{N}{M′} M→N LRᵥ→LRₜsi
   j V V′ j≤i M→V v M′→V′ v′ 𝒱j =
   LRᵥ→LRₜsi j V V′ (≤-trans j≤i (n≤1+n i)) (M —→⟨ M→N ⟩ M→V) v M′→V′ v′ 𝒱j

LRᵥ→LRₜ-down-one-≽ : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}
                       {F}{F′}{i}{M}{M′}{N′}
   → M′ —→ N′
   → (bind-premise ≽ F F′ M M′ (suc i) c d)
   → (bind-premise ≽ F F′ M N′ i c d)
LRᵥ→LRₜ-down-one-≽ {B}{B′}{c}{A}{A′}{d}{F}{F′}{i}{M}{N}{M′} M′→N′ LRᵥ→LRₜsi
   j V V′ j≤i M→V v M′→V′ v′ 𝒱j =
   LRᵥ→LRₜsi j V V′ (≤-trans j≤i (n≤1+n i)) M→V v (N —→⟨ M′→N′ ⟩ M′→V′) v′ 𝒱j


LRₜ-bind : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}
                 {F}{F′}{M}{M′}{i}{dir}
   → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ d) i
   → (∀ j V V′ → j ≤ i → M —↠ V → Value V → M′ —↠ V′ → Value V′
         → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
         → #(dir ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
   → #(dir ∣ (F ⦉ M ⦊) ⊑ᴸᴿₜ (F′ ⦉ M′ ⦊) ⦂ c) i
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


\begin{code}
compatible-blame : ∀{Γ}{A}{M}
   → map proj₁ Γ ⊢ M ⦂ A
     -------------------------------
   → Γ ⊨ M ⊑ᴸᴿ blame ⦂ (A , A , Refl⊑)
compatible-blame{Γ}{A}{M} ⊢M = (λ γ γ′ → LRₜ-blame) , (λ γ γ′ → LRₜ-blame)

lookup-⊑ᴸᴿ : ∀{dir} (Γ : List Prec) → (γ γ′ : Subst)
  → ∀ {A}{A′}{A⊑A′}{x} → Γ ∋ x ⦂ (A , A′ , A⊑A′)
  → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ γ x ⊑ᴸᴿᵥ γ′ x ⦂ A⊑A′
lookup-⊑ᴸᴿ {dir} (.(A , A′ , A⊑A′) ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
lookup-⊑ᴸᴿ {dir} (B ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {suc x} ∋x =
   Sᵒ (lookup-⊑ᴸᴿ Γ (λ z → γ (suc z)) (λ z → γ′ (suc z)) ∋x)

compatibility-var : ∀ {Γ A A′ A⊑A′ x}
  → Γ ∋ x ⦂ (A , A′ , A⊑A′)
    -------------------------------
  → Γ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
compatibility-var {Γ}{A}{A′}{A⊑A′}{x} ∋x = LT , GT
  where
  LT : Γ ∣ ≼ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
  LT γ γ′ rewrite sub-var γ x | sub-var γ′ x = LRᵥ⇒LRₜ (lookup-⊑ᴸᴿ Γ γ γ′ ∋x)

  GT : Γ ∣ ≽ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
  GT γ γ′ rewrite sub-var γ x | sub-var γ′ x = LRᵥ⇒LRₜ (lookup-⊑ᴸᴿ Γ γ γ′ ∋x)
\end{code}

\begin{code}
compatible-lambda : ∀{Γ : List Prec}{A}{B}{C}{D}{N N′ : Term}
     {c : A ⊑ C}{d : B ⊑ D}
   → ((A , C , c) ∷ Γ) ⊨ N ⊑ᴸᴿ N′ ⦂ (B , D , d)
     ------------------------------------------------
   → Γ ⊨ (ƛ N) ⊑ᴸᴿ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ =
  (λ γ γ′ → ⊢ℰλNλN′) , (λ γ γ′ → ⊢ℰλNλN′)
 where
 ⊢ℰλNλN′ : ∀{dir}{γ}{γ′} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
            ⊢ᵒ (dir ∣ (⟪ γ ⟫ (ƛ N)) ⊑ᴸᴿₜ (⟪ γ′ ⟫ (ƛ N′)) ⦂ fun⊑ c d)
 ⊢ℰλNλN′ {dir}{γ}{γ′} =
     LRᵥ⇒LRₜ (substᵒ (≡ᵒ-sym LRᵥ-fun)
          (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI {P = ▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c)}
            (appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI ((proj dir N N′ ⊨N⊑N′)
                                            (W • γ) (W′ • γ′))))))
                  Zᵒ)))
\end{code}

\begin{code}
compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ᴸᴿ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (A , A′ , c)
     ----------------------------------
   → Γ ⊨ L · M ⊑ᴸᴿ L′ · M′ ⦂ (B , B′ , d)
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

\begin{code}
compatible-inj-L : ∀{Γ}{G A′}{c : gnd⇒ty G ⊑ A′}{M M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (gnd⇒ty G , A′ , c)
     ---------------------------------------------
   → Γ ⊨ M ⟨ G !⟩ ⊑ᴸᴿ M′ ⦂ (★ , A′ , unk⊑{G}{A′} c)
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

\begin{code}
compatible-inj-R : ∀{Γ}{G}{c : ★ ⊑ gnd⇒ty G }{M M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , gnd⇒ty G , c)
   → Γ ⊨ M ⊑ᴸᴿ M′ ⟨ G !⟩ ⦂ (★ , ★ , unk⊑unk)
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

\begin{code}
compatible-proj-L : ∀{Γ}{H}{A′}{c : gnd⇒ty H ⊑ A′}{M}{M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , A′ ,  unk⊑ c)
   → Γ ⊨ M ⟨ H ?⟩ ⊑ᴸᴿ M′ ⦂ (gnd⇒ty H , A′ , c)
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
       let ℰV₁V′j = LRᵥ⇒LRₜ-step{gnd⇒ty H}{A′}{c}{V₁}{V′}{≼}{j} 𝒱V₁V′j in
       anti-reduction-≼-L-one ℰV₁V′j V₁HH→V₁
   Goal {suc j} {V} {V′}{≽} 𝒱VV′sj
       with LRᵥ-dyn-any-elim-≽{V}{V′}{j}{H}{A′}{c} 𝒱VV′sj
   ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′sj =
       let V₁HH→V₁ = collapse{H}{V = V₁} v₁ refl in
       inj₂ (inj₂ (v′ , V₁ , unit V₁HH→V₁ , v₁ , 𝒱V₁V′sj))
\end{code}

\begin{code}
compatible-proj-R : ∀{Γ}{H}{c : ★ ⊑ gnd⇒ty H}{M}{M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , ★ , unk⊑unk)
   → Γ ⊨ M ⊑ᴸᴿ M′ ⟨ H ?⟩ ⦂ (★ , gnd⇒ty H , c)
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
     ... | ≽ = anti-reduction-≽-R-one (LRₜ-blame-step{★}{gnd⇒ty H}{unk⊑ d}{≽})
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
         let 𝒱VGV′j = LRᵥ-inject-L-intro-≽ {G}{gnd⇒ty G}{d} 𝒱V₁V′₁j in
         let ℰVGV′j = LRᵥ⇒LRₜ-step{V = V₁ ⟨ G !⟩}{V′₁}{≽} 𝒱VGV′j in
         anti-reduction-≽-R-one ℰVGV′j (collapse v′ refl)
\end{code}

\begin{code}
fundamental : ∀ {Γ}{A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
  → Γ ⊩ M ⊑ M′ ⦂ A⊑A′
    ----------------------------
  → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (A , A′ , A⊑A′)
fundamental {Γ} {A} {A′} {A⊑A′} .(` _) .(` _) (⊑-var ∋x) =
   compatibility-var ∋x
fundamental {Γ} {_} {_} {base⊑} ($ c) ($ c) ⊑-lit =
   compatible-literal
fundamental {Γ} {A} {A′} {A⊑A′} (L · M) (L′ · M′) (⊑-app ⊢L⊑L′ ⊢M⊑M′) =
    compatible-app{L = L}{L′}{M}{M′} (fundamental L L′ ⊢L⊑L′)
                                     (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(fun⊑ _ _)} (ƛ N)(ƛ N′) (⊑-lam ⊢N⊑N′) =
    compatible-lambda{N = N}{N′} (fundamental N N′ ⊢N⊑N′)
fundamental {Γ} {★} {A′} {unk⊑ c} (M ⟨ G !⟩) M′ (⊑-inj-L ⊢M⊑M′) =
    compatible-inj-L{G =  G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {★} {★} {.unk⊑unk} M (M′ ⟨ G !⟩) (⊑-inj-R ⊢M⊑M′) =
    compatible-inj-R{Γ}{G = G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {_} {A′} {A⊑A′} (M ⟨ H ?⟩) M′ (⊑-proj-L ⊢M⊑M′) =
    compatible-proj-L{Γ}{H}{A′}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.(gnd⇒ty _)} {A⊑A′} M (M′ ⟨ H′ ?⟩) (⊑-proj-R ⊢M⊑M′) =
    compatible-proj-R{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.A} {.Refl⊑} M .blame (⊑-blame ⊢M∶A) =
   compatible-blame ⊢M∶A
\end{code}

\begin{code}
_⊨_⊑_for_ : Dir → Term → Term → ℕ → Set

≼ ⊨ M ⊑ M′ for k = (M ⇓ × M′ ⇓)
                    ⊎ (M′ —↠ blame)
                    ⊎ (∃[ N ] Σ[ r ∈ M —↠ N ] len r ≡ k)
                    
≽ ⊨ M ⊑ M′ for k = (M ⇓ × M′ ⇓)
                    ⊎ (M′ —↠ blame)
                    ⊎ (∃[ N′ ] Σ[ r ∈ M′ —↠ N′ ] len r ≡ k)
                    
⊨_⊑_for_ : Term → Term → ℕ → Set
⊨ M ⊑ M′ for k = (≼ ⊨ M ⊑ M′ for k) × (≽ ⊨ M ⊑ M′ for k)

LR⇒sem-approx : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}{k}{dir}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k)
  → dir ⊨ M ⊑ M′ for k
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
      inj₁ ((V , (M —→⟨ M→N ⟩ M→V) , v) , (V′ , M′→V′ , v′))
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (L , N→L , eq)) =
      inj₂ (inj₂ (L , (M —→⟨ M→N ⟩ N→L) , cong suc eq))
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
      inj₁ ((V , M→V , v) , V′ , (M′ —→⟨ M′→N′ ⟩ N′→V′) , v′)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′ —→⟨ M′→N′ ⟩ N′→blame))
... | inj₂ (inj₂ (L′ , N′→L′ , eq)) =
      inj₂ (inj₂ (L′ , (M′ —→⟨ M′→N′ ⟩ N′→L′) , cong suc eq))

sem-approx⇒GG : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}
   → (∀ k → ⊨ M ⊑ M′ for k)
   → (M′ ⇓ → M ⇓)
   × (M′ ⇑ → M ⇑)
   × (M ⇓ → M′ ⇓ ⊎ M′ —↠ blame)
   × (M ⇑ → M′ ⇑⊎blame)
   × (M —↠ blame → M′ —↠ blame)
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

  to-value-left : M ⇓ → M′ ⇓ ⊎ M′ —↠ blame
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

  blame-blame : (M —↠ blame → M′ —↠ blame)
  blame-blame M→blame
      with proj₁ (⊨M⊑M′ (suc (len M→blame)))
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
        ⊥-elim (cant-reduce-value-and-blame v M→V M→blame)
  ... | inj₂ (inj₁ M′→blame) = M′→blame
  ... | inj₂ (inj₂ (N , M→N , eq)) =
        ⊥-elim (step-blame-plus-one M→N M→blame eq)

LR⇒GG : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}
   → [] ⊢ᵒ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′
   → (M′ ⇓ → M ⇓)
   × (M′ ⇑ → M ⇑)
   × (M ⇓ → M′ ⇓ ⊎ M′ —↠ blame)
   × (M ⇑ → M′ ⇑⊎blame)
   × (M —↠ blame → M′ —↠ blame)
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

\begin{code}
gradual-guarantee : ∀ {A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
   → [] ⊩ M ⊑ M′ ⦂ A⊑A′
    ---------------------------
   → (M′ ⇓ → M ⇓)
   × (M′ ⇑ → M ⇑)
   × (M ⇓ → M′ ⇓ ⊎ M′ —↠ blame)
   × (M ⇑ → M′ ⇑⊎blame)
   × (M —↠ blame → M′ —↠ blame)
gradual-guarantee {A}{A′}{A⊑A′} M M′ M⊑M′ =
  let (⊨≼M⊑ᴸᴿM′ , ⊨≽M⊑ᴸᴿM′) = fundamental M M′ M⊑M′ in
  LR⇒GG (⊨≼M⊑ᴸᴿM′ id id ,ᵒ ⊨≽M⊑ᴸᴿM′ id id)
\end{code}
