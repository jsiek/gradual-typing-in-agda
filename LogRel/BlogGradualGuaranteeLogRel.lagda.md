```
{-# OPTIONS --rewriting #-}
module LogRel.BlogGradualGuaranteeLogRel where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)

open import Var
open import InjProj.CastCalculus
open import InjProj.CastDeterministic
--open import InjProj.Reduction

```

One of the defining characteristics of a gradually typed language is
captured by the [gradual
guarantee](https://drops.dagstuhl.de/opus/volltexte/2015/5031/) ,
which governs how the behavior of a program can change when the
programmer changes some of the type annotations in the program to be
more or less precise. It says that changing a program to be more
precise, it will behave the same except that it may error more often.
Change in the other direction, to be less precise, yield exactly the
same behavior.

In this blog post I prove in Agda the gradual guarantee for the
gradually typed lambda calculus using the logical relations proof
technique. In the past I've proved the gradual guarantee using a
simulation argument, but I was curious to see whether the proof would
be easier/harder using logical relations.  The approach I use here is
a synthesis of techniques from Dreyer, Ahmed, and Birkedal (LMCS 2011)
regarding step-indexing using a modal logic and Max New (Ph.D. thesis
2020) regarding logical relations for gradual typing.

# Precision and the Gradual Guarantee

To talk about the gradual guarantee, we first define when one type is
less precise than another one. The following definition says that the
unknown type `★` is less precise than any other type.

```
infixr 6 _⊑_
data _⊑_ : Type → Type → Set where

  unk⊑unk : ★ ⊑ ★
  
  unk⊑ : ∀{G}{B}
     → gnd⇒ty G ⊑ B
       -------------
     → ★ ⊑ B
  
  base⊑ : ∀{ι}
        ----------
      → $ₜ ι ⊑ $ₜ ι

  fun⊑ : ∀{A B C D}
     → A ⊑ C  →  B ⊑ D
       ---------------
     → A ⇒ B ⊑ C ⇒ D
```

The first two rules for precision are usually presented as a single rule:

    unk⊑any : ∀{B} → ★ ⊑ B
    
Instead we have separated out the case for when both types are `★`
from the case when only the less-precise type is `★`.  Also, for the
rule `unk⊑`, instead of writing `B ≢ ★` we have written `gnd⇒ty G ⊑
B`, which turns out to be important later when we define the logical
relation and use recursion on the precision relation.

Of course, the precision relation is reflexive.
```
Refl⊑ : ∀{A} → A ⊑ A
Refl⊑ {★} = unk⊑unk
Refl⊑ {$ₜ ι} = base⊑
Refl⊑ {A ⇒ B} = fun⊑ Refl⊑ Refl⊑
```

Next we define a precision relation on terms. I'm going to skip the
normal steps of first defining the precision relation for the surface
language and proving that compiling from the surface language to a
cast calculus preserves precision. That is relatively easy, so I'll
jump to defining precision on terms of the cast calculus.

```
infix 3 _⊩_⊑_⦂_

Prec : Set
Prec = (∃[ A ] ∃[ B ] A ⊑ B)

data _⊩_⊑_⦂_ : List Prec → Term → Term → ∀{A B : Type} → A ⊑ B → Set 

data _⊩_⊑_⦂_ where

  ⊑-var : ∀ {Γ x A⊑B}
     → Γ ∋ x ⦂ A⊑B
       -------------------------------------
     → Γ ⊩ (` x) ⊑ (` x) ⦂ proj₂ (proj₂ A⊑B)

  ⊑-lit : ∀ {Γ c}
       -----------------------------------
     → Γ ⊩ ($ c) ⊑ ($ c) ⦂ base⊑{typeof c}

  ⊑-app : ∀{Γ L M L′ M′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → Γ ⊩ L ⊑ L′ ⦂ fun⊑ c d
     → Γ ⊩ M ⊑ M′ ⦂ c
       -----------------------
     → Γ ⊩ L · M ⊑ L′ · M′ ⦂ d

  ⊑-lam : ∀{Γ N N′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → (A , C , c) ∷ Γ ⊩ N ⊑ N′ ⦂ d
       ----------------------------
     → Γ ⊩ ƛ N ⊑ ƛ N′ ⦂ fun⊑ c d

  ⊑-inj-L : ∀{Γ M M′}{G B}{c : (gnd⇒ty G) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ c
       --------------------------------
     → Γ ⊩ M ⟨ G !⟩ ⊑ M′ ⦂ unk⊑{G}{B} c

  ⊑-inj-R : ∀{Γ M M′}{G}{c : ★ ⊑ (gnd⇒ty G)}
     → Γ ⊩ M ⊑ M′ ⦂ c
       ---------------------------
     → Γ ⊩ M ⊑ M′ ⟨ G !⟩ ⦂ unk⊑unk

  ⊑-proj-L : ∀{Γ M M′ H B}{c : (gnd⇒ty H) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑ c
       ---------------------
     → Γ ⊩ M ⟨ H ?⟩ ⊑ M′ ⦂ c

  ⊑-proj-R : ∀{Γ M M′ H}{c : ★ ⊑ (gnd⇒ty H)}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑unk
       ---------------------
     → Γ ⊩ M ⊑ M′ ⟨ H ?⟩  ⦂ c

  ⊑-blame : ∀{Γ M A}
     → map proj₁ Γ ⊢ M ⦂ A
       ------------------------
     → Γ ⊩ M ⊑ blame ⦂ Refl⊑{A}
```

To write down the gradual guarantee, we also need some notation for
expressing whether a program halts with a value, diverges, or
encounters an error. So we write `⇓` for halting with a result value,
`⇑` for diverging, and `⇑⊎blame` for diverging or producing an error.

    _⇓ : Term → Set
    M ⇓ = ∃[ V ] (M —↠ V) × Value V

    _⇑ : Term → Set
    M ⇑ = ∀ k → ∃[ N ] Σ[ r ∈ M —↠ N ] k ≡ len r

    _⇑⊎blame : Term → Set
    M ⇑⊎blame = ∀ k → ∃[ N ] Σ[ r ∈ M —↠ N ] ((k ≡ len r) ⊎ (N ≡ blame))

We can now state the gradual guarnatee.  Suppose program `M` is less
or equally precise as program `M′`.  Then `M` and `M′` should behave
the same except that `M′` results in an error more often.  More
specifically, if `M′` results in a value or diverges, so does `M`.  On
the other hand, if `M` results a value, then `M′` results in a value
or errors. If `M` diverges, then `M′` diverges or errors.
If `M` errors, then so does `M′`.

    gradual-guarantee : ∀ {A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
       → [] ⊩ M ⊑ M′ ⦂ A⊑A′
        -----------------------------------
       → (M′ ⇓ → M ⇓)
       × (M′ ⇑ → M ⇑)
       × (M ⇓ → M′ ⇓ ⊎ M′ —↠ blame)
       × (M ⇑ → M′ ⇑⊎blame)
       × (M —↠ blame → M′ —↠ blame)

# Semantic Approximation

We separate the gradual guarantee into two properties, one that
observes the less precise term `M` for `k` steps of reduction and the
other that observes the more precise term `M′` for `k` steps of
reduction. After those `k` steps, the term being observed may have
reduced to a value or an error, or it might still be reducing.  If it
reduced to a value, then the relation requires the other term to also
reduce to a value, except of course that `M′` may error.  We define
these two properties with one relation, written `dir ⊨ M ⊑ M′ for k`,
that is parameterized over a direction `dir`. The direction `≼`
observes the less precise term `M` and the `≽` direction observes the
more precise term `M′`.

```
data Dir : Set where
  ≼ : Dir
  ≽ : Dir

_⊨_⊑_for_ : Dir → Term → Term → ℕ → Set

≼ ⊨ M ⊑ M′ for k = (M ⇓ × M′ ⇓)
                    ⊎ (M′ —↠ blame)
                    ⊎ (∃[ N ] Σ[ r ∈ M —↠ N ] len r ≡ k)
                    
≽ ⊨ M ⊑ M′ for k = (M ⇓ × M′ ⇓)
                    ⊎ (M′ —↠ blame)
                    ⊎ (∃[ N′ ] Σ[ r ∈ M′ —↠ N′ ] len r ≡ k)
```

We write `⊨ M ⊑ M′ for k` for the conjunction of semantic
approximation in both directions.

```
⊨_⊑_for_ : Term → Term → ℕ → Set
⊨ M ⊑ M′ for k = (≼ ⊨ M ⊑ M′ for k) × (≽ ⊨ M ⊑ M′ for k)
```

The following verbose but easy proof confirms that semantic
approximation implies the Gradual Guarantee.

```
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
```

# Definition of the Logical Relation

