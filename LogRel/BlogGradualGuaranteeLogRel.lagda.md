```
{-# OPTIONS --rewriting #-}
module LogRel.BlogGradualGuaranteeLogRel where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)

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

One might wonder if the gradual guarantee could be simply proved by
induction on the derivation of its premise `[] ⊩ M ⊑ M′ ⦂ A⊑A′`.  Such
a proof attempt runs into trouble in the case for function
application, where one needs to have more information about how the
bodies of related lambda abstractions evaluate when given related
arguments, but don't have it. The main idea of a logical relation is
to add that extra information, effectively strengthening the theorem
statement to get the induction to go through.

However, before diving into the logical relation, we have one more
items to cover regarding the gradual guarantee.

# Semantic Approximation

We separate the gradual guarantee into two properties, one that
observes the less precise term `M` for `k` steps of reduction and the
other that observes the more precise term `M′` for `k` steps of
reduction. After those `k` steps, the term being observed may have
reduced to a value or an error, or it might still be reducing.  If it
reduced to a value, then the relation requires the other term to also
reduce to a value, except of course that `M′` may error.  We define
these two properties with one relation, written `dir ⊨ M ⊑ M′ for k`
and called semantic approximation, that is parameterized over a
direction `dir`. The direction `≼` observes the less precise term `M`
and the `≽` direction observes the more precise term `M′`.

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
approximation implies the gradual guarantee.

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

The logical relation acts as a bridge between term precision and
semantic approximzation. As alluded to above, it packs away extra
information when relating two lambda abstractions. However, while this
idea is straightforward, especially in the context of the simply-typed
lambda calculus (STLC), the definition of logical relation for the
cast calculus is rather more involved. We start by reviewing how one
would define a logical relation for the STLC, then introduce the
complications needed for the cast calculus.

For the STLC, the logical relation would consist of two relations, one
for terms and another for values, and it would be indexed by their
type `A`.

    M ≼ᴸᴿₜ M′ ⦂ A
    V ≼ᴸᴿᵥ V′ ⦂ A

The relation for values would be defined as an Agda function by
recursion on the type `A`.  At base type we relate literals if they
are identical.

    ($ c) ≼ᴸᴿᵥ ($ c′) ⦂ ι   =   c ≡ c′

At function type, two lambda abstractions are related if substituting
related arguments into their bodies yields related terms.

    (ƛ N) ≼ᴸᴿᵥ (ƛ N′) ⦂ A ⇒ B = 
        ∀ W W′ → W ≼ᴸᴿᵥ W′ ⦂ A → N [ W ] ≼ᴸᴿₜ N′ [ W′ ] ⦂ B

The recurse uses of `≼ᴸᴿᵥ` and `≼ᴸᴿₜ` at type `A` and `B` in the above
are Okay because those types are part of the function type `A ⇒ B`.

The definition of the relation on terms would have the following form.

    M ≼ᴸᴿₜ M′ ⦂ A =  M —↠ V → ∃[ V′ ] M′ —↠ V′ × V ≼ᴸᴿᵥ V′ ⦂ A

The first challenge regarding the Cast Calculus is handling the
unknown type `★` and its value form, the injection `V ⟨ G !⟩` that
casts value `V` from the ground type `G` to `★`. One might try to
define the case for injection as follows

    V ⟨ G !⟩ ≼ᴸᴿᵥ V′ ⟨ H !⟩ ⦂ ★
        with G ≡ H
    ... | yes refl = V ≼ᴸᴿᵥ V′ ⦂ G
    ... | no neq = ⊥

but then realize that Agda rejects the recursion on type `G` as that
type is not a subpart of `★`.

At this point one might think to try defining the logical relation
using a `data` declaration in Agda, but then one gets stuck in the
case for function type because the recursion `W ≼ᴸᴿᵥ W′ ⦂ A` appears
to the left of an implication.

This is where step indexing comes into play. We add an extra parameter
to the relation, a natural number, and decrement that number in the
recursive calls. Here's a first attempt. We'll define the following two
functions, parameterized on the step index `k` and the direction `dir`
(just like in the semantic approximation above.)

    dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ for k
    dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ for k


When the step-index is at zero, we relate all values.

    dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ for zero = ⊤

For `suc k`, we proceed by cases on precision `A ⊑ A′`.  In the case
for `unk⊑unk`, where we need to relate injections to `★` on both
sides, the recursion uses step index `k` to relate the underlying
values.

    dir ∣ V ⟨ G !⟩ ⊑ᴸᴿᵥ V′ ⟨ H !⟩ ⦂ unk⊑unk for (suc k)
        with G ≡ᵍ H
    ... | yes refl = Value V × Value V′ × (dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ Refl⊑ for k)
    ... | no neq = ⊥

In the case for relating function types, we could try the following

    dir ∣ ƛ N ⊑ᴸᴿᵥ ƛ N′ ⦂ (fun⊑ A⊑A′ B⊑B′) for (suc k) =
      ∀ W W′ → (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ A⊑A′ for k)
             → (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′ for k) 

which again is Okay regarding termination because the recursion is at
the small step-index `k`. Unfortunately, we run into another problem.
Our proofs will depend on the logical relation being downward closed.
In general, a step-indexed property `S` is downward closed if,
whenever it is true at a given step index `n`, it remains true at
smaller step indices.

    downClosed : (ℕ → Set) → Set
    downClosed S = ∀ n → S n → ∀ k → k ≤ n → S k

The above definition of the relation for function types is not
downward closed. The fix is to allow the recursion at any
number `j` that is less-than-or-equal to `k`.

    dir ∣ ƛ N ⊑ᴸᴿᵥ ƛ N′ ⦂ (fun⊑ A⊑A′ B⊑B′) for (suc k) =
      ∀ W W′ j → j ≤ k → (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ A⊑A′ for j)
             → (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′ for j) 

But now Agda rejects this definition because it is not structurally
recursive, i.e., j is not a subpart of `suc k`. One could instead
define the relation by strong recursion and then proceed to prove that
it is downward closed. I've tried that approach and it works. However,
using strong recursion in Agda is somewhat annoying, as is the proof
of downward closedness. We instead use the `StepIndexedLogic` library
to define the logical relation, which enables the definition of
recursive predicates and proves downward closedness for us.  However,
there is some cost to using the `StepIndexedLogic` library, as
there is some overhead to using the library.

```
open import StepIndexedLogic
```

Recall that the `StepIndexedLogic` library provides an operator `μᵒ`
that takes a non-recursive predicate (with an extra parameter) and
turns it into a recursive predicate where the extra parameter is bound
to itself. However, the library does not directly support mutually
recursive predicates, so we must merge the two into a single predicate
whose input is a disjoint union (aka. sum type), and the dispatch back
out to separate predicates, which we name `LRᵥ` (for values) and `LRₜ`
(for terms). The predicates are indexed not only by the two terms and
the direction (`≼` or `≽`), but also by the precision relation between
the types of the two terms.

```
LR-type : Set
LR-type = (Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)

LR-ctx : Context
LR-ctx = LR-type ∷ []

LRᵥ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)
LRₜ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)
```


```
_∣_ˢ⊑ᴸᴿₜ_⦂_ : Dir → Term → Term → ∀{A}{A′} (A⊑A′ : A ⊑ A′)
   → Setˢ LR-ctx (cons Now ∅)
dir ∣ M ˢ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = (inj₂ ((_ , _ , A⊑A′) , dir , M , M′)) ∈ zeroˢ

_∣_ˢ⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A}{A′} (A⊑A′ : A ⊑ A′)
   → Setˢ LR-ctx (cons Now ∅)
dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ = (inj₁ ((_ , _ , A⊑A′) , dir , V , V′)) ∈ zeroˢ
```

```
instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }
```

The definition of the logical relation for terms is a reorganized
version of semantic approximation that only talks about one step at a
time of the term that is being observed. Let us consider the `≼`
direction, that observes the less-precise term `M`.  The first clause
says that `M` takes a step to `N` and that `N` is related to `M′` at
one tick later in time. The third clause says that `M` is already a
value, and requires `M′` to reduce to a value that is related to
`M`. Finally, the second clause allows `M′` to produce an error.

```
LRₜ (A , A′ , c) ≼ M M′ =
   (∃ˢ[ N ] (M —→ N)ˢ ×ˢ ▷ˢ (≼ ∣ N ˢ⊑ᴸᴿₜ M′ ⦂ c))
   ⊎ˢ (M′ —↠ blame)ˢ
   ⊎ˢ ((Value M)ˢ ×ˢ (∃ˢ[ V′ ] (M′ —↠ V′)ˢ ×ˢ (Value V′)ˢ
                       ×ˢ (LRᵥ (_ , _ , c) ≼ M V′)))
```

The other direction, `≽`, is defined in a symmetric way, observing the
reduction of the more-precise `M′` instead of `M`.

```
LRₜ (A , A′ , c) ≽ M M′ =
   (∃ˢ[ N′ ] (M′ —→ N′)ˢ ×ˢ ▷ˢ (≽ ∣ M ˢ⊑ᴸᴿₜ N′ ⦂ c))
   ⊎ˢ (Blame M′)ˢ
   ⊎ˢ ((Value M′)ˢ ×ˢ (∃ˢ[ V ] (M —↠ V)ˢ ×ˢ (Value V)ˢ
                                ×ˢ (LRᵥ (_ , _ , c) ≽ V M′)))
```

Next we proceed to the definition of the logical relation for values,
the predicate `LRᵥ`. In the case of precision for base types `base⊑`,
we only relate identical constants.

```
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir ($ c) ($ c′) = (c ≡ c′) ˢ
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir V V′ = ⊥ ˢ
```

In the case for related function types, two lambda abstractions are
related if, for any two arguments that are related later, substituting
the arguments into the bodies produces terms that are related later.

```
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir (ƛ N)(ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (dir ∣ W ˢ⊑ᴸᴿᵥ W′ ⦂ A⊑A′)
                  →ˢ ▷ˢ (dir ∣ (N [ W ]) ˢ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′) 
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir V V′ = ⊥ ˢ
```

Notice how in the above definition, we no longer need to quantify over
the extra `j` where `j ≤ k`. The implication operator `→ˢ` of the
`StepIndexedLogic` instead takes care of that complication; ensuring
that our logical relation is downward closed.

In the case for relating

```
LRᵥ (.★ , .★ , unk⊑unk) dir (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ Refl⊑{gnd⇒ty G}))
... | no neq = ⊥ ˢ
LRᵥ (.★ , .★ , unk⊑unk) dir V V′ = ⊥ ˢ
```

```
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≼ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ ▷ˢ (≼ ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ d)
... | no neq = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≽ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (LRᵥ (gnd⇒ty G , A′ , d) ≽ V V′)
... | no neq = ⊥ ˢ
LRᵥ (★ , .A′ , unk⊑{H}{A′} d) dir V V′ = ⊥ ˢ
```


```
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
```

```
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
```

```
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
  EQ : ∀{dir} → # (pre-LRₜ⊎LRᵥ (X₂ dir)) (LRₜ⊎LRᵥ , ttᵖ) ≡ᵒ LRₜ-def A⊑A′ dir M M′
  EQ {≼} = cong-⊎ᵒ (≡ᵒ-refl refl)
           (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) 
             (cong-∃ λ V′ → cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
              ((≡ᵒ-sym (fixpointᵒ pre-LRₜ⊎LRᵥ (inj₁ (c , ≼ , M , V′)))))))))
  EQ {≽} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ λ V → cong-×ᵒ (≡ᵒ-refl refl)
              (cong-×ᵒ (≡ᵒ-refl refl)
               (≡ᵒ-sym (fixpointᵒ pre-LRₜ⊎LRᵥ (inj₁ (c , ≽ , V , M′))))))))

LRₜ-suc : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}{k}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k) ⇔ #(LRₜ-def A⊑A′ dir M M′) (suc k)
LRₜ-suc {A}{A′}{A⊑A′}{dir}{M}{M′}{k} =
   ≡ᵒ⇒⇔{k = suc k} (LRₜ-stmt{A}{A′}{A⊑A′}{dir}{M}{M′})
```


```
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
```
