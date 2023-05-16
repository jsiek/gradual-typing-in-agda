```
{-# OPTIONS --rewriting #-}
module LogRel.BlogGradualGuaranteeLogRel where

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

If `c` is a derivation of `★ ⊑ gnd⇒ty G`, then it must be an instance
of the `unk⊑` rule.

```
unk⊑gnd-inv : ∀{G}
   → (c : ★ ⊑ gnd⇒ty G)
   → ∃[ d ] c ≡ unk⊑{G}{gnd⇒ty G} d
unk⊑gnd-inv {$ᵍ ι} (unk⊑ {$ᵍ .ι} base⊑) = base⊑ , refl
unk⊑gnd-inv {★⇒★} (unk⊑ {★⇒★} (fun⊑ c d)) = fun⊑ c d , refl
```

If `c` and `d` are both derivations of `★ ⊑ A`, then they are equal.

```
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
```

If `c` and `d` are both derivations of `gnd⇒ty G ⊑ A`, then
they are equal.

```
gnd-prec-unique : ∀{G A}
   → (c : gnd⇒ty G ⊑ A)
   → (d : gnd⇒ty G ⊑ A)
   → c ≡ d
gnd-prec-unique {$ᵍ ι} {.($ₜ ι)} base⊑ base⊑ = refl
gnd-prec-unique {★⇒★} {.(_ ⇒ _)} (fun⊑ c c₁) (fun⊑ d d₁)
    with dyn-prec-unique c d | dyn-prec-unique c₁ d₁
... | refl | refl = refl
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

Next we proceed to define the logical relation for values, the
predicate `LRᵥ`. In the case of precision for base types `base⊑`, we
only relate identical constants.

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
`StepIndexedLogic` instead takes care of that complication, ensuring
that our logical relation is downward closed.

In the case for relating two values of the unknown type `★`,
two injections are related if they are injections from the same
ground types and if the underlying values are related later.

```
LRᵥ (.★ , .★ , unk⊑unk) dir (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ Refl⊑{gnd⇒ty G}))
... | no neq = ⊥ ˢ
LRᵥ (.★ , .★ , unk⊑unk) dir V V′ = ⊥ ˢ
```

In the case for relating two values where the less precise value is of
unknown type but the more precise value is not, our definition depends
on the direction (`≼` or `≽`). For the `≼` direction, the underlying
values must be related later. Alternatively, we could relate them now,
by using recusion on the precision derivation `d`, but the proof of
the compatibility lemma for a projection on the more-precise side
depends on only requiring the two underlying values to be related later.

```
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≼ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ ▷ˢ (≼ ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ d)
... | no neq = ⊥ ˢ
```

For the `≽` direction, the underlying values must be related now.
Alternatively, we could relate them later, but the proof of the
compatibility lemma for a projection on the less-precise side depends
on the underlying values being related now.

```
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≽ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (LRᵥ (gnd⇒ty G , A′ , d) ≽ V V′)
... | no neq = ⊥ ˢ
LRᵥ (★ , .A′ , unk⊑{H}{A′} d) dir V V′ = ⊥ ˢ
```

With `LRₜ` and `LRᵥ` in hand, we can define the combined predicate
`pre-LRₜ⊎LRᵥ` and then use the fixpoint operator `μᵒ` from the
StepIndexedLogic to define the combined logical relation.

```
pre-LRₜ⊎LRᵥ : LR-type → Setˢ LR-ctx (cons Later ∅)
pre-LRₜ⊎LRᵥ (inj₁ (c , dir , V , V′)) = LRᵥ c dir V V′
pre-LRₜ⊎LRᵥ (inj₂ (c , dir , M , M′)) = LRₜ c dir M M′

LRₜ⊎LRᵥ : LR-type → Setᵒ
LRₜ⊎LRᵥ X = μᵒ pre-LRₜ⊎LRᵥ X
```

We now give the main definitions for the logical relation, `⊑ᴸᴿᵥ` for
values and the `⊑ᴸᴿₜ` for terms.

```
_∣_⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ = LRₜ⊎LRᵥ (inj₁ ((_ , _ , A⊑A′) , dir , V , V′))

_∣_⊑ᴸᴿₜ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = LRₜ⊎LRᵥ (inj₂ ((_ , _ , A⊑A′) , dir , M , M′))
```

The following notation is for the conjunction of both directions.

```
_⊑ᴸᴿₜ_⦂_ : Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = (≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) ×ᵒ (≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′)
```

# Relating open terms

The relations that we have defined so far, `⊑ᴸᴿᵥ` and `⊑ᴸᴿₜ`, only
apply to closed terms, that is, terms with no free variables.  We also
need to related open terms. The standard way to do that is to apply
two substitutions to the two terms, replacin each free variable with
related values.

So we relate a pair of substitutions `γ` and `γ′` with this definition
of `Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′`, which says that the substitutions must be pointwise
related using the logical relation for values.

```
_∣_⊨_⊑ᴸᴿ_ : (Γ : List Prec) → Dir → Subst → Subst → List Setᵒ
[] ∣ dir ⊨ γ ⊑ᴸᴿ γ′ = []
((_ , _ , A⊑A′) ∷ Γ) ∣ dir ⊨ γ ⊑ᴸᴿ γ′ = (dir ∣ (γ 0) ⊑ᴸᴿᵥ (γ′ 0) ⦂ A⊑A′)
                     ∷ (Γ ∣ dir ⊨ (λ x → γ (suc x)) ⊑ᴸᴿ (λ x → γ′ (suc x)))
```

We then define two open terms `M` and `M′` to be logically related
if there are a pair of related subtitutions `γ` and `γ′` such that
applying them to `M` and `M′` produces related terms.

```
_∣_⊨_⊑ᴸᴿ_⦂_ : List Prec → Dir → Term → Term → Prec → Set
Γ ∣ dir ⊨ M ⊑ᴸᴿ M′ ⦂ (_ , _ , A⊑A′) = ∀ (γ γ′ : Subst)
   → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′) ⦂ A⊑A′
```

We use the following notation for the conjunction of the two
directions and define the `proj` function for accessing each
direction.

```
_⊨_⊑ᴸᴿ_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ᴸᴿ M′ ⦂ c = (Γ ∣ ≼ ⊨ M ⊑ᴸᴿ M′ ⦂ c) × (Γ ∣ ≽ ⊨ M ⊑ᴸᴿ M′ ⦂ c)

proj : ∀ {Γ}{c}
  → (dir : Dir)
  → (M M′ : Term)
  → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ c
  → Γ ∣ dir ⊨ M ⊑ᴸᴿ M′ ⦂ c
proj {Γ} {c} ≼ M M′ M⊑M′ = proj₁ M⊑M′
proj {Γ} {c} ≽ M M′ M⊑M′ = proj₂ M⊑M′
```

# Reasoning about the logical relation

Unfortunately, there is some overhead to using the StepIndexedLogic to
define the logical relation. One needs to use the `fixpointᵒ` theorem
to obtain usable definitions.

The following states what we would like the `⊑ᴸᴿₜ` relation to look
like.

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

We prove that the above is equivalent to `⊑ᴸᴿₜ` with the following lemma,
using the `fixpointᵒ` theorem in several places.

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
```

In situations where we need to reason with an explicit step index `k`,
we use the following corollary.

```
LRₜ-suc : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}{k}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k) ⇔ #(LRₜ-def A⊑A′ dir M M′) (suc k)
LRₜ-suc {A}{A′}{A⊑A′}{dir}{M}{M′}{k} =
   ≡ᵒ⇒⇔{k = suc k} (LRₜ-stmt{A}{A′}{A⊑A′}{dir}{M}{M′})
```

# The logical relation implies semantic approximation

Before getting too much further, its good to check whether the logical
relation is strong enough, i.e., it should imply semantic
approximation. Indeed, the following somewhat verbose but easy lemma
proves that it does so.

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

# The logical relation implies the gradual guarantee

Putting together the above lemma with `sem-approx⇒GG`, we know that
the logical relation implies the gradual guarantee.

```
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
```

# Looking forward to the fundamental lemma

The `fundamental` lemma is the last, but largest, piece of the puzzle.
It states that if `M` and `M′` are related by term precision, then
they are also logically related.

    fundamental : ∀ {Γ}{A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
      → Γ ⊩ M ⊑ M′ ⦂ A⊑A′
        ----------------------------
      → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (A , A′ , A⊑A′)

The proof of the fundamental lemma is by induction on the term
precision relation, with each case proved as a separate lemma.  By
tradition, we refer to these lemmas as the compatibility lemmas. The
proofs of the compatibility lemmas rely on a considerable number of
technical lemmas regarding the logical relation, which we prove next.

# The logical relation is preserved by anti-reduction (aka. expansion)

If two terms are related, then taking a step backwards with either or
both of the terms yields related terms. For example, if `≼ ∣ N ⊑ᴸᴿₜ M′`
and we step `N` backwards to `M`, then we have `≼ ∣ M ⊑ᴸᴿₜ M′`.

```
anti-reduction-≼-L-one : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≼ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i
  → (M→N : M —→ N)
    ----------------------------
  → #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
anti-reduction-≼-L-one {c = c} {M} {N} {M′} {i} ℰ≼NM′i M→N =
  inj₁ (N , M→N , ℰ≼NM′i)
```

Because the `≼` direction observes the reduction steps of the
less-precise term, and the above lemma is about taking a backward step
with the less-precise term, the step index increases by one, i.e.,
not the `i` in the premise and `suc i` in the conclusion above.

If instead the backward step is taken by the more-precise term, then
the step index does not change, as in the following lemma.

```
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
```

Here are the anti-reduction lemmas for the `≽` direction.

```
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
```

Putting together the above lemmas, we show that taking a step
backwards on both sides yields terms that are related.

```
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
```

We shall also need to know that taking multiple steps backwards is
preserved by the logical relation. For the `≼` direction, we need this
for taking backward steps with the more-precise term.

```
anti-reduction-≼-R : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≼ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M′→N′ : M′ —↠ N′)
  → #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≼-R {M′ = M′} ℰMN′ (.M′ END) = ℰMN′
anti-reduction-≼-R {M′ = M′} {N′} {i} ℰMN′ (.M′ —→⟨ M′→L′ ⟩ L′→*N′) =
  anti-reduction-≼-R-one (anti-reduction-≼-R ℰMN′ L′→*N′) M′→L′
```

For the `≽` direction, we need this for taking backward steps with the
less-precise term.

```
anti-reduction-≽-L : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≽ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i
  → (M→N : M —↠ N)
  → #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≽-L {c = c} {M} {.M} {N′} {i} ℰNM′ (.M END) = ℰNM′
anti-reduction-≽-L {c = c} {M} {M′} {N′} {i} ℰNM′ (.M —→⟨ M→L ⟩ L→*N) =
  anti-reduction-≽-L-one (anti-reduction-≽-L ℰNM′ L→*N) M→L
```

# Blame is more precise

The `blame` term immediately errors, so it is logically related to any
term on the less-precise side.

```
LRₜ-blame-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{k}
   → #(dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′) k
LRₜ-blame-step {A}{A′}{A⊑A′}{dir} {M} {zero} = tz (dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′)
LRₜ-blame-step {A}{A′}{A⊑A′}{≼} {M} {suc k} = inj₂ (inj₁ (blame END))
LRₜ-blame-step {A}{A′}{A⊑A′}{≽} {M} {suc k} = inj₂ (inj₁ isBlame)

LRₜ-blame : ∀{𝒫}{A}{A′}{A⊑A′ : A ⊑ A′}{M}{dir}
   → 𝒫 ⊢ᵒ dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′
LRₜ-blame {𝒫}{A}{A′}{A⊑A′}{M}{dir} = ⊢ᵒ-intro λ n x → LRₜ-blame-step{dir = dir}
```

Next we turn to proving lemmas regarding the logical relation for
values.

# Related values are syntatic values

The definitionn of `⊑ᴸᴿᵥ` included several clauses that ensured that
the related values are indeed syntactic values. Here we make use of
that to prove that indeed, logically related values are syntactic
values.

```
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
```

# Logically related values are logically related terms

If two values are related via `⊑ᴸᴿᵥ`, then they are also related via
`⊑ᴸᴿₜ` at the same step index.

```
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
```

As a corollary, this holds for all step indices, i.e., it holds in the
logic.

```
LRᵥ⇒LRₜ : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{𝒫}{V V′}{dir}
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′
     ---------------------------
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′
LRᵥ⇒LRₜ {A}{A′}{A⊑A′}{𝒫}{V}{V′}{dir} ⊢𝒱VV′ = ⊢ᵒ-intro λ k 𝒫k →
  LRᵥ⇒LRₜ-step{V = V}{V′}{dir}{k} (⊢ᵒ-elim ⊢𝒱VV′ k 𝒫k)
```

# Equations regarding `⊑ᴸᴿᵥ`

We apply the `fixpointᵒ` theorem to fold or unfold the definition of
related lambda abstractions.

```
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
```

# Elimination rules for `⊑ᴸᴿᵥ`

If we are given that two values are logically related at two types
related by a particular precision rule, then we can deduce something
about the shape of the values.

If the two types are base types, then the values are identical
literals.

```
LRᵥ-base-elim-step : ∀{ι}{ι′}{c : $ₜ ι ⊑ $ₜ ι′}{V}{V′}{dir}{k}
  → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) (suc k)
  → ∃[ c ] ι ≡ ι′ × V ≡ $ c × V′ ≡ $ c
LRᵥ-base-elim-step {ι} {.ι} {base⊑} {$ c} {$ c′} {dir} {k} refl =
  c , refl , refl , refl
```

If the two types are function types related by `fun⊑`, then the values
are lambda expressions and their bodies are related as follows.

```
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
```

For the `≼` direction, if the two types are related by `unk⊑`, so the
less-precise side has type `★`, then the value on the less-precise
side is an injection and its underlying value is related later.

```
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
```

For the `≽` direction, if the two types are related by `unk⊑`, so the
less-precise side has type `★`, then the value on the less-precise
side is an injection and its underlying value is related now, i.e., at
the same step-index.

```
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
```

# Introduction rules for `⊑ᴸᴿᵥ`

In the proofs of the compatibility lemmas we will often need to prove
that values of a particular form are related by `⊑ᴸᴿᵥ`. The following
lemmas do this. We shall need lemmas to handle injections on both the
less and more-precise side, and in both directions `≼` and `≽`.

We start with the introduction rule for relating literals at base
type.

```
LRᵥ-base-intro-step : ∀{ι}{dir}{c}{k} → # (dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}) k
LRᵥ-base-intro-step {ι} {dir} {c} {zero} = tt
LRᵥ-base-intro-step {ι} {dir} {c} {suc k} = refl

LRᵥ-base-intro : ∀{𝒫}{ι}{c}{dir}
   → 𝒫 ⊢ᵒ dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}
LRᵥ-base-intro{𝒫}{ι}{c}{dir} = ⊢ᵒ-intro λ k 𝒫k →
  LRᵥ-base-intro-step{ι}{dir}{c}{k}
```

In the `≽` direction, an injection on the more-precise side is related
if its underlying value is related at the same step index.

```
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
```

The same is true for the `≼` direction.

```
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
```

We combine both directions into the following lemma.

```
LRᵥ-inject-R-intro : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}{dir}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(dir ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
LRᵥ-inject-R-intro {G} {c} {V} {V′} {k} {≼} 𝒱VV′ =
   LRᵥ-inject-R-intro-≼{G} {c} {V} {V′} {k} 𝒱VV′ 
LRᵥ-inject-R-intro {G} {c} {V} {V′} {k} {≽} 𝒱VV′ =
   LRᵥ-inject-R-intro-≽{G} {c} {V} {V′} {k} 𝒱VV′
```

In the `≼` direction, an injection on the less-precise side is related
if its underlying value is related at one step earlier.

```
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
```

In the `≽` direction, an injection on the less-precise side is related
if its underlying value is related now, i.e., at the same step
index.

```
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
```

We can combine the two directions into the following lemma, which
states that an injection on the less-precise side is related if its
underlying value at the same step index. The proof uses downward
closedness in the `≼` direction.

```
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
```

# The Bind Lemma

The last technical lemma before we get to the compatibility lemmas in
the gnarly Bind Lemma.

Let `F` and `F′` be possibly empty frames and recall that the `_⦉_⦊`
notation is for plugging a term into a frame.

Roughly speaking, the Bind Lemma shows that if you are trying to prove

    F ⦉ M ⦊ ⊑ᴸᴿₜ F′ ⦉ M′ ⦊

for arbitrary terms `M` and `M′`, then it suffices to prove that

    F ⦉ V ⦊ ⊑ᴸᴿₜ F′ ⦉ V′ ⦊

for some values `V` and `V′` under the assumptions

    M —↠ V
    M′ —↠ V′
    V ⊑ᴸᴿᵥ V′

The Bind Lemma is used in all of the compatibility lemmas concerning
terms that have may have reducible sub-terms, i.e., application,
injection, and projection.

Here is the statement of the Bind lemma with all the gory details.

    LRₜ-bind : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}
                     {F}{F′}{M}{M′}{i}{dir}
       → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ d) i
       → (∀ j V V′ → j ≤ i → M —↠ V → Value V → M′ —↠ V′ → Value V′
             → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
             → #(dir ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
       → #(dir ∣ (F ⦉ M ⦊) ⊑ᴸᴿₜ (F′ ⦉ M′ ⦊) ⦂ c) i

We define the following abbreviation for the `(∀ j V V′ ...)` premise
of the Bind Lemma.

```
bind-premise : Dir → PEFrame → PEFrame → Term → Term → ℕ
   → ∀ {B}{B′}(c : B ⊑ B′) → ∀ {A}{A′} (d : A ⊑ A′) → Set
bind-premise dir F F′ M M′ i c d =
    (∀ j V V′ → j ≤ i → M —↠ V → Value V → M′ —↠ V′ → Value V′
     → # (dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
     → # (dir ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
```

The premise is preserved with respect to `M` reducing to `N` and also
`M′` reducing to `N′`, with the step index decreasing by one, which we
show in the following two lemmas.

```
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
```

The Bind Lemma is proved by induction on the step index `i`. The base
case is trivially true because the logical relation is always true at
zero. For the inductive step, we reason separately about the two
directions `≼` and `≽`, and then reason by cases on the premise that
`M ⊑ᴸᴿₜ M′`. If `M` or `M′` take a single step to related terms, we
use the induction hypothesis, applying the above lemmas to obtain the
premise of the induction hypothesis. If `M` or `M′` are values,
then we use the anti-reduction lemmas. Otherwise, if `M′` is `blame`,
then `F′ ⦉ blame ⦊` reduces to `blame`.

```
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
```

# Compatibility Lemmas

The end is in sight! We just have to prove nine compatibility lemmas.
The first few are easy. The ones about projection are the most
interesting.

A literal expression `$ c` is related to itself, via the
`LRᵥ-base-intro` and `LRᵥ⇒LRₜ` lemmas.

```
compatible-literal : ∀{Γ}{c}{ι}
   → Γ ⊨ $ c ⊑ᴸᴿ $ c ⦂ ($ₜ ι , $ₜ ι , base⊑)
compatible-literal {Γ}{c}{ι} =
  (λ γ γ′ → LRᵥ⇒LRₜ LRᵥ-base-intro) , (λ γ γ′ → LRᵥ⇒LRₜ LRᵥ-base-intro)
```

`blame` on the right-hand side is logically related to anything on the
left (less precise) side.

```
compatible-blame : ∀{Γ}{A}{M}
   → map proj₁ Γ ⊢ M ⦂ A
     -------------------------------
   → Γ ⊨ M ⊑ᴸᴿ blame ⦂ (A , A , Refl⊑)
compatible-blame{Γ}{A}{M} ⊢M = (λ γ γ′ → LRₜ-blame) , (λ γ γ′ → LRₜ-blame)
```

Next we prove the compatibility lemmas for variables. For that we
need to know that given two related substitutions `γ ⊑ᴸᴿ γ′`,
applying them to the same variable yields related values: `γ x ⊑ᴸᴿᵥ γ′ x`.

```
lookup-⊑ᴸᴿ : ∀{dir} (Γ : List Prec) → (γ γ′ : Subst)
  → ∀ {A}{A′}{A⊑A′}{x} → Γ ∋ x ⦂ (A , A′ , A⊑A′)
  → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ γ x ⊑ᴸᴿᵥ γ′ x ⦂ A⊑A′
lookup-⊑ᴸᴿ {dir} (.(A , A′ , A⊑A′) ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
lookup-⊑ᴸᴿ {dir} (B ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {suc x} ∋x =
   Sᵒ (lookup-⊑ᴸᴿ Γ (λ z → γ (suc z)) (λ z → γ′ (suc z)) ∋x)
```

We then use `LRᵥ⇒LRₜ` to show that `γ x ⊑ᴸᴿₜ γ′ x`. (The `sub-var`
lemma just says that `⟪ γ ⟫ (` x) ≡ γ x`.)

```
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
```

The compatibility lemma for lambda is easy but important.  Roughly
speaking, tt takes the premise `N ⊑ᴸᴿ N′` and stores it in the logical
relation for the lambda values, `ƛ N ⊑ᴸᴿₜ ƛ N′`, which is needed to
prove the compatibility lemma for function application.

```
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
```

The compatibility lemma for function application shows that
two applications are logically related

    L · M ⊑ᴸᴿ L′ · M′

if their operator and operand terms are logically related

    L ⊑ᴸᴿ L′
    M ⊑ᴸᴿ M′

The proof starts with two uses of the Bind Lemma, after which it
remains to prove

    V · W ⊑ᴸᴿₜ V′ · W′

for some `V`, `W`, `V′`, and `W′` where

    L —↠ V, L′ —↠ V′, V ⊑ᴸᴿᵥ V′
    M —↠ W, M′ —↠ W′, W ⊑ᴸᴿᵥ W′
    
We apply the elimination lemma for function types, `LRᵥ-fun-elim-step`,
to `V ⊑ᴸᴿᵥ V′`, so `V` and `V′` are related lambda expressions:

    ƛ N ⊑ᴸᴿᵥ ƛ N′

Thanks to the definition of `⊑ᴸᴿᵥ`, we therefore know that

    N [ W ] ⊑ᴸᴿₜ N′ [ W′ ]

Of course, via β reduction

   (ƛ N) · W   —→ N [ W ]
   (ƛ N′) · W′ —→ N′ [ W′ ]
   
so we can apply anti-reduction to conclude that

   (ƛ N) · W ⊑ᴸᴿₜ (ƛ N′) · W′

Now here's the proof in Agda.

```
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
```

We have four more compatibility lemmas to prove, regarding injections
and projections on the left and right-hand side.

For an injection on the left, we apply the Bind Lemma, so it remains
to prove that

    V ⟨ G !⟩ ⊑ᴸᴿ V′

for some values `V` and `V′` where

    M —↠ V, M′ —↠ V′, V ⊑ᴸᴿᵥ V′

We apply `LRᵥ-inject-L-intro` to obtain

    V ⟨ G !⟩ ⊑ᴸᴿᵥ V′

and then conclude via `LRᵥ⇒LRₜ-step`.

```
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
```

For an injection on the right, the proof is similar but uses the 
`LRᵥ-inject-R-intro` lemma.

```
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
```

For projection on the left, we again start with an application of the
Bind Lemma. So we need to show that

    V ⟨ H ?⟩ ⊑ᴸᴿₜ V′

for some values `V` and `V′` where

    M —↠ V, M′ —↠ V′, V ⊑ᴸᴿᵥ V′

The proof is by induction on the step index `j`. The base case is
trivially true because the logical relation is always true at zero.
For the inductive step we consider the step index `suc j`, so
we need to prove

    #(V ⟨ H ?⟩ ⊑ᴸᴿₜ V′) (suc j)

We proceed by cases on the two directions `≼` and `≽`.

For the `≼` case, we use lemma `LRᵥ-dyn-any-elim-≼` with `#(V ⊑ᴸᴿᵥ V′) (suc j)`
to obtain

    V ≡ V₁ ⟨ H !⟩
    #(V₁ ⊑ᴸᴿᵥ V′) j

We use `LRᵥ⇒LRₜ-step` to obtain

    #(V₁ ⊑ᴸᴿₜ V′) j

and then because

    V₁ ⟨ H !⟩ ⟨ H ?⟩ —→ V₁

The `anti-reduction-≼-L-one` lemma allows us to conclude that

    #(V₁ ⟨ H !⟩ ⟨ H ?⟩ ⊑ᴸᴿₜ V′) (suc j)

For the `≽` case, we use lemma `LRᵥ-dyn-any-elim-≽` with `#(V ⊑ᴸᴿᵥ V′) (suc j)`
to obtain

    V ≡ V₁ ⟨ H !⟩
    #(V₁ ⊑ᴸᴿᵥ V′) (suc j)

(Recall that in the definition of `⊑ᴸᴿᵥ` for `unk⊑` and `≽`, we chose
to relate the underlying value now, i.e., at `suc j`.)
By definition, to prove `#(V₁⟨ H !⟩⟨ H ?⟩ ⊑ₜ V′) (suc j)`, it suffices
to show that the left-hand side reduces to a related value at `suc j`
(because the right-hand side is a value), which we have already
proved.

```
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
```

The last compatibility lemma is for projection on the right.
As usual we start with the Bind Lemma, so our goal is to
prove that 

    V ⊑ᴸᴿₜ V′ ⟨ H ?⟩

for some values `V` and `V′` where

    M —↠ V, M′ —↠ V′, V ⊑ᴸᴿᵥ V′

The proof is by induction on the step index `j`. The base case is
trivially true because the logical relation is always true at zero.
For the inductive step we consider the step index `suc j`, so
we need to prove

    #(V ⊑ᴸᴿₜ V′ ⟨ H ?⟩) (suc j)

Note that `V` and `V′` are both of type `★`, by 
definition `V ⊑ᴸᴿᵥ V′` gives us

    V ≡ V₁ ⟨ G !⟩
    V′ ≡ V₁′ ⟨ G !⟩
    



```
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
```

# Proof of the Fundamental Lemma

```
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
```

# Proof of the Gradual Guarantee

```
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
```
