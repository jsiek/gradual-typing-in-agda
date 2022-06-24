open import Data.Nat
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app;
            inspect; [_])

module Denot.LazyCoercionsRegular where

  open import Types
  open import Labels
  open import CastStructureABT
  open import LazyCoercionsABT
  open import Denot.Value
  open import SetsAsPredicates


-- TODO
  -- most of data def for coercion meaning
  -- shallow-typechecking; coerce-val
  -- finish data def for coercion meaning
  -- define value consistency
  -- prove consistency lemma
  -- prove blame results that repackage the consitency lemma
  -- prove soundness wrt operational semantics
  -- 



  infix 4 _↝⟦_∶_⟧↝_


  {-
    We want this version of the meaning of coercions to reflect the behavior
    of the small-step operational semantics of LazyCoercions.
    That includes, most importantly, the cast rule:

      cast : ∀ {A B} {V : Term} {c : Cast (A ⇒ B)}
        → (⊢V : [] ⊢ V ⦂ A) → (v : Value V) → {a : Active c}
          ------------------------------
        → V ⟨ c ⟩ —→ applyCast V ⊢V v c {a}

    which reflects the applyCast definition for LazyCoercions

      applyCast M Γ⊢M∶A v id {a} = M
      applyCast M Γ⊢M∶A v (B ?? ℓ) {a} with canonical⋆ Γ⊢M∶A v
      ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , ⟨ q , refl ⟩ ⟩ ⟩ ⟩ ⟩ = M' ⟨ coerce A' B ℓ ⟩
      applyCast {A = A ⇒ B} {B = A' ⇒ B'} M Γ⊢M∶A v (c ↣ d) {a} = 
        ƛ A' ˙ ((rename suc M · ((` zero) ⟨ c ⟩)) ⟨ d ⟩)
      applyCast M Γ⊢M∶A v (c `× d) {a} = 
        ⟦ first M ⟨ c ⟩ , second M ⟨ d ⟩ ⟧
      applyCast {A = A `⊎ B} {B = A' `⊎ B'} M Γ⊢M∶A v (c `+ d) {a} =
        let L = inl ((` zero) ⟨ c ⟩) other B' in
        let R = inr ((` zero) ⟨ d ⟩) other A' in
            case M of A ⇒ L ∣ B ⇒ R
      applyCast M Γ⊢M∶A v (⊥ A ⟨ ℓ ⟩ B) {a} = mkblame B ℓ

    where the canonical⋆ case encodes the fact that
      all syntactic Values that type at ⋆
      are wrap terms (with inert casts)
        -- intuitively: syntactic values usually type at specific types; except wrap
  
    But also we use the wrap rule for inert coercions

      wrap : ∀ {A B} {V : Term} {c : Cast (A ⇒ B)}
        → (v : Value V) → {i : Inert c}
          ------------------------------
        → V ⟨ c ⟩ —→ V ⟨ c ₍ i ₎⟩

    which leads into the cases for the cross inert casts

      fun-cast : ∀ {A B C D} {V W : Term} {c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}
        → Value V → Value W → {x : Cross c} → {i : Inert c}
          --------------------------------------------------
        → V ⟨ c ₍ i ₎⟩ · W —→ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩

      fst-cast : ∀ {A B C D} {V : Term} {c : Cast ((A `× B) ⇒ (C `× D))}
        → Value V → {x : Cross c} → {i : Inert c}
          -------------------------------------
        → fst (V ⟨ c ₍ i ₎⟩) —→ (fst V) ⟨ fstC c x ⟩

      snd-cast : ∀ {A B C D} {V : Term} {c : Cast ((A `× B) ⇒ (C `× D))}
        → Value V → {x : Cross c} → {i : Inert c}
          -------------------------------------
        → snd (V ⟨ c ₍ i ₎⟩) —→ (snd V) ⟨ sndC c x ⟩

      case-cast : ∀ {A B C D} {V M N : Term} {c : Cast (A `⊎ B ⇒ C `⊎ D)}
        → Value V → {x : Cross c} → {i : Inert c}
          --------------------------------------------
        → case (V ⟨ c ₍ i ₎⟩) of C ⇒ M ∣ D ⇒ N
            —→ case V of A ⇒ (rename (ext ⇑) M [ ` 0 ⟨ inlC c x ⟩ ])
                       ∣ B ⇒ (rename (ext ⇑) N [ ` 0 ⟨ inrC c x ⟩ ])
  -}

  -- The hope is that we can make regular coercions a function on denot@ values

  fst-val : Val → Val
  fst-val (blame ℓ) = blame ℓ
  fst-val v = fst v

  snd-val : Val → Val
  snd-val (blame ℓ) = blame ℓ
  snd-val v = snd v

  fst-val-type : ∀ A B {v} → ⟦ v ∶ A ⟧ → ⟦ fst-val v ∶ A `× B ⟧
  fst-val-type A B {blame ℓ} v∶A = tt
  fst-val-type A B {const k} v∶A = v∶A
  fst-val-type A B {V ↦ v} v∶A = v∶A
  fst-val-type A B {ν} v∶A = v∶A
  fst-val-type A B {fst v} v∶A = v∶A
  fst-val-type A B {snd v} v∶A = v∶A
  fst-val-type A B {inl V} v∶A = v∶A
  fst-val-type A B {inr V} v∶A = v∶A

  snd-val-type : ∀ A B {v} → ⟦ v ∶ B ⟧ → ⟦ snd-val v ∶ A `× B ⟧
  snd-val-type A B {const k} v∶B = v∶B
  snd-val-type A B {V ↦ v} v∶B = v∶B
  snd-val-type A B {ν} v∶B = v∶B
  snd-val-type A B {fst v} v∶B = v∶B
  snd-val-type A B {snd v} v∶B = v∶B
  snd-val-type A B {inl V} v∶B = v∶B
  snd-val-type A B {inr V} v∶B = v∶B
  snd-val-type A B {blame ℓ} v∶B = tt

  sum-val-aux : List Val → List Val ⊎ Label
  sum-val-aux [] = inj₁ []
  sum-val-aux (blame ℓ ∷ V) = inj₂ ℓ
  sum-val-aux (v ∷ V) with sum-val-aux V
  ... | inj₁ V' = inj₁ (v ∷ V')
  ... | inj₂ ℓ = inj₂ ℓ

  inl-val : List Val → Val
  inl-val V with sum-val-aux V
  ... | inj₁ V' = inl V'
  ... | inj₂ ℓ = blame ℓ

  inr-val : List Val → Val
  inr-val V with sum-val-aux V
  ... | inj₁ V' = inr V'
  ... | inj₂ ℓ = blame ℓ

  sum-val-aux-type : ∀ {A V V'} → ⟦ V ∶ A ⟧₊ → sum-val-aux V ≡ inj₁ V' → ⟦ V' ∶ A ⟧₊
  sum-val-aux-type {A} {[]} {V'} V∶A refl = tt
  sum-val-aux-type {A} {const k ∷ V} {V'} ⟨ v∶A , V∶A ⟩ eq with sum-val-aux V | inspect sum-val-aux V | eq
  ... | inj₂ ℓ | _ | ()
  ... | inj₁ U | [ sum-val-auxV≡inj₁U ] | eq with inj₁-injective eq
  ... | refl = ⟨ v∶A , sum-val-aux-type V∶A sum-val-auxV≡inj₁U ⟩
  sum-val-aux-type {A} {(V₁ ↦ v) ∷ V} {V'} ⟨ v∶A , V∶A ⟩ eq with sum-val-aux V | inspect sum-val-aux V | eq
  ... | inj₂ ℓ | _ | ()
  ... | inj₁ U | [ sum-val-auxV≡inj₁U ] | eq with inj₁-injective eq
  ... | refl = ⟨ v∶A , sum-val-aux-type V∶A sum-val-auxV≡inj₁U ⟩
  sum-val-aux-type {A} {ν ∷ V} {V'} ⟨ v∶A , V∶A ⟩ eq with sum-val-aux V | inspect sum-val-aux V | eq
  ... | inj₂ ℓ | _ | ()
  ... | inj₁ U | [ sum-val-auxV≡inj₁U ] | eq with inj₁-injective eq
  ... | refl = ⟨ v∶A , sum-val-aux-type V∶A sum-val-auxV≡inj₁U ⟩
  sum-val-aux-type {A} {fst v ∷ V} {V'} ⟨ v∶A , V∶A ⟩ eq with sum-val-aux V | inspect sum-val-aux V | eq
  ... | inj₂ ℓ | _ | ()
  ... | inj₁ U | [ sum-val-auxV≡inj₁U ] | eq with inj₁-injective eq
  ... | refl = ⟨ v∶A , sum-val-aux-type V∶A sum-val-auxV≡inj₁U ⟩
  sum-val-aux-type {A} {snd v ∷ V} {V'} ⟨ v∶A , V∶A ⟩ eq with sum-val-aux V | inspect sum-val-aux V | eq
  ... | inj₂ ℓ | _ | ()
  ... | inj₁ U | [ sum-val-auxV≡inj₁U ] | eq with inj₁-injective eq
  ... | refl = ⟨ v∶A , sum-val-aux-type V∶A sum-val-auxV≡inj₁U ⟩
  sum-val-aux-type {A} {inl V₁ ∷ V} {V'} ⟨ v∶A , V∶A ⟩ eq with sum-val-aux V | inspect sum-val-aux V | eq
  ... | inj₂ ℓ | _ | ()
  ... | inj₁ U | [ sum-val-auxV≡inj₁U ] | eq with inj₁-injective eq
  ... | refl = ⟨ v∶A , sum-val-aux-type V∶A sum-val-auxV≡inj₁U ⟩
  sum-val-aux-type {A} {inr V₁ ∷ V} {V'} ⟨ v∶A , V∶A ⟩ eq with sum-val-aux V | inspect sum-val-aux V | eq
  ... | inj₂ ℓ | _ | ()
  ... | inj₁ U | [ sum-val-auxV≡inj₁U ] | eq with inj₁-injective eq
  ... | refl = ⟨ v∶A , sum-val-aux-type V∶A sum-val-auxV≡inj₁U ⟩

  inl-val-type : ∀ A B {V} → ⟦ V ∶ A ⟧₊ → ⟦ inl-val V ∶ A `⊎ B ⟧
  inl-val-type A B {V} V∶A with sum-val-aux V | inspect sum-val-aux V
  ... | inj₁ V' | [ eq ] = sum-val-aux-type V∶A eq
  ... | inj₂ ℓ | _ = tt

  inr-val-type : ∀ A B {V} → ⟦ V ∶ B ⟧₊ → ⟦ inr-val V ∶ A `⊎ B ⟧
  inr-val-type A B {V} V∶B with sum-val-aux V | inspect sum-val-aux V
  ... | inj₁ V' | [ eq ] = sum-val-aux-type V∶B eq
  ... | inj₂ ℓ | _ = tt
  

  {- There is one major problem with this definition:
    We need to guarantee that if we coerce a denotation to blame, it only produces one blame label.
    There are at least a couple places this problem crops up:
      + the phrasing "v ∈ mem V  and v ↝ blame ℓ ==> ?? ↝ blame ℓ"
        a priori lets through too much blame... but there's maybe some condition where
        consistent values coerce to the same blame label, and we can gaurantee that
        everything in V is consistent.
      + the other major problem is product denotations.
        We may produce blame from the first and second components failing the subcoercions
        and these sources of blame may have different labels;
        we want to have an execution order to the coercion where we blame the first component
        before we blame the second component.
           (a weird alternative would be to have blame that is both labeled and structured;
            then we could produce structured blame and mimic the execution order by inspecting the structure of the blame we get back.)
        There isn't a good way to filter these two sources of blame without inspecting the entire denotation.  
  -}
  data _↝⟦_∶_⟧₊↝_ : ∀ {A B} V → (c : Cast (A ⇒ B)) → (u∶A : ⟦ u ∶ A ⟧) → (V' : List Val) → Set
  data _↝⟦_∶_⟧↝_ : ∀ {A B} → (u : Val) → (c : Cast (A ⇒ B)) → (u∶A : ⟦ u ∶ A ⟧) → (v ∶ Val) → Set where
    coerce-blame : ∀ {A B}{c : Cast (A ⇒ B)}{ℓ bl∶A} → blame ℓ ↝⟦ c ∶ bl∶A ⟧↝ blame ℓ
    coerce-id : ∀ {A B}{c : Cast (A ⇒ B)}{u v u∶A} → u ↝⟦ id ∶ u∶A ⟧↝ u
    coerce-inj : ∀ {A B}{c : Cast (A ⇒ B)}{u u∶A} → u ↝⟦ (A !!) ∶ u∶A ⟧↝ u
    coerce-proj-ok : ∀ {A B}{c : Cast (A ⇒ B)}{u ℓ u∶A} → ⟦ u ∶ B ⟧ → u ↝⟦ (B ?? ℓ) ∶ u∶A ⟧↝ u
    coerce-proj-fail : ∀ {A B}{c : Cast (A ⇒ B)}{u ℓ u∶A} → ¬ ⟦ u ∶ B ⟧ → u ↝⟦ (B ?? ℓ) ∶ u∶A ⟧↝ blame ℓ
    coerce-fun-fail-dom : ∀ {A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')} {u V v u∶A⇒B}
        → (V∶A' : ⟦ V ∶ A' ⟧₊) → v ∈ mem V → v ↝⟦ c ∶ ? ⟧↝ blame ℓ
        → u ↝⟦ c ↣ d ∶ u∶A⇒B ⟧↝ (V ↦ blame ℓ)
    coerce-fun-fail-cod :  ∀ {A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')}{V w ℓ V∶A→w∶B}
          -- successful c cast
        → ∀ (V∶A' : ⟦ V ∶ A' ⟧₊)
        → (∀ v → v ∈ mem V → v ↝⟦ c ∶ ? ⟧↝ v)
          -- failed d cast
        → ¬isBlame w
        → w ↝⟦ d ∶ ? ⟧↝ blame ℓ
        → V ↦ w ↝⟦ c ↣ d ∶ V∶A→w∶B ⟧↝ V ↦ blame ℓ
    coerce-fun-ok : ∀ {A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')}{V w V∶A→w∶B}
        -- successful c cast
      → ∀ (V∶A' : ⟦ V ∶ A' ⟧₊)
      → (∀ v → v ∈ mem V → v ↝⟦ c ∶ ? ⟧↝ v)
        -- successful d cast
      → w ↝⟦ d ∶ ? ⟧↝ w
      → V ↦ w ↝⟦ c ↣ d ∶ V∶A→w∶B ⟧↝ V ↦ w
    coerce-ν : ∀ {A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')}
      → ν ↝⟦ c ↣ d ∶ tt ⟧↝ ν
    coerce-prod-fail-fst : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')} {u ℓ u∶A}
      → u ↝⟦ c ∶ u∶A ⟧↝ blame ℓ
      → fst u ↝⟦ c `× d ∶ u∶A ⟧↝ blame ℓ
    -- this rule is why we need to define this on sets rather than single values, I think. 
    coerce-prod-fail-snd : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')} {v ℓ v∶B}
      → v ↝⟦ d ∶ v∶B ⟧↝ blame ℓ
      → snd v ↝⟦ c `× d ∶ v∶B ⟧↝ blame ℓ
    coerce-prod-ok-fst : ∀ {A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')} {u u∶A}
      → u ↝⟦ c ∶ u∶A ⟧↝ u
      → fst u ↝⟦ c `× d ∶ u∶A ⟧↝ fst u
    coerce-prod-ok-snd : ∀ {A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')} {v v∶B}
      → v ↝⟦ c ∶ v∶B ⟧↝ v
      → snd v ↝⟦ c `× d ∶ v∶B ⟧↝ snd v
    coerce-sum-fail-inl : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')} {V v ℓ}
      → (V∶A : ⟦ V ∶ A ⟧₊) → v ∈ mem V → v ↝⟦ c ∶ ? ⟧↝ blame ℓ
      → inl V ↝⟦ c `+ d ⟧↝ blame ℓ
    coerce-sum-fail-inr : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')} {V v ℓ}
      → (V∶B : ⟦ V ∶ B ⟧₊) → v ∈ mem V → v ↝⟦ d ∶ ? ⟧↝ blame ℓ
      → inr V ↝⟦ c `+ d ⟧↝ blame ℓ
    coerce-sum-ok-inl : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')} {V}
      → (V∶A : ⟦ V ∶ A ⟧₊) → (∀ v → v ∈ mem V → v ↝⟦ c ∶ ? ⟧↝ v)
      → inl V ↝⟦ c `+ d ⟧↝ inl V
    coerce-sum-ok-inr : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')} {V}
      → (V∶B : ⟦ V ∶ B ⟧₊) → (∀ v → v ∈ mem V → v ↝⟦ d ∶ ? ⟧↝ v)
      → inr V ↝⟦ c `+ d ⟧↝ inr V
    coerce-fail : ∀ {A B v ℓ v∶A} → v ↝⟦ ⊥ A ⟨ ℓ ⟩ B ∶ v∶A ⟧↝ blame ℓ




{-
  coerce-val {A ⇒ B}{A' ⇒ B'} (c ↣ d) (V ↦ w) V∶A→w∶B with ⟦ V ∶ A ⟧₊?
  ... | yes V∶A = V ↦ (coerce-val d w (V∶A→w∶B V∶A))
          -- operationally, at an application we take
          -- f ⟨ c ↣ d ⟩ · a ⟶ (f · (a ⟨ c ⟩)) ⟨ d ⟩
          -- if a ⟨ c ⟩ is blame ℓ , then we return blame ℓ immediately at the application site
          -- if a ⟨ c ⟩ suceeds, then we should be able to reuse V
  ... | no ¬V∶A = ν 
          -- I think this value shouldn't matter, because application never looks up V
          -- if V denoted an argument, it would produce blame in the app-blame-rand case

    V' ↝⟦ c ⟧↝ blame ℓ

    ν ↝⟦ c ↣ d ⟧↝ V' ↦ blame ℓ

  coerce-val (c ↣ d) ν u∶A = ν
  coerce-val (c ↣ d) (blame ℓ) u∶A = blame ℓ
  coerce-val (c `× d) (fst u) u∶A = fst-val (coerce-val c u u∶A)
  coerce-val (c `× d) (snd u) u∶A = snd-val (coerce-val d u u∶A)
  coerce-val (c `× d) (blame ℓ) u∶A = blame ℓ
  coerce-val (c `+ d) (inl U) U∶A = inl-val (coerce-val₊ c U U∶A)
  coerce-val (c `+ d) (inr U) U∶A = inr-val (coerce-val₊ d U U∶A)
  coerce-val (c `+ d) (blame ℓ) u∶A = blame ℓ
  coerce-val (⊥ A ⟨ ℓ ⟩ B) u u∶A = blame ℓ

-}



  coerce-val : ∀ {A B} → (c : Cast (A ⇒ B)) → (u : Val) → ⟦ u ∶ A ⟧ → Val
  coerce-val₊ : ∀ {A B} → (c : Cast (A ⇒ B)) → (U : List Val) → ⟦ U ∶ A ⟧₊ → List Val
  coerce-val₊ c [] tt = []
  coerce-val₊ c (u ∷ U) ⟨ u∶A , U∶A ⟩ = coerce-val c u u∶A ∷ coerce-val₊ c U U∶A 
  coerce-val id u u∶A = u
  coerce-val (A !!) u u∶A = u
  coerce-val (B ?? ℓ) u u∶A with ⟦ u ∶ B ⟧?  
     {- replace with shallow typecheck -}   V ↦ blame ℓ
  ... | yes u∶B = u
  ... | no ¬u∶B = blame ℓ

  u ↝⟦(⋆ → Int) ?? ℓ⟧↝ v
  
  V ↦ true ↝ V ↦ blame ℓ


  u ↝⟦(Int → ⋆) ?? ℓ⟧↝ v
  
  u : (Bool → Int)  ↝ ⋆

  [true] ↦ zero ↝   {Int} ↦ blame ℓ

  coercions:
     blame ↣ id


  u ↝⟦(⋆ → Int) ?? ℓ⟧↝ v
  
  V ↦ blame ℓ ↝ V ↦ blame ℓ


  u ↝⟦(A `× B) ?? ℓ⟧↝ v
  
  V ↦ blame ℓ' ↝ V ↦ blame ℓ'


V ∶ A ==> w ∶ B
--------------
V ↦ w ∶ A → B

  coerce-val {A ⇒ B}{A' ⇒ B'} (c ↣ d) (V ↦ w) V∶A→w∶B with ⟦ V ∶ A ⟧₊?
  ... | yes V∶A = V ↦ (coerce-val d w (V∶A→w∶B V∶A))
          -- operationally, at an application we take
          -- f ⟨ c ↣ d ⟩ · a ⟶ (f · (a ⟨ c ⟩)) ⟨ d ⟩
          -- if a ⟨ c ⟩ is blame ℓ , then we return blame ℓ immediately at the application site
          -- if a ⟨ c ⟩ suceeds, then we should be able to reuse V
  ... | no ¬V∶A = ν 
          -- I think this value shouldn't matter, because application never looks up V
          -- if V denoted an argument, it would produce blame in the app-blame-rand case

    V' ↝⟦ c ⟧↝ blame ℓ

    ν ↝⟦ c ↣ d ⟧↝ V' ↦ blame ℓ

  coerce-val (c ↣ d) ν u∶A = ν
  coerce-val (c ↣ d) (blame ℓ) u∶A = blame ℓ
  coerce-val (c `× d) (fst u) u∶A = fst-val (coerce-val c u u∶A)
  coerce-val (c `× d) (snd u) u∶A = snd-val (coerce-val d u u∶A)
  coerce-val (c `× d) (blame ℓ) u∶A = blame ℓ
  coerce-val (c `+ d) (inl U) U∶A = inl-val (coerce-val₊ c U U∶A)
  coerce-val (c `+ d) (inr U) U∶A = inr-val (coerce-val₊ d U U∶A)
  coerce-val (c `+ d) (blame ℓ) u∶A = blame ℓ
  coerce-val (⊥ A ⟨ ℓ ⟩ B) u u∶A = blame ℓ

  _↝⟦_∶_⟧↝_ : ∀ {A B} → (u : Val) → (c : Cast (A ⇒ B)) → ⟦ u ∶ A ⟧ → Val → Set
  u ↝⟦ c ∶ u∶A ⟧↝ v = v ≡ coerce-val c u u∶A

{-
  data _↝⟦_⟧↝_ : ∀ {A B} → Val → (c : Cast (A ⇒ B)) → Val → Set where

-- as I go through, we need to check if these are okay
-- also need to consider whether it's worth making the cases disjoint
    coerce-pass-blame : ∀ {A B} {c : Cast (A ⇒ B)} {ℓ}
                      → blame ℓ ↝⟦ c ⟧↝ blame ℓ
    coerce-id : ∀ {u} → u ↝⟦ id ⟧↝ u


    coerce-proj-ok : ∀ {B ℓ u v} → ???
      → u ↝⟦ B ?? ℓ ⟧↝ u
    coerce-proj-fail : ∀ {B ℓ u v} → ???
      → u ↝⟦ B ?? ℓ ⟧↝ blame ℓ
    coerce-fun : ∀ {A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')}{u v} 
               → u ↝⟦ c ↣ d ⟧↝ v
    coerce-prod-fst : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')}{u v}
               → (nbv : ¬isBlame v)
               → (u↝v : u ↝⟦ c ⟧↝ v)
               → fst u ↝⟦ c `× d ⟧↝ fst v
    coerce-prod-snd : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')}{u v}
               → (nbv : ¬isBlame v)
               → (u↝v : u ↝⟦ d ⟧↝ v)
               → snd u ↝⟦ c `× d ⟧↝ snd v
    coerce-prod-fst-fail : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')}{u ℓ}
               → (u↝bl : u ↝⟦ c ⟧↝ blame ℓ)
               → fst u ↝⟦ c `× d ⟧↝ blame ℓ
    coerce-prod-snd-fail : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')}{u ℓ}
               → (u↝bl : u ↝⟦ d ⟧↝ blame ℓ)
               → snd u ↝⟦ c `× d ⟧↝ blame ℓ
    coerce-sum-inl : ∀ {A B A' B'}{c : Cast (A ⇒ A')}{d : Cast (B ⇒ B')}{U V}
               → 
               → inl U ↝⟦ c `+ d ⟧↝ inl V
    coerce-fail : ∀ {A B ℓ u} → u ↝⟦ ⊥ A ⟨ ℓ ⟩ B ⟧↝ blame ℓ
-}

{-

      fst-cast : ∀ {A B C D} {V : Term} {c : Cast ((A `× B) ⇒ (C `× D))}
        → Value V → {x : Cross c} → {i : Inert c}
          -------------------------------------
        → fst (V ⟨ c ₍ i ₎⟩) —→ (fst V) ⟨ fstC c x ⟩

      applyCast M Γ⊢M∶A v (B ?? ℓ) {a} with canonical⋆ Γ⊢M∶A v
      ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , ⟨ q , refl ⟩ ⟩ ⟩ ⟩ ⟩ = M' ⟨ coerce A' B ℓ ⟩
      applyCast {A = A ⇒ B} {B = A' ⇒ B'} M Γ⊢M∶A v (c ↣ d) {a} = 
        ƛ A' ˙ ((rename suc M · ((` zero) ⟨ c ⟩)) ⟨ d ⟩)
      applyCast M Γ⊢M∶A v (c `× d) {a} = 
        ⟦ first M ⟨ c ⟩ , second M ⟨ d ⟩ ⟧
      applyCast {A = A `⊎ B} {B = A' `⊎ B'} M Γ⊢M∶A v (c `+ d) {a} =
        let L = inl ((` zero) ⟨ c ⟩) other B' in
        let R = inr ((` zero) ⟨ d ⟩) other A' in
            case M of A ⇒ L ∣ B ⇒ R
      applyCast M Γ⊢M∶A v (⊥ A ⟨ ℓ ⟩ B) {a} = mkblame B ℓ

-}

    {- 
    -- this case exists conceptually as blame-handling by a coercion,
           but is subsumed by coerce-ok because the cast technically succeeds here
      coerce-fail-↦ : ∀{A B A′ B′}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}{V w V′ w′}
      -- blame is produced in the body of the function itself
      → ⟦ V ∶ A ⟧₊ → ¬isBlame₊ V →
      → (V ↦ blame ℓ) ↝⟦ c ↣ d ⟧↝ V ↦ blame ℓ 
    -}

{- examples:

  (((λx∶Int.x) ⟨ℓ₁ ⋆ ⇒ Int ⟩) · True ⟨ℓ₂ ⋆ ⟩)

   (λz∶⋆.((λx∶Int.x) · (z⟨ℓ₁ Int⟩))) · True⟨ℓ₂ ⋆⟩

      c : Cast (⋆ ⇒ Int)
      d : Cast (Int ⇒ Int)
      c ↣ d : Cast ((Int ⇒ Int) ⇒ (⋆ ⇒ Int))
 
    true ↝⟦ c ⟧↝ blame ℓ₁
 ------------------------------------------
    V ↦ w ↝⟦ c ↣ d ⟧↝ true ↦ blame ℓ₁

    V ↝⟦ c ⟧↝ blame ℓ
 ------------------------------------------
    _ ↝⟦ c ↣ d ⟧↝ V ↦ blame ℓ


    42 ↝⟦ c ⟧↝ 42   w ↝⟦ d ⟧↝ w'
 ------------------------------------------
    42 ↦ w ↝⟦ c ↣ d ⟧↝ 42 ↦ w'


   ((λx∶⋆.42⟨ℓ₁ ⋆⟩) ⟨ℓ₂ ⋆ ⇒ Bool ⟩)

  we _do_ want to blame ℓ₂


   zero ↝⟦ c ⟧↝ zero   42 ↝⟦ d ⟧↝ blame ℓ₁
 ------------------------------------------
    zero ↦ 42 ↝⟦ c ↣ d ⟧↝ zero ↦ blame ℓ₁

    zero ↝⟦ c ⟧↝ zero     w 
---------------------------------------------

     coerce-fail-cod : ∀{A B A′ B′}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}{V w ℓ}
      
      → V ↝⟦ c ⟧₊↝ V   →   w ↝⟦ d ⟧↝ blame ℓ
      -- do we need a side-condition here where w is blameless? or where V is blameless?
      → (V ↦ w) ↝⟦ c ↣ d ⟧↝ blame ℓ       


   (λz∶⋆.((λx∶Int.x) · (z⟨ℓ₁ Int⟩)))

-}

  𝒞⟦_⟧ : ∀ {A B} → (c : Cast (A ⇒ B)) → 𝒫 Val → 𝒫 Val
  𝒞⟦_⟧ {A = A} c D v = Σ[ u ∈ Val ] u ∈ D × Σ[ u∶A ∈ ⟦ u ∶ A ⟧ ] u ↝⟦ c ∶ u∶A ⟧↝ v


  coerce-preserves-type-aux : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ u (u∶A : ⟦ u ∶ A ⟧) → ⟦ (coerce-val c u u∶A) ∶ B ⟧
  coerce-preserves-type-aux₊ : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ U (U∶A : ⟦ U ∶ A ⟧₊) → ⟦ (coerce-val₊ c U U∶A) ∶ B ⟧₊
  coerce-preserves-type-aux₊ c [] U∶A = tt
  coerce-preserves-type-aux₊ c (u ∷ U) ⟨ u∶A , U∶A ⟩ = 
    ⟨ coerce-preserves-type-aux c u u∶A , coerce-preserves-type-aux₊ c U U∶A ⟩
  coerce-preserves-type-aux id u u∶A = u∶A
  coerce-preserves-type-aux (_ !!) u u∶A = tt
  coerce-preserves-type-aux {A}{B} (_ ?? x) u u∶A with ⟦ u ∶ B ⟧?
  ... | yes u∶B = u∶B
  ... | no ¬u∶B = ⟦blame∶τ⟧ B
  coerce-preserves-type-aux {A ⇒ B} {A' ⇒ B'} (c ↣ d) (V ↦ u) u∶A with ⟦ V ∶ A ⟧₊?
  ... | yes V∶A = λ _ →  coerce-preserves-type-aux d u (u∶A V∶A)
  ... | no ¬V∶A = tt
  coerce-preserves-type-aux (c ↣ d) ν u∶A = tt
  coerce-preserves-type-aux (c ↣ d) (blame ℓ) u∶A = tt
  coerce-preserves-type-aux {A `× B}{A' `× B'}(c `× d) (fst u) u∶A = 
    fst-val-type A' B' (coerce-preserves-type-aux c u u∶A)
  coerce-preserves-type-aux {A `× B}{A' `× B'}(c `× d) (snd u) u∶A =
    snd-val-type A' B' (coerce-preserves-type-aux d u u∶A)
  coerce-preserves-type-aux (c `× d) (blame ℓ) u∶A = tt
  coerce-preserves-type-aux {A `⊎ B}{A' `⊎ B'}(c `+ d) (inl V) u∶A = 
    inl-val-type A' B' (coerce-preserves-type-aux₊ c V u∶A)
  coerce-preserves-type-aux {A `⊎ B}{A' `⊎ B'}(c `+ d) (inr V) u∶A = 
    inr-val-type A' B' (coerce-preserves-type-aux₊ d V u∶A)
  coerce-preserves-type-aux (c `+ d) (blame ℓ) u∶A = tt
  coerce-preserves-type-aux (⊥ A ⟨ ℓ ⟩ B) u u∶A = ⟦blame∶τ⟧ B


  coerce-preserves-type : ∀ {A B} (c : Cast (A ⇒ B)) u v
                 → (u∶A : ⟦ u ∶ A ⟧) → u ↝⟦ c ∶ u∶A ⟧↝ v → ⟦ v ∶ B ⟧
  coerce-preserves-type c u v u∶A refl = coerce-preserves-type-aux c u u∶A




  open import Denot.CastStructureRegular


  instance 
    dcs : DenotCastStruct
    dcs = record 
            { cast = cs
            ; _↝⟨_∶_⟩↝_ = _↝⟦_∶_⟧↝_ }


{-
  coerce-preserves-type : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ u v (u∶A : ⟦ u ∶ A ⟧) → u ↝⟦ c ∶ u∶A ⟧↝ v → ⟦ v ∶ B ⟧
  coerce-preserves-type id u v u∶A refl = u∶A
  coerce-preserves-type (_ !!) u v u∶A u↝v = tt
  coerce-preserves-type {A}{B} (B ?? ℓ) u v u∶A refl with ⟦ u ∶ B ⟧?
  ... | yes u∶B = u∶B
  ... | no ¬u∶B = ⟦blame∶τ⟧ B
  coerce-preserves-type {A ⇒ B}{A' ⇒ B'}(c ↣ d) (V ↦ u) .(coerce-val (c ↣ d) (V ↦ u) u∶A) u∶A refl 
    with ⟦ V ∶ A ⟧₊?
  ... | yes V∶A = λ _ → coerce-preserves-type d u (coerce-val d u (u∶A V∶A)) (u∶A V∶A) refl
  ... | no ¬V∶A = tt
  coerce-preserves-type (c ↣ d) ν .(coerce-val (c ↣ d) ν u∶A) u∶A refl = tt
  coerce-preserves-type (c ↣ d) (blame ℓ) .(coerce-val (c ↣ d) (blame ℓ) u∶A) u∶A refl = tt
  coerce-preserves-type (c `× d) (fst u) .(coerce-val (c `× d) (fst u) u∶A) u∶A refl
    with coerce-val c u u∶A | inspect (coerce-val c u) u∶A
  ... | blame ℓ | [ _ ] = tt
  ... | const k | [ eq ] = coerce-preserves-type c u (const k) u∶A (sym eq)
  ... | V ↦ v | [ eq ] = coerce-preserves-type c u (V ↦ v) u∶A (sym eq)
  ... | ν | [ eq ] = coerce-preserves-type c u ν u∶A (sym eq)
  ... | fst v | [ eq ] = coerce-preserves-type c u (fst v) u∶A (sym eq)
  ... | snd v | [ eq ] = coerce-preserves-type c u (snd v) u∶A (sym eq)
  ... | inl V | [ eq ] = coerce-preserves-type c u (inl V) u∶A (sym eq)
  ... | inr V | [ eq ] = coerce-preserves-type c u (inr V) u∶A (sym eq)
  coerce-preserves-type (c `× d) (snd u) .(coerce-val (c `× d) (snd u) u∶A) u∶A refl
    with coerce-val d u u∶A | inspect (coerce-val d u) u∶A
  ... | blame ℓ | [ _ ] = tt
  ... | const k | [ eq ] = coerce-preserves-type d u (const k) u∶A (sym eq)
  ... | V ↦ v | [ eq ] = coerce-preserves-type d u (V ↦ v) u∶A (sym eq)
  ... | ν | [ eq ] = coerce-preserves-type d u ν u∶A (sym eq)
  ... | fst v | [ eq ] = coerce-preserves-type d u (fst v) u∶A (sym eq)
  ... | snd v | [ eq ] = coerce-preserves-type d u (snd v) u∶A (sym eq)
  ... | inl V | [ eq ] = coerce-preserves-type d u (inl V) u∶A (sym eq)
  ... | inr V | [ eq ] = coerce-preserves-type d u (inr V) u∶A (sym eq)
  coerce-preserves-type (c `× d) (blame ℓ) .(coerce-val (c `× d) (blame ℓ) u∶A) u∶A refl = tt
  coerce-preserves-type (c `+ d) (inl V) .(coerce-val (c `+ d) (inl V) u∶A) u∶A refl
    with coerce-val₊ c V u∶A
  ... | inj₁ V' = {!   !}
  ... | inj₂ ℓ = tt
  coerce-preserves-type (c `+ d) (inr V) .(coerce-val (c `+ d) (inr V) u∶A) u∶A refl
    with coerce-val₊ d V u∶A
  ... | inj₁ V' = {!   !}
  ... | inj₂ ℓ = tt
  coerce-preserves-type (c `+ d) (blame ℓ) .(coerce-val (c `+ d) (blame ℓ) u∶A) u∶A refl = tt
  coerce-preserves-type {A}{B} (⊥ _ ⟨ x ⟩ _) u v u∶A refl = ⟦blame∶τ⟧ B
-}


{-




  -- ===========================================================================
 -- Classifying Coercions
-- ===========================================================================

{- inspired by : 
     data Progress (M : Term) : Set where
    step : ∀ {N : Term} → M —→ N → Progress M
    done : Value M → Progress M
    error : Error M → Progress M
-}
  {- if one value casts to another, u ↝⟦ c ⟧↝ v,
     where (c : Cast (A ⇒ B)) 
     then exactly one holds:
     + ∃ℓ. u ≡ v ≡ blame ℓ
     + ¬isBlame u and ⟦ u ∶ B ⟧ and v ≡ u
     + ¬isBlame u and ¬ ⟦ u ∶ B ⟧ and ∃ℓ. u ≡ blame ℓ  (or, more specifically, ∃ℓ ∈ get-label.'')
  -}

  get-blame-label : ∀ {A B} (c : Cast (A ⇒ B)) (v : Val)
    → ⟦ v ∶ A ⟧ → ¬ ⟦ v ∶ B ⟧ → List Label
  get-blame-label₊ : ∀ {A B} (c : Cast (A ⇒ B)) (V : List Val)
    → ⟦ V ∶ A ⟧₊ → ¬ ⟦ V ∶ B ⟧₊ → List Label
  get-blame-label₊ c [] V∶A ¬V∶B = ⊥-elim (¬V∶B tt)
  get-blame-label₊ {A}{B} c (v ∷ V) ⟨ v∶A , V∶A ⟩ ¬V∶B with ⟦ v ∶ B ⟧? | ⟦ V ∶ B ⟧₊?
  ... | yes v∶B | yes V∶B = ⊥-elim (¬V∶B ⟨ v∶B , V∶B ⟩) 
  ... | yes v∶B | no ¬V∶B = get-blame-label₊ c V V∶A ¬V∶B
  ... | no ¬v∶B | yes V∶B = get-blame-label c v v∶A ¬v∶B
  ... | no ¬v∶B | no ¬V∶B = get-blame-label c v v∶A ¬v∶B ++ get-blame-label₊ c V V∶A ¬V∶B
  get-blame-label {A} {.A} id v v∶A ¬v∶B = ⊥-elim (¬v∶B v∶A)
  get-blame-label {A} {.⋆} (.A !!) v v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {.⋆} {B} (.B ?? ℓ) v v∶A ¬v∶B = ℓ ∷ []
  get-blame-label {(A ⇒ B)} {(A' ⇒ B')} (c ↣ d) (V ↦ w) V∶A→w∶B ¬[V∶A'→w∶B']
    with ⟦ V ∶ A' ⟧₊?
  ... | no ¬V∶A' = ⊥-elim (¬[V∶A'→w∶B'] (λ z → ⊥-elim (¬V∶A' z)))
  ... | yes V∶A' with ⟦ w ∶ B' ⟧?
  ... | yes w∶B' = ⊥-elim (¬[V∶A'→w∶B'] (λ _ → w∶B'))
  ... | no ¬w∶B' with ⟦ V ∶ A ⟧₊?
  ... | yes V∶A = get-blame-label d w (V∶A→w∶B V∶A) (λ z → ¬[V∶A'→w∶B'] (λ _ → z))
  ... | no ¬V∶A = get-blame-label₊ c V V∶A' ¬V∶A
  get-blame-label {.(_ ⇒ _)} {.(_ ⇒ _)} (c ↣ d) ν v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {.(_ ⇒ _)} {.(_ ⇒ _)} (c ↣ d) (blame x) v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {.(_ `× _)} {.(_ `× _)} (c `× d) (fst v) v∶A ¬v∶B = 
    get-blame-label c v v∶A ¬v∶B
  get-blame-label {.(_ `× _)} {.(_ `× _)} (c `× d) (snd v) v∶A ¬v∶B = 
    get-blame-label d v v∶A ¬v∶B
  get-blame-label {.(_ `× _)} {.(_ `× _)} (c `× d) (blame x) v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {.(_ `⊎ _)} {.(_ `⊎ _)} (c `+ d) (inl V) V∶A ¬V∶B = 
    get-blame-label₊ c V V∶A ¬V∶B
  get-blame-label {.(_ `⊎ _)} {.(_ `⊎ _)} (c `+ d) (inr V) V∶A ¬V∶B = 
    get-blame-label₊ d V V∶A ¬V∶B
  get-blame-label {.(_ `⊎ _)} {.(_ `⊎ _)} (c `+ d) (blame x) v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {A} {B} (⊥ .A ⟨ ℓ ⟩ .B) v v∶A ¬v∶B = ℓ ∷ []


  data Coerce : ∀ {A B} → (c : Cast (A ⇒ B)) → (u : Val) → (v : Val) → Set where
    pass-value : ∀ {A B c u}
               → (u∶B : ⟦ u ∶ B ⟧) 
               → Coerce {A}{B} c u u
    new-blame : ∀ {A B c u ℓ}
               → (u∶A : ⟦ u ∶ A ⟧)
               → (¬u∶B : ¬ ⟦ u ∶ B ⟧)
               → (ℓ∈ : ℓ ∈ mem (get-blame-label c u u∶A ¬u∶B))
               → Coerce {A}{B} c u (blame ℓ)
    dom-blame : ∀{A B A′ B′}{c : Cast (A′ ⇒ A)}{d : Cast (B ⇒ B′)}{V v ℓ u}
               → (v∈ : v ∈ mem V) → (nbV : ¬isBlame₊ V) → (cfail : Coerce c v (blame ℓ)) 
               → Coerce {A ⇒ B}{A′ ⇒ B′} (c ↣ d) u (V ↦ blame ℓ)
    const-blame : ∀ {A B v ℓ} → Coerce (⊥ A ⟨ ℓ ⟩ B) v (blame ℓ)

  classify-coercion : ∀ {A}{B} {c : Cast (A ⇒ B)} {u v} → ⟦ u ∶ A ⟧ → u ↝⟦ c ⟧↝ v → Coerce c u v
  classify-coercion u∶A (coerce-ok u∶B) = pass-value u∶B
  classify-coercion u∶A (coerce-fail-proj ¬⋆ ¬v∶B) = new-blame tt ¬v∶B (here refl)
  classify-coercion {A ⇒ B}{A' ⇒ B'} {c = c ↣ d} u∶A (coerce-fail-cod {V = V}{w = w}{ℓ = ℓ} V∶A' V∶A nbV nbw u↝v) 
    with classify-coercion (u∶A V∶A) u↝v
  ... | pass-value u∶B = ⊥-elim (nbw tt)
  ... | const-blame = new-blame u∶A (λ z → {! z V∶A'   !}) {!   !}
  ... | new-blame u∶A ¬u∶B ℓ∈ = new-blame (λ z → u∶A) (λ z → ¬u∶B (z V∶A')) ℓ∈'
     where
     ℓ∈' : ℓ ∈ mem (get-blame-label (c ↣ d) (V ↦ w) (λ z → u∶A) (λ z → ¬u∶B (z V∶A')))
     ℓ∈' with ⟦ V ∶ A' ⟧₊? 
     ... | no ¬V∶A'' = ⊥-elim (¬V∶A'' V∶A')
     ... | yes V∶A'' with ⟦ w ∶ B' ⟧?
     ... | yes w∶B' = ⊥-elim (¬u∶B w∶B')
     ... | no ¬w∶B' with ⟦ V ∶ A ⟧₊?
     ... | no ¬V∶A = ⊥-elim (¬V∶A V∶A)
     ... | yes V∶Aagain = ℓ∈
  classify-coercion u∶A (coerce-fail-dom v∈ u↝v nbV) = dom-blame v∈ nbV (classify-coercion {!   !} u↝v)
  classify-coercion u∶A (coerce-fail-fst u↝v nbv) 
    with classify-coercion u∶A u↝v
  ... | pass-value u∶B = ⊥-elim (nbv tt)
  ... | new-blame u∶A ¬u∶B x = new-blame u∶A ¬u∶B x
  classify-coercion u∶A (coerce-fail-snd u↝v nbv)
    with classify-coercion u∶A u↝v
  ... | pass-value u∶B = ⊥-elim (nbv tt)
  ... | new-blame u∶A ¬u∶B ℓ∈ = new-blame u∶A ¬u∶B ℓ∈
  classify-coercion u∶A (coerce-fail-inl {v = v} v∈ nbv v↝bl) 
    with classify-coercion (⟦∶⟧₊→∈ u∶A v v∈) v↝bl
  ... | pass-value u∶B = ⊥-elim (nbv tt)
  ... | new-blame v∶A ¬v∶B ℓ∈ = new-blame u∶A (λ z → ¬v∶B (⟦∶⟧₊→∈ z v v∈)) {! ℓ∈  !}
  classify-coercion u∶A (coerce-fail-inr {v = v} v∈ nbv v↝bl)
    with classify-coercion ((⟦∶⟧₊→∈ u∶A v v∈)) v↝bl
  ... | pass-value u∶B = ⊥-elim (nbv tt)
  ... | new-blame v∶A ¬v∶B ℓ∈ = new-blame u∶A (λ z → ¬v∶B (⟦∶⟧₊→∈ z v v∈)) {! ℓ∈  !}
  classify-coercion u∶A coerce-fail = new-blame u∶A {!   !} {!   !}

  {- if one value casts to another, u ↝⟦ c ⟧↝ v,
     where (c : Cast (A ⇒ B)) 
     then exactly one holds:
     + ∃ℓ. u ≡ v ≡ blame ℓ
     + ¬isBlame u and ⟦ u ∶ B ⟧ and v ≡ u
     + ¬isBlame u and ¬ ⟦ u ∶ B ⟧ and ∃ℓ. u ≡ blame ℓ  (or, more specifically, ∃ℓ ∈ get-label.'')
  -}

  coerce-fun : ∀ {A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')}{V V' w w'} 
     → (mem V) ⊆ 𝒞⟦ c ⟧ (mem V')
     → w ↝⟦ d ⟧↝ w'
     → V ↦ w ↝⟦ c ↣ d ⟧↝ V' ↦ w'
  coerce-fun {A}{B}{A'}{B'}{c}{d}{V}{V'}{w}{w'} V⊆ w↝w' 
    with ⟦ V' ∶ A ⟧₊?
  ... | no ¬V'∶A = {!   !} 
  ... | yes V'∶A with ⟦ w ∶ B' ⟧?
  ... | no ¬w∶B' = {!  !}
  ... | yes w∶B' = {!   !}
 



-}