{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

module Denot.GroundCoercionsOmniscient where

  open import Types
  open import Labels
  open import CastStructureABT
  open import GroundCoercionsABT
  open import Denot.Value
  open import SetsAsPredicates




  𝐺⟦_⟧ : (G : Type) → (g : Ground G) → Val → Set
  𝐺⟦ ` b ⟧ G-Base (const {b'} k) with base-eq? b b'
  ... | yes refl = True
  ... | no neq = False
  𝐺⟦ ` b ⟧ G-Base v = False
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun ν = True
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun (v ↦ w) = True
  𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun v = False
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair (Val.fst v) = True
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair (Val.snd v) = True
  𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair v = False
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum (inl v) = True
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum (inr v) = True
  𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum v = False

  


  {- could add a lemma that the list of blame labels is always nonempty -}
  {- could also add a lemma that the list is complete... all possible blames are here. -}
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
  get-blame-label {A} {.⋆} (inj .A) v v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {.⋆} {B} (proj .B ℓ) v v∶A ¬v∶B = (ℓ ∷ [])
  get-blame-label {(A ⇒ B)} {(A' ⇒ B')} (cfun c d) (V ↦ w) V∶A→w∶B ¬[V∶A'→w∶B'] 
    with ⟦ V ∶ A' ⟧₊?
  ... | no ¬V∶A' = ⊥-elim (¬[V∶A'→w∶B'] (λ z → ⊥-elim (¬V∶A' z)))
  ... | yes V∶A' with ⟦ w ∶ B' ⟧?
  ... | yes w∶B' = ⊥-elim (¬[V∶A'→w∶B'] (λ _ → w∶B'))
  ... | no ¬w∶B' with ⟦ V ∶ A ⟧₊?
  ... | yes V∶A = get-blame-label d w (V∶A→w∶B V∶A) (λ z → ¬[V∶A'→w∶B'] (λ _ → z))
  ... | no ¬V∶A = get-blame-label₊ c V V∶A' ¬V∶A
  get-blame-label {.(_ ⇒ _)} {.(_ ⇒ _)} (cfun c c₁) ν v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {.(_ ⇒ _)} {.(_ ⇒ _)} (cfun c c₁) (Val.blame x) v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {.(_ `× _)} {.(_ `× _)} (cpair c d) (Val.fst v) v∶A ¬v∶B = get-blame-label c v v∶A ¬v∶B
  get-blame-label {.(_ `× _)} {.(_ `× _)} (cpair c d) (Val.snd v) v∶A ¬v∶B = get-blame-label d v v∶A ¬v∶B
  get-blame-label {.(_ `× _)} {.(_ `× _)} (cpair c d) (Val.blame x) v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {.(_ `⊎ _)} {.(_ `⊎ _)} (csum c d) (inl x) v∶A ¬v∶B = get-blame-label₊ c x v∶A ¬v∶B
  get-blame-label {.(_ `⊎ _)} {.(_ `⊎ _)} (csum c d) (inr x) v∶A ¬v∶B = get-blame-label₊ d x v∶A ¬v∶B
  get-blame-label {.(_ `⊎ _)} {.(_ `⊎ _)} (csum c d) (Val.blame x) v∶A ¬v∶B = ⊥-elim (¬v∶B tt)
  get-blame-label {A} {C} (cseq {B = B} c d) v v∶A ¬v∶C with ⟦ v ∶ B ⟧?
  ... | yes v∶B = get-blame-label d v v∶B ¬v∶C
  ... | no ¬v∶B = get-blame-label c v v∶A ¬v∶B

  infix 4 _↝⟦_⟧↝_
  infix 4 _↝⟦_⟧₊↝_

  data _↝⟦_⟧↝_ : ∀ {A B} → Val → (c : Cast (A ⇒ B)) → Val → Set
  data _↝⟦_⟧₊↝_ : ∀ {A B} → List Val → (c : Cast (A ⇒ B)) → List Val → Set where
    [] : ∀ {A B}{c : Cast (A ⇒ B)} → [] ↝⟦ c ⟧₊↝ []
    _∷_ : ∀ {v V v' V'}{A B}{c : Cast (A ⇒ B)} 
        → v ↝⟦ c ⟧↝ v' → V ↝⟦ c ⟧₊↝ V'
        → (v ∷ V) ↝⟦ c ⟧₊↝ (v' ∷ V')
  data _↝⟦_⟧↝_ where
    coerce-ok : ∀ {A B}{c : Cast (A ⇒ B)}{v} 
      → ⟦ v ∶ B ⟧ → v ↝⟦ c ⟧↝ v
    coerce-fail : ∀ {A B}{c : Cast (A ⇒ B)}{v} 
      → (v∶A : ⟦ v ∶ A ⟧) (¬v∶B : ¬ ⟦ v ∶ B ⟧)
      → ∀ {ℓ} → ℓ ∈ mem (get-blame-label c v v∶A ¬v∶B) → v ↝⟦ c ⟧↝ Val.blame ℓ
    𝒪seq : ∀ {A B C} {c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}{u v w}
      → u ↝⟦ c ⟧↝ v → v ↝⟦ d ⟧↝ w
      → u ↝⟦ cseq c d ⟧↝ w

  𝒞⟦_⟧ : ∀ {A B} → (c : Cast (A ⇒ B)) → 𝒫 Val → 𝒫 Val
  𝒞⟦ c ⟧ D v = Σ[ u ∈ Val ] u ∈ D × u ↝⟦ c ⟧↝ v


{- V ↦ blame ℓ  ~>  V' ↦ blame ℓ -}
{-
what omniscient is supposed to look like
   - (((λ x∶Nat. λ y:Nat. true)⟨ ℓ1: Nat → (Nat → Bool) ⇒ ⋆ ⟩ ⟨ ℓ2: ⋆ ⇒ Nat → (Nat → Nat) ⟩) 3)
omniscient -> blame ℓ2

{-
casting a function 

application  (blame  ∗  something) -> blame

let f = {2 -> 3 -> blame 1};
    g = {f but with different labels 2};
   apply  f 2;
   apply  g 2 3;
   ... return 42

let f = {blame 1};
    g = {blame 2}
   apply  f 2;
   apply  g 2 3;
   ... return 42

-}


regular : produce values   like   3 ↦ blame ℓ2
                                  4 ↦ blame ℓ2

   - ((λx:Nat. if x==0 then 0 ⟨ℓ1: Nat ⇒ ⋆ ⟩ else true ⟨ℓ2: bool ⇒ ⋆ ⟩)⟨ℓ3: Nat → Nat ⟩  0)
   omniscient :  2 ↦ true ~> blame ℓ3, 0 ↦ 0 ~> 0 ↦ 0
   - soundness of regular wrt. omniscient

has-no-blame-at-all v →  v ∈ ⟦ M ⟧ → v ∈ 𝒪⟦ M ⟧
blame ℓ ∈ ⟦ M ⟧ → blame ℓ ∈ 𝒪⟦ M ⟧
3 ↦ blame ℓ2 ∈ ⟦ M ⟧   ...    blame ℓ2 ∈ 


-}

  omni-preserves-type : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ u v → u ↝⟦ c ⟧↝ v → ⟦ u ∶ A ⟧ → ⟦ v ∶ B ⟧
  omni-preserves-type₊ : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ U V → U ↝⟦ c ⟧₊↝ V → ⟦ U ∶ A ⟧₊ → ⟦ V ∶ B ⟧₊
  omni-preserves-type₊ c .[] .[] [] V∶A = tt
  omni-preserves-type₊ c (u ∷ U) (v ∷ V) (x ∷ U↝V) ⟨ u∶A , U∶A ⟩ = 
    ⟨ omni-preserves-type c u v x u∶A , omni-preserves-type₊ c U V U↝V U∶A ⟩
  omni-preserves-type c u .u (coerce-ok x) u∶A = x
  omni-preserves-type {B = B} c u .(Val.blame _) (coerce-fail v∶A ¬v∶B x) u∶A = ⟦blame∶τ⟧ B
  omni-preserves-type (cseq c d) u w (𝒪seq {v = v} u↝v v↝w) u∶A = 
    omni-preserves-type d v w v↝w (omni-preserves-type c u v u↝v u∶A)
 
 


{-
  infix 4 _↝⟨_⟩↝_
  infix 4 _↝⟪_⟫↝_

  ¬blame : Val → Set
  ¬blame (const x) = True
  ¬blame (x ↦ v) = True
  ¬blame ν = True
  ¬blame (fst v) = True
  ¬blame (snd v) = True
  ¬blame (inl x) = True
  ¬blame (inr x) = True
  ¬blame (blame x) = False
-}

  -- this is the right idea, but it isn't strictly positive
{-
  data _↝⟨_⟩↝_ : ∀ {A B} → Val → Cast (A ⇒ B) → Val → Set
  data _↝⟪_⟫↝_ : ∀ {A B} → (V : List Val) → (c : Cast (A ⇒ B)) → (V' : List Val) → Set where
    [] : ∀ {A B}{c : Cast (A ⇒ B)} → [] ↝⟪ c ⟫↝ []
    _∷_ : ∀ {A B}{c : Cast (A ⇒ B)}{v v' V V'} → v ↝⟨ c ⟩↝ v' → V ↝⟪ c ⟫↝ V' → (v ∷ V) ↝⟪ c ⟫↝ (v' ∷ V')
  data _↝⟨_⟩↝_ where
    ⟦id⟧ : ∀{v : Val}{A : Type}{a : Atomic A}
      → v ↝⟨ id{A}{a} ⟩↝ v
    ⟦inj⟧ : ∀{v : Val}{G : Type}{g : Ground G}
      → v ↝⟨ inj G {g} ⟩↝ v
    ⟦proj⟧-ok : ∀{v : Val}{G : Type}{g : Ground G}{ℓ : Labels.Label}
      → 𝐺⟦ G ⟧ g v
      → v ↝⟨ proj G ℓ {g} ⟩↝ v
    ⟦proj⟧-fail : ∀{v : Val}{G : Type}{g : Ground G}{ℓ : Labels.Label}
      → ¬ 𝐺⟦ G ⟧ g v
      → v ↝⟨ proj G ℓ {g} ⟩↝ blame ℓ
    ⟦cfun⟧ : ∀{V w V′ w′}{A B A′ B′ : Type}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}
      → V′ ↝⟪ c ⟫↝ V   →   w ↝⟨ d ⟩↝ w′
      → (V ↦ w) ↝⟨ cfun c d ⟩↝ (V′ ↦ w′)
    ⟦cfun⟧-fail-cod : ∀ {V w ℓ}{A B A′ B′}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}
      → (∀ V V' → V ↝⟪ c ⟫↝ V' → All ¬blame V)
      → w ↝⟨ d ⟩↝ blame ℓ
      → (V ↦ w) ↝⟨ cfun c d ⟩↝ blame ℓ
    ⟦cseq⟧ : ∀{u v w : Val}{A B C : Type}{c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}
      →   u ↝⟨ c ⟩↝ v    →   v ↝⟨ d ⟩↝ w
      → u ↝⟨ cseq c d ⟩↝ w
-}

  open import Denot.CastStructure

-- This won't typecheck; LazyCoercions and GroundCoercions are written
-- using CastStructureOrig instead of CasStructureABT

  instance 
    dcs : DenotCastStruct
    dcs = record 
            { cast = cs
            ; _↝⟨_⟩↝_ = _↝⟦_⟧↝_ }



{-
  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Val M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  {-
    V⟨id⟩    —→    V
   -}
  applyCast M v id {a} = M
  {-
    V⟨G!⟩⟨G?⟩    —→    V
    V⟨G!⟩⟨H?p⟩   —→   blame p  if G ≠ H
   -}
  applyCast M v (proj B ℓ {gb}) {a} with canonical⋆ M v
  ... | ⟨ G , ⟨ V , ⟨ c , ⟨ I-inj {G}{ga} , meq ⟩ ⟩ ⟩ ⟩
         rewrite meq
         with gnd-eq? G B {ga} {gb}
  ...    | no neq = blame ℓ
  ...    | yes eq
            with eq
  ...       | refl = V
  {-
   V⟨c ; d⟩     —→    V⟨c⟩⟨d⟩
   -}
  applyCast M v (cseq c d) = (M ⟨ c ⟩) ⟨ d ⟩
  applyCast M v (cpair c d) {a} = eta× M (cpair c d) C-pair
  applyCast M v (csum c d) {a} = eta⊎ M (csum c d) C-sum
  applyCast M v (cfun c d) {()}
  applyCast M v (inj A) {()}

-}