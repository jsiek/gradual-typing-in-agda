open import Data.Nat
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

module Denot.LazyCoercionsOmniscient where

  open import Types
  open import Labels
  open import CastStructureABT
  open import LazyCoercionsABT
  open import Denot.Value
  open import SetsAsPredicates


  infix 4 _↝⟦_⟧↝_

  data _↝⟦_∶_⟧↝_ : ∀ {A B} → Val → (c : Cast (A ⇒ B)) → Val → Set where
    coerce-ok : ∀ {A B}{c : Cast (A ⇒ B)}{v} 
      → ⟦ v ∶ B ⟧ 
      → v ↝⟦ c ⟧↝ v
        V ↦ blame ℓ
    coerce-ok : ∀ {A B}{c : Cast (A ⇒ B)}{v} 
      → ⟦ v ∶ A ⟧ → ⟦ v ∶ B ⟧ 
      → v ↝⟦ ⊥ A ⟨ ℓ ⟩ B "A inconsistent with B" ⟧↝ v
    coerce-fail-proj : ∀ {B}{v ℓ}
      (¬⋆ : B ≢  ⋆ ) → (¬v∶B : ¬ ⟦ v ∶ B ⟧) 
      → v ↝⟦ _??_ B ℓ {¬⋆} ⟧↝ blame ℓ
    coerce-fail-cod : ∀{A B A′ B′}{c : Cast (A′ ⇒ A)}{d : Cast (B ⇒ B′)}{V w ℓ}
      -- blame is produced by a failure of the codomain cast d
      → (V∶A' : ⟦ V ∶ A′ ⟧₊) → (V∶A : ⟦ V ∶ A ⟧₊) 
      → (nbV : ¬isBlame₊ V) → (nbw : ¬isBlame w) 
      → (w↝bl : w ↝⟦ d ⟧↝ blame ℓ)
      → (V ↦ w) ↝⟦ c ↣ d ⟧↝ blame ℓ
    coerce-fail-dom : ∀{A B A′ B′}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}{V v ℓ u}
      -- blame is produced by a failure of the domain cast c
         → (v∈ : v ∈ mem V) → (v↝bl : v ↝⟦ c ⟧↝ blame ℓ) → (nbV : ¬isBlame₊ V)
         → u ↝⟦ c ↣ d ⟧↝ V ↦ blame ℓ
    coerce-fail-fst : ∀ {A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}{v ℓ} 
      → (v↝bl : v ↝⟦ c ⟧↝ blame ℓ) → (nbv : ¬isBlame v)
      → fst v ↝⟦ c `× d ⟧↝ blame ℓ
    coerce-fail-snd : ∀ {A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}{v ℓ} 
      → (v↝bl : v ↝⟦ d ⟧↝ blame ℓ) → (nbv : ¬isBlame v)
      → snd v ↝⟦ c `× d ⟧↝ blame ℓ
    coerce-fail-inl : ∀ {A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}{V v ℓ} 
      → (v∈ : v ∈ mem V) → (nbv : ¬isBlame v) → (v↝bl : v ↝⟦ c ⟧↝ blame ℓ) 
      → inl V ↝⟦ c `+ d ⟧↝ blame ℓ
    coerce-fail-inr : ∀ {A B A' B'}{c : Cast (A ⇒ B)}{d : Cast (A' ⇒ B')}{V v ℓ} 
      → (v∈ : v ∈ mem V) → (nbv : ¬isBlame v) → (v↝bl : v ↝⟦ d ⟧↝ blame ℓ) 
      → inr V ↝⟦ c `+ d ⟧↝ blame ℓ
    coerce-fail : ∀ {A B ℓ v}
      → v ↝⟦ ⊥ A ⟨ ℓ ⟩ B ⟧↝ blame ℓ


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
  𝒞⟦ c ⟧ D v = Σ[ u ∈ Val ] u ∈ D × u ↝⟦ c ⟧↝ v


  omni-preserves-type : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ u v → u ↝⟦ c ⟧↝ v → ⟦ u ∶ A ⟧ → ⟦ v ∶ B ⟧
  omni-preserves-type {A} {B} c u .u (coerce-ok x) u∶A = x
  omni-preserves-type {.⋆} {B} .(B ?? _) u .(blame _) (coerce-fail-proj ¬⋆ x) u∶A = ⟦blame∶τ⟧ B
  omni-preserves-type {.(_ ⇒ _)} {.(_ ⇒ _)} .(_ ↣ _) .(_ ↦ _) .(blame _) (coerce-fail-cod V∶A' V∶A nbV nbw w↝bl) u∶A = tt
  omni-preserves-type {.(_ ⇒ _)} {A' ⇒ B'} .(_ ↣ _) d .(_ ↦ blame _) (coerce-fail-dom v∈ v↝bl nbV) u∶A _ = ⟦blame∶τ⟧ B'
  omni-preserves-type {.(_ `× _)} {.(_ `× _)} (_ `× _) .(fst _) .(blame _) (coerce-fail-fst u↝v nbv) u∶A = tt
  omni-preserves-type {.(_ `× _)} {.(_ `× _)} .(_ `× _) .(snd _) .(blame _) (coerce-fail-snd u↝v nbv) u∶A = tt
  omni-preserves-type {.(_ `⊎ _)} {.(_ `⊎ _)} .(_ `+ _) .(inl _) .(blame _) (coerce-fail-inl v∈ nbv v↝bl) u∶A = tt
  omni-preserves-type {.(_ `⊎ _)} {.(_ `⊎ _)} .(_ `+ _) .(inr _) .(blame _) (coerce-fail-inr v∈ nbv v↝bl) u∶A = tt
  omni-preserves-type {A} {B} .(⊥ A ⟨ _ ⟩ B) u .(blame _) coerce-fail u∶A = ⟦blame∶τ⟧ B


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
 

  open import Denot.CastStructure


  instance 
    dcs : DenotCastStruct
    dcs = record 
            { cast = cs
            ; _↝⟨_⟩↝_ = _↝⟦_⟧↝_ }
