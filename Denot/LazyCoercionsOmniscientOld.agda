open import Data.Nat
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

module Denot.LazyCoercionsOmniscient where

  open import Types
  open import Labels
  open import CastStructureABT
  open import LazyCoercionsABT
  open import Denot.Value
  open import SetsAsPredicates



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
    coerce-fun : ∀{v w v′ w′ : Value}{A B A′ B′ : Type}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}
      → v′ ↝⟦ c ⟧↝ v   →   w ↝⟦ d ⟧↝ w′
      → (v ↦ w) ↝⟦ c ↣ d ⟧↝ (v′ ↦ w′)


   coerce-fail-fst :  
       v ↝⟦ c ⟧↝ blame ℓ
       fst v ↝⟦ c `× d ⟧↝ blame ℓ


{-
| -2 ⟩
   proj Int L1 `× proj Int L2

⟨ true | 
   proj Int L1 `× proj Int L2
-}


  𝒞⟦_⟧ : ∀ {A B} → (c : Cast (A ⇒ B)) → 𝒫 Val → 𝒫 Val
  𝒞⟦ c ⟧ D v = Σ[ u ∈ Val ] u ∈ D × u ↝⟦ c ⟧↝ v


  omni-preserves-type : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ u v → u ↝⟦ c ⟧↝ v → ⟦ u ∶ A ⟧ → ⟦ v ∶ B ⟧
  omni-preserves-type₊ : ∀ {A B} (c : Cast (A ⇒ B))
           → ∀ U V → U ↝⟦ c ⟧₊↝ V → ⟦ U ∶ A ⟧₊ → ⟦ V ∶ B ⟧₊
  omni-preserves-type₊ c .[] .[] [] V∶A = tt
  omni-preserves-type₊ c (u ∷ U) (v ∷ V) (x ∷ U↝V) ⟨ u∶A , U∶A ⟩ = 
    ⟨ omni-preserves-type c u v x u∶A , omni-preserves-type₊ c U V U↝V U∶A ⟩
  omni-preserves-type c u .u (coerce-ok x) u∶A = x
  omni-preserves-type {B = B} c u .(Val.blame _) (coerce-fail v∶A ¬v∶B x) u∶A = ⟦blame∶τ⟧ B


  open import Denot.CastStructure


  instance 
    dcs : DenotCastStruct
    dcs = record 
            { cast = cs
            ; _↝⟨_⟩↝_ = _↝⟦_⟧↝_ }
