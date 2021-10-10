open import Data.Nat
open import Data.Bool
open import Data.List
open import Relation.Nullary using (¬_; Dec; yes; no; recompute)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
    using (_≡_;_≢_; refl; trans; sym; cong)
open import Data.Product
    using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Types
open import Labels
open import Utils

module LambdaBGG where

open import LambdaB
open import ParamCCPrecisionABT pcs

ground-inert : ∀ {A G} {ℓ}
  → (A~G : A ~ G)
  → A ≢ ⋆ → ¬ Ground A
  → Ground G
  → Inert (cast A G ℓ A~G)
ground-inert {⋆} A~G A-nd A-ng g = contradiction refl A-nd
ground-inert {` ι} A~G A-nd A-ng g = contradiction G-Base A-ng
ground-inert {A₁ ⇒ A₂} (fun~ _ _) _ _ G-Fun = I-fun _
ground-inert {A₁ `× A₂} (pair~ _ _) _ _ G-Pair = I-pair _
ground-inert {A₁ `⊎ A₂} (sum~ _ _) _ _ G-Sum = I-sum _

applyCast-catchup-proj-ground : ∀ {A′ G} {V V′} {c : Cast (⋆ ⇒ G)}
  → (g : Ground G)
  → (⊢V : [] ⊢ V ⦂ ⋆) → [] ⊢ V′ ⦂ A′
  → (v : Value V) → Value V′
  → G ⊑ A′
  → [] , [] ⊢ V ⊑ V′
    ----------------------------------------------------------
  → ∃[ W ] Value W × (applyCast V ⊢V v c {A-proj c (ground-nd g)} —↠ W) × [] , [] ⊢ W ⊑ V′
applyCast-catchup-proj-ground {A′} {G} g ⊢V ⊢V′ v v′ G⊑A′ V⊑V′
  with ground? G
... | yes g
  with canonical⋆ ⊢V v
...   | ⟨ H , ⟨ V₁ , ⟨ c₁ , ⟨ i , ⟨ ⊢V₁ , refl ⟩ ⟩ ⟩ ⟩ ⟩
  with gnd-eq? H G {inert-ground c₁ i} {g}
...     | yes refl = {!!}
...     | no neq with V⊑V′
{- NOTE : We have no side condition to discriminate these cases. -}
...       | ⊑-wrap _ _ _ = {!!}
...       | ⊑-wrapl _ _ _ _ = {!!}
...       | ⊑-wrapr _ _ _ _ = {!!}
applyCast-catchup-proj-ground g ⊢V ⊢V′ v v′ G⊑A′ V⊑V′ | no ng = contradiction g ng

applyCast-catchup-proj : ∀ {A′ B} {V V′} {c : Cast (⋆ ⇒ B)}
  → (nd : B ≢ ⋆)
  → (⊢V : [] ⊢ V ⦂ ⋆) → [] ⊢ V′ ⦂ A′
  → (v : Value V) → Value V′
  → B ⊑ A′
  → [] , [] ⊢ V ⊑ V′
    ----------------------------------------------------------
  → ∃[ W ] Value W × (applyCast V ⊢V v c {A-proj c nd} —↠ W) × [] , [] ⊢ W ⊑ V′
applyCast-catchup-proj {B = B} {c = c} nd ⊢V ⊢V′ v v′ B⊑A′ V⊑V′
  with ground? B
... | yes g = applyCast-catchup-proj-ground {c = c} g ⊢V ⊢V′ v v′ B⊑A′ V⊑V′
... | no ng = {!!}

applyCast-catchup : ∀ {A A′ B} {V V′} {c : Cast (A ⇒ B)}
  → (a : Active c)
  → (⊢V : [] ⊢ V ⦂ A) → [] ⊢ V′ ⦂ A′
  → (v : Value V) → Value V′
  → A ⊑ A′ → B ⊑ A′
  → [] , [] ⊢ V ⊑ V′
    -----------------------------------------------------------------
  → ∃[ W ] Value W × (applyCast V ⊢V v c {a} —↠ W) × [] , [] ⊢ W ⊑ V′
applyCast-catchup (A-id _) ⊢V ⊢V′ v v′ A⊑A′ B⊑A′ V⊑V′ =
  ⟨ _ , ⟨ v , ⟨ _ ∎ , V⊑V′ ⟩ ⟩ ⟩
applyCast-catchup {V = V} (A-inj (cast A ⋆ ℓ _) A-ng† A-nd†) ⊢V ⊢V′ v v′ A⊑A′ unk⊑ V⊑V′
  with ground A {A-nd†}
... | ⟨ G , ⟨ g , A~G ⟩ ⟩ =
  ⟨ (V ⟨ cast A G ℓ A~G ₍ i ₎⟩) ⟨ cast G ⋆ ℓ unk~R ₍ I-inj g _ ₎⟩ ,
    ⟨ V-wrap (V-wrap v i) (I-inj g _) ,
      ⟨ _ —→⟨ ξ {F = F-cast _} (⊢cast _ ⊢V 𝐶⊢-cast) (wrap v {i}) ⟩
        _ —→⟨ wrap (V-wrap v i) {I-inj g _} ⟩
        _ ∎ ,
        ⊑-wrapl G⊑A′ unk⊑ ⊢V′ (⊑-wrapl A⊑A′ G⊑A′ ⊢V′ V⊑V′) ⟩ ⟩ ⟩
  where
  A-nd = recompute (dec-neg (eq-unk A)) A-nd†
  A-ng = recompute (dec-neg (ground? A)) A-ng†
  G⊑A′ = ⊑-ground-relax g A⊑A′ A~G A-nd
  i : Inert (cast A G ℓ A~G)
  i = ground-inert A~G A-nd A-ng g
applyCast-catchup (A-proj (cast ⋆ B ℓ _) B-nd) ⊢V ⊢V′ v v′ unk⊑ B⊑A′ V⊑V′ =
  {!!}
