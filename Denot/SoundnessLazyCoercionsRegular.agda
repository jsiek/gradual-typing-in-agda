{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to p⊤; tt to ptt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; lookup; length)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong-app)
open import Level using (Lift; lift; lower)

open import Denot.LazyCoercionsRegular as LDC
open import PreCastStructure
open import CastStructureABT
open import Denot.CastStructureRegular
open import SetsAsPredicates
open import LazyCoercionsABT
open import Types
open import Labels
open import Denot.Value
open import Denot.OpRegular
open import Syntax hiding (id)

module Denot.SoundnessLazyCoercionsRegular where

  open DenotCastStruct LDC.dcs using (⟦_⟧)


{-
  --   ⊢lit : ∀ {Γ A} {r : rep A} {p : Prim A}
  --       ------------------
  --     → Γ ⊢ $ r # p ⦂ A

𝑃⊢ (op-lit {A₁} r p) []ᵥ tt A = A ≡ A₁

-}

  _⟶_ = _—→_
  
  ⟦_`∶_⟧ : (ℕ → 𝒫 Val) → List Type → Set
  ⟦ ρ `∶ Γ ⟧ = ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧

  ⟦⟧-typesound : ∀ {Γ A} M ρ 
     → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧)
     → (Γ⊢M∶A : Γ ⊢ M ⦂ A)
     -------------------------------
     → ∀ d → d ∈ ⟦ M ⟧ ρ → ⟦ d ∶ A ⟧
  ⟦⟧-typesound₊ : ∀ {Γ A} M ρ 
     → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧)
     → (Γ⊢M∶A : Γ ⊢ M ⦂ A)
     -------------------------------
     → ∀ V → mem V ⊆ ⟦ M ⟧ ρ → ⟦ V ∶ A ⟧₊
  ⟦⟧-typesound₊ M ρ ρ∶Γ Γ⊢M∶A [] V⊆ = tt
  ⟦⟧-typesound₊ M ρ ρ∶Γ Γ⊢M∶A (v ∷ V) V⊆ = 
    ⟨ ⟦⟧-typesound M ρ ρ∶Γ Γ⊢M∶A v (V⊆ v (here refl)) 
    , ⟦⟧-typesound₊ M ρ ρ∶Γ Γ⊢M∶A V (λ d z → V⊆ d (there z)) ⟩
  ⟦⟧-typesound {Γ} {A} (` i) ρ ρ∶Γ (var-p x refl) d d∈⟦M⟧ = ρ∶Γ i d d∈⟦M⟧ x
  ⟦⟧-typesound {Γ} .{A ⇒ _} (ƛ .A ˙ N) ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) ν Λ-ν = tt
  ⟦⟧-typesound {Γ} .{A ⇒ _} (ƛ .A ˙ N) ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (V ↦ w) (Λ-↦ w∈⟦N⟧V V∶A nbV neV) V∶A' = 
    ⟦⟧-typesound N (mem V • ρ) (λ {zero → λ v v∈ → λ {refl → ⟦∶⟧₊→∈ V∶A v v∈} ; (suc i) → ρ∶Γ i}) ⊢N w w∈⟦N⟧V
  ⟦⟧-typesound {Γ} {A} (M · N) ρ ρ∶Γ (⊢· ⊢M ⊢N refl) d (∗-app {V = V} nbM nbN V↦d∈⟦M⟧ V⊆⟦N⟧) =
    ⟦⟧-typesound M ρ ρ∶Γ ⊢M (V ↦ d) V↦d∈⟦M⟧ (⟦⟧-typesound₊ N ρ ρ∶Γ ⊢N V V⊆⟦N⟧)
  ⟦⟧-typesound {Γ} {A} (M · N) ρ ρ∶Γ (⊢· ⊢M ⊢N refl) (blame ℓ) (∗-blame-rator bℓ∈) = ⟦blame∶τ⟧ A
  ⟦⟧-typesound {Γ} {A} (M · N) ρ ρ∶Γ (⊢· ⊢M ⊢N refl) (blame ℓ) (∗-blame-rand nbM bℓ∈) = ⟦blame∶τ⟧ A
  ⟦⟧-typesound {Γ} {A} ($ f # P) ρ ρ∶Γ (⊢$ f P refl) = ℘-typing A P f
  ⟦⟧-typesound {Γ} {A} (if L then M else N endif) ρ ρ∶Γ (⊢if ⊢L ⊢M ⊢N ⟨ ⟨ refl , refl ⟩ , refl ⟩) d (If-then nbL true∈ d∈⟦M⟧) = ⟦⟧-typesound M ρ ρ∶Γ ⊢M d d∈⟦M⟧
  ⟦⟧-typesound {Γ} {A} (if L then M else N endif) ρ ρ∶Γ (⊢if ⊢L ⊢M ⊢N ⟨ ⟨ refl , refl ⟩ , refl ⟩) d (If-else nbL false∈ d∈⟦N⟧) = ⟦⟧-typesound N ρ ρ∶Γ ⊢N d d∈⟦N⟧
  ⟦⟧-typesound {Γ} {A} (if L then M else N endif) ρ ρ∶Γ (⊢if ⊢L ⊢M ⊢N ⟨ ⟨ refl , refl ⟩ , refl ⟩) (blame ℓ) (If-blame bℓ∈⟦L⟧) = ⟦blame∶τ⟧ A
  ⟦⟧-typesound {Γ} .{_ `× _} (⟦ M , N ⟧) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) (fst d) (pair-fst nbM nbN d∈ v∈) = ⟦⟧-typesound M ρ ρ∶Γ ⊢M d d∈
  ⟦⟧-typesound {Γ} .{_ `× _} (⟦ M , N ⟧) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) (snd d) (pair-snd nbM nbN u∈ d∈) = ⟦⟧-typesound N ρ ρ∶Γ ⊢N d d∈
  ⟦⟧-typesound {Γ} .{_ `× _} (⟦ M , N ⟧) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) (blame ℓ) (pair-blame-fst bℓ∈) = tt
  ⟦⟧-typesound {Γ} .{_ `× _} (⟦ M , N ⟧) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) (blame ℓ) (pair-blame-snd nbM bℓ∈) = tt
  ⟦⟧-typesound {Γ} {A} (first M) ρ ρ∶Γ (⊢fst ⊢M ⟨ _ , refl ⟩) d (car-fst nbM d∈) = ⟦⟧-typesound M ρ ρ∶Γ ⊢M (fst d) d∈
  ⟦⟧-typesound {Γ} {A} (first M) ρ ρ∶Γ (⊢fst ⊢M ⟨ _ , refl ⟩) (blame ℓ) (car-blame bℓ∈) = ⟦blame∶τ⟧ A
  ⟦⟧-typesound {Γ} {A} (second M) ρ ρ∶Γ (⊢snd ⊢M ⟨ _ , refl ⟩) d (cdr-snd nbM d∈) = ⟦⟧-typesound M ρ ρ∶Γ ⊢M (snd d) d∈
  ⟦⟧-typesound {Γ} {A} (second M) ρ ρ∶Γ (⊢snd ⊢M ⟨ _ , refl ⟩) (blame ℓ) (cdr-blame bℓ∈) = ⟦blame∶τ⟧ A
  ⟦⟧-typesound {Γ} .{_ `⊎ B} (inl M other B) ρ ρ∶Γ (⊢inl B ⊢M refl) (inl V) (inleft-inl nbM V⊆) = ⟦⟧-typesound₊ M ρ ρ∶Γ ⊢M V V⊆
  ⟦⟧-typesound {Γ} .{_ `⊎ B} (inl M other B) ρ ρ∶Γ (⊢inl B ⊢M refl) (blame ℓ) (inleft-blame bℓ∈) = tt
  ⟦⟧-typesound {Γ} .{A `⊎ _} (inr M other A) ρ ρ∶Γ (⊢inr A ⊢M refl) (inr V) (inright-inr nbM V⊆) = ⟦⟧-typesound₊ M ρ ρ∶Γ ⊢M V V⊆
  ⟦⟧-typesound {Γ} .{A `⊎ _} (inr M other A) ρ ρ∶Γ (⊢inr A ⊢M refl) (blame ℓ) (inright-blame bℓ∈) = tt
  ⟦⟧-typesound {Γ} {C} (case L of A ⇒ M ∣ B ⇒ N) ρ ρ∶Γ (⊢case A B ⊢L ⊢M ⊢N ⟨ ⟨ refl , refl ⟩ , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩) d (cond-inl {V = V} nbL V⊆ d∈⟦M⟧) = 
    ⟦⟧-typesound M (mem V • ρ) (λ {zero → λ d d∈V → λ {refl → ⟦∶⟧₊→∈ V∶A d d∈V} ; (suc i) → ρ∶Γ i}) ⊢M d d∈⟦M⟧
    where
    V∶A : ⟦ V ∶ A ⟧₊
    V∶A = ⟦⟧-typesound L ρ ρ∶Γ ⊢L (inl V) V⊆
  ⟦⟧-typesound {Γ} {C} (case L of A ⇒ M ∣ B ⇒ N) ρ ρ∶Γ (⊢case A B ⊢L ⊢M ⊢N ⟨ ⟨ refl , refl ⟩ , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩) d (cond-inr {V = V} nbL V⊆ d∈⟦N⟧) = 
    ⟦⟧-typesound N (mem V • ρ) (λ {zero → λ d d∈V → λ {refl → ⟦∶⟧₊→∈ V∶B d d∈V} ; (suc i) → ρ∶Γ i}) ⊢N d d∈⟦N⟧
    where
    V∶B : ⟦ V ∶ B ⟧₊
    V∶B = ⟦⟧-typesound L ρ ρ∶Γ ⊢L (inr V) V⊆
  ⟦⟧-typesound {Γ} {A} (case L of A₁ ⇒ M ∣ B ⇒ N) ρ ρ∶Γ (⊢case A₁ B ⊢L ⊢M ⊢N ⟨ ⟨ refl , refl ⟩ , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩) (blame ℓ) (cond-blame bℓ∈⟦L⟧) = ⟦blame∶τ⟧ A
  ⟦⟧-typesound {Γ} {A} (M ⟨ c ⟩) ρ ρ∶Γ (⊢cast c ⊢M ⟨ refl , refl ⟩) d ⟨ u , ⟨ u∈⟦M⟧ , ⟨ u∶A , u↝d ⟩ ⟩ ⟩ = coerce-preserves-type c u d u∶A u↝d
  ⟦⟧-typesound {Γ} {A} (M ⟨ c ₍ i ₎⟩) ρ ρ∶Γ (⊢wrap c i ⊢M ⟨ refl , refl ⟩) d ⟨ u , ⟨ u∈⟦M⟧ , ⟨ u∶A , u↝d ⟩ ⟩ ⟩ = coerce-preserves-type c u d u∶A u↝d
  ⟦⟧-typesound {Γ} {.A} (mkblame A ℓ) ρ ρ∶Γ (⊢blame A ℓ refl) (blame ℓ) refl = ⟦blame∶τ⟧ A


  ⟦⟧-coerce-sound-⊇ : ∀ V → (vV : Value V) → ∀ ρ {Γ A B}
                 → (ρ∶Γ : ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧)
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ 𝒞⟦ c ⟧ (⟦ V ⟧ ρ)
  ⟦⟧-coerce-sound-⊇ V vV ρ ρ∶Γ 

{-
  example-lemma-2 : ∀ {A B A' B'} {c : Cast (A' ⇒ A)} {d : Cast (B ⇒ B')} F
                → Λ A' (λ D → 𝒞⟦ d ⟧ ((Λ A F) ∗ (𝒞⟦ c ⟧ D))) ⊆ 𝒞⟦ c ↣ d ⟧ (Λ A F)
  example-lemma-2 F (V ↦ w) (Λ-↦ ⟨ u , ⟨ ∗-app {V = V'} V↦w∈ V⊆ nbV₁ , u↝w ⟩ ⟩ V∶A nbV neV) = 
    ⟨ V' ↦ u , ⟨ V↦w∈ , {!  u↝w !} ⟩ ⟩
  example-lemma-2 F (V ↦ w) (Λ-↦ ⟨ .(blame _) , ⟨ ∗-blame-rator bl∈ , u↝w ⟩ ⟩ V∶A nbV neV) = {!   !}
  example-lemma-2 F (V ↦ w) (Λ-↦ ⟨ .(blame _) , ⟨ ∗-blame-rand bl∈ , u↝w ⟩ ⟩ V∶A nbV neV) = {!   !}
  example-lemma-2 F .ν Λ-ν = ⟨ ν , ⟨ Λ-ν , coerce-ok tt ⟩ ⟩
  example-lemma-2 F .(blame _) (Λ-blame w∈ V∶A nbV neV) = {! w∈  !}

{-
  example-lemma : ∀ {A B A' B'} {c : Cast (A' ⇒ A)} {d : Cast (B ⇒ B')} F 
                → Λ A' (λ D → 𝒞⟦ d ⟧ (F (𝒞⟦ c ⟧ D))) ⊆ 𝒞⟦ c ↣ d ⟧ (Λ A F)
  example-lemma {c = c} F (V ↦ w) (Λ-↦ ⟨ u , ⟨ u∈ , u↝w ⟩ ⟩ V∶A' nbV neV) 
    = ⟨ V ↦ u , ⟨ Λ-↦ {!  u∈ !} {!   !} nbV neV , {!  !} ⟩ ⟩
  example-lemma {c = c} F (blame ℓ) (Λ-blame ⟨ u , ⟨ u∈ , u↝w ⟩ ⟩ V∶A' nbV neV) 
    = {! u∈  !}
  example-lemma F .ν Λ-ν = ⟨ ν , ⟨ Λ-ν , coerce-ok tt ⟩ ⟩


  example-lemma-2 : ∀ {A B A' B'} {c : Cast (A' ⇒ A)} {d : Cast (B ⇒ B')} F
                → Λ A' (λ D → 𝒞⟦ d ⟧ ((Λ A F) ∗ (𝒞⟦ c ⟧ D))) ⊆ 𝒞⟦ c ↣ d ⟧ (Λ A F)
  example-lemma-2 F (V ↦ w) (Λ-↦ ⟨ u , ⟨ ∗-app (Λ-↦ {V = V'} u∈ V∶A₁ nbV₂ neV₁) V⊆ nbV₁ , u↝w ⟩ ⟩ V∶A nbV neV)
    = ⟨ V' ↦ u , ⟨ Λ-↦ u∈ V∶A₁ nbV₁ neV₁ , coerce-fail-↦ {! V⊆   !} {!   !} ⟩ ⟩

  example-lemma-2 F (V ↦ .(blame _)) (Λ-↦ ⟨ .(blame _) , ⟨ ∗-blame-rator bl∈ , coerce-ok x ⟩ ⟩ V∶A nbV neV) = {!   !}
  example-lemma-2 {B' = B'} F (V ↦ .(blame _)) (Λ-↦ ⟨ .(blame _) , ⟨ ∗-blame-rator bl∈ , coerce-fail-proj ¬⋆ x ⟩ ⟩ V∶A nbV neV) = ⊥-elim (x (⟦blame∶τ⟧ B'))
  example-lemma-2 F (V ↦ .(blame _)) (Λ-↦ ⟨ .(blame _) , ⟨ ∗-blame-rator bl∈ , coerce-fail ⟩ ⟩ V∶A nbV neV) = 
    ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩
  example-lemma-2 F (V ↦ .(blame _)) (Λ-↦ ⟨ .(blame _) , ⟨ ∗-blame-rand bl∈ , coerce-ok x ⟩ ⟩ V∶A nbV neV) = {!   !}
  example-lemma-2 F (V ↦ .(blame _)) (Λ-↦ ⟨ .(blame _) , ⟨ ∗-blame-rand bl∈ , coerce-fail-proj ¬⋆ x ⟩ ⟩ V∶A nbV neV) = {!   !}
  example-lemma-2 F (V ↦ .(blame _)) (Λ-↦ ⟨ .(blame _) , ⟨ ∗-blame-rand bl∈ , coerce-fail ⟩ ⟩ V∶A nbV neV) = {!   !}
  example-lemma-2 F .ν Λ-ν = ⟨ ν , ⟨ Λ-ν , coerce-ok tt ⟩ ⟩
  example-lemma-2 F .(blame _) 
    (Λ-blame {V = V} ⟨ u , ⟨ ∗-app (Λ-↦ {V = V'} w∈ V∶A₁ nbV₂ neV₁) V⊆ nbV₁ , u↝w ⟩ ⟩ 
             V∶A nbV neV) = ⟨ V' ↦ u , ⟨ Λ-↦ w∈ V∶A₁ nbV₂ neV₁ , coerce-fail-cod (coerce-ok₊ V∶A₁) u↝w ⟩ ⟩
  example-lemma-2 F .(blame _) (Λ-blame ⟨ .(blame _) , ⟨ ∗-blame-rator bl∈ , u↝w ⟩ ⟩ V∶A nbV neV) = {!   !}
  example-lemma-2 F .(blame _) (Λ-blame ⟨ .(blame _) , ⟨ ∗-blame-rand bl∈ , u↝w ⟩ ⟩ V∶A nbV neV) = {!   !}
  example-lemma-2 F d d∈ = {!   !}

-}

  ⟦⟧-coerce-sound-⊇ : ∀ V → (vV : Value V) → ∀ ρ {Γ A B}
                 → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) → (Γ⊢V∶A : Γ ⊢ V ⦂ A) 
                 → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ 𝒞⟦ c ⟧ (⟦ V ⟧ ρ)
  ⟦⟧-coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} ν Λ-ν = 
    ⟨ ν , ⟨ Λ-ν , coerce-ok tt ⟩ ⟩
  ⟦⟧-coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ {Γ} {A ⇒ B} {A' ⇒ B'} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) 
    (c ↣ d) {a} (V ↦ w) (Λ-↦ ⟨ u , ⟨ u∈'ΛN⟨c⟩' , u↝w ⟩ ⟩ V∶A nbV neV) = {!   !}
  ⟦⟧-coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ {Γ} {A ⇒ B} {A' ⇒ B'} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) 
    (c ↣ d) {a} (blame ℓ) (Λ-blame bl∈ V∶A nbV neV) = {!   !}
  ⟦⟧-coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (⊥ ._ ⟨ ℓ ⟩ ._) {a} v v∈ = {! u↝v !}
  ⟦⟧-coerce-sound-⊇ ($ f # P) V-const ρ ρ∶Γ (⊢$ f P refl) c {a} d d∈ = {!   !}
  ⟦⟧-coerce-sound-⊇ (⟦ M , N ⟧) (V-pair vV vV₁) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) c {a} d d∈ = {!   !}
  ⟦⟧-coerce-sound-⊇ (inl M other B) (V-inl vV) ρ ρ∶Γ (⊢inl B ⊢M refl) c {a} d d∈ = {!   !}
  ⟦⟧-coerce-sound-⊇ (inr M other A) (V-inr vV) ρ ρ∶Γ (⊢inr  A ⊢M refl) c {a} d d∈ = {!   !}
  ⟦⟧-coerce-sound-⊇ (M ⟨ c₁ ₍ .i ₎⟩) (V-wrap vV i) ρ ρ∶Γ (⊢wrap c₁ i ⊢M ⟨ refl , refl ⟩) c {a} d d∈ = {!   !}

{-

  {- this is not true...  I have to wonder if we want related values, or 
     blameless values or what... -}

  ⟦⟧-coerce-sound-⊇ : ∀ V → (vV : Value V) → ∀ ρ {Γ A B}
                 → (ρ∶Γ : ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧)
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ 𝒞⟦ c ⟧ (⟦ V ⟧ ρ)
  ⟦⟧-coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} ν Λ-ν = 
    ⟨ ν , ⟨ Λ-ν , coerce-ok tt ⟩ ⟩
  ⟦⟧-coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ {Γ} {A ⇒ B} {A' ⇒ B'} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} (V ↦ w) 
    (Λ-↦ ⟨ u , ⟨ u∈'ΛN⟨c⟩' , coerce-fail q y z ⟩ ⟩ Vne) = 
    ⟨ V ↦ w , ⟨ Λ-↦ {!  !} Vne , coerce-ok (λ V∶A' → {!   !}) ⟩ ⟩ 
  ⟦⟧-coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ {Γ} {A ⇒ B} {A' ⇒ B'} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} (V ↦ w) 
    (Λ-↦ ⟨ .w , ⟨ w∈'ΛN⟨c⟩' , coerce-ok u∶B' ⟩ ⟩ Vne) = 
    ⟨ V ↦ w , ⟨ Λ-↦ {!  w∈'ΛN⟨c⟩' !} Vne , coerce-ok (λ V∶A' → {! ⟦⟧-typesound N (mem V • ρ) ? ⊢N w ? !}) ⟩ ⟩
  ⟦⟧-coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (⊥ ._ ⟨ ℓ ⟩ ._) {a} v v∈ = {! u↝v !}
  ⟦⟧-coerce-sound-⊇ ($ f # P) V-const ρ ρ∶Γ (⊢$ f P refl) c {a} d d∈ = {!   !}
  ⟦⟧-coerce-sound-⊇ (⟦ M , N ⟧) (V-pair vV vV₁) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) c {a} d d∈ = {!   !}
  ⟦⟧-coerce-sound-⊇ (inl M other B) (V-inl vV) ρ ρ∶Γ (⊢inl B ⊢M refl) c {a} d d∈ = {!   !}
  ⟦⟧-coerce-sound-⊇ (inr M other A) (V-inr vV) ρ ρ∶Γ (⊢inr  A ⊢M refl) c {a} d d∈ = {!   !}
  ⟦⟧-coerce-sound-⊇ (M ⟨ c₁ ₍ .i ₎⟩) (V-wrap vV i) ρ ρ∶Γ (⊢wrap c₁ i ⊢M ⟨ refl , refl ⟩) c {a} d d∈ = {!   !}

{-
  ⟦⟧-coerce-sound-⊆ : ∀ V → (vV : Value V) → ∀ ρ {Γ A B} 
                 → (ρ∶Γ : ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧)
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ∀ d → ¬ (isBlame d) → d ∈ 𝒞⟦ c ⟧ (⟦ V ⟧ ρ) → d ∈ ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ
  ⟦⟧-coerce-sound-⊆ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} v ¬bv ⟨ u , ⟨ u∈ , u↝v ⟩ ⟩ = {! u∈ !}
  ⟦⟧-coerce-sound-⊆ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (⊥ ._ ⟨ ℓ ⟩ ._) {a} v ¬bv ⟨ u , ⟨ u∈ , u↝v ⟩ ⟩ = {! u↝v !}
  ⟦⟧-coerce-sound-⊆ ($ f # P) V-const ρ ρ∶Γ (⊢$ f P refl) c {a} d ¬bd ⟨ u , ⟨ u∈ , u↝d ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ (⟦ M , N ⟧) (V-pair vV vV₁) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) c {a} d ¬bd ⟨ u , ⟨ u∈ , u↝d ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ (inl M other B) (V-inl vV) ρ ρ∶Γ (⊢inl B ⊢M refl) c {a} d ¬bd ⟨ u , ⟨ u∈ , u↝d ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ (inr M other A) (V-inr vV) ρ ρ∶Γ (⊢inr  A ⊢M refl) c {a} d ¬bd ⟨ u , ⟨ u∈ , u↝d ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ (M ⟨ c₁ ₍ .i ₎⟩) (V-wrap vV i) ρ ρ∶Γ (⊢wrap c₁ i ⊢M ⟨ refl , refl ⟩) c {a} d ¬bd ⟨ u , ⟨ u∈ , u↝d ⟩ ⟩ = {!   !}
-}
  

{-

  ⟦⟧-coerce-sound-⊆ : ∀ V → (vV : Value V) → ∀ ρ {Γ A B} 
                 → (ρ∶Γ : ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧)
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) → (c : Cast (A ⇒ B)) → {a : Active c}
                 → 𝒞⟦ c ⟧ (⟦ V ⟧ ρ) ⊆ ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A id {a} v ⟨ .v , ⟨ u∈ , coerce-ok x ⟩ ⟩ = u∈
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A id {a} .(blame _) ⟨ u , ⟨ u∈ , coerce-fail v∶A ¬v∶B x ⟩ ⟩ = ⊥-elim (¬v∶B v∶A)
  ⟦⟧-coerce-sound-⊆ V vV ρ {Γ} {.⋆} {B} ρ∶Γ Γ⊢V∶A (proj B ℓ {g = g}) {a} .(blame _) ⟨ u , ⟨ u∈ , coerce-fail tt ¬v∶B (here refl) ⟩ ⟩ 
    with canonical⋆ Γ⊢V∶A vV
  ... | ⟨ A' , ⟨ M' , ⟨ inj .A' , ⟨ I-inj {A'}{ga} , ⟨ M'∶A' , 𝐶⊢-blame ⟩ ⟩ ⟩ ⟩ ⟩
    with gnd-eq? A' B {ga} {g}
  ... | no neq = refl  -- this must be the case
  ... | yes refl with u∈
  ... | ⟨ .u , ⟨ u'∈⟦M'⟧ , coerce-ok tt ⟩ ⟩ = ⊥-elim (¬v∶B (⟦⟧-typesound M' ρ ρ∶Γ M'∶A' u u'∈⟦M'⟧))
  ... | ⟨ u' , ⟨ u'∈⟦M'⟧ , coerce-fail v∶A ¬v∶B₁ x ⟩ ⟩ = ⊥-elim (¬v∶B₁ tt)
  ⟦⟧-coerce-sound-⊆ V vV ρ {Γ} {.⋆} {B} ρ∶Γ Γ⊢V∶A (proj B ℓ {g = g}) {a} v ⟨ .v , ⟨ u∈ , coerce-ok v∶B ⟩ ⟩
    with canonical⋆ Γ⊢V∶A vV
  ... | ⟨ A' , ⟨ M' , ⟨ inj .A' , ⟨ I-inj {A'}{ga} , ⟨ M'∶A' , 𝐶⊢-blame ⟩ ⟩ ⟩ ⟩ ⟩ 
    with gnd-eq? A' B {ga} {g}
  ... | no neq with u∈
  ... | ⟨ .v , ⟨ v∈⟦M'⟧ , coerce-ok tt ⟩ ⟩ = {! !}
  ... | ⟨ u , ⟨ u∈⟦M'⟧ , coerce-fail v∶A ¬v∶B x₁ ⟩ ⟩ = ⊥-elim (¬v∶B tt)
  
     -- "want" v ≡ blame ℓ
     -- v ∶ B  {x}
     -- ¬ A' ≡ B {neq}
     -- ⟨ u , u∈M' , u↝v ⟩ {u∈}
     -- M' ∶ A'    {M'∶A'}
     -- so u : A'
     -- I think either v is u or v is blame ℓ (because u↝v by injection A')
     -- but it should be that v is u because u ∶ A' so injecting it should succeed
     -- 
  ⟦⟧-coerce-sound-⊆ V vV ρ {Γ} {.⋆} {B} ρ∶Γ Γ⊢V∶A (proj B ℓ {g = g}) {a} v ⟨ .v , ⟨ u∈ , coerce-ok x ⟩ ⟩ 
    | ⟨ A' , ⟨ M' , ⟨ inj .A' , ⟨ I-inj {A'}{ga} , ⟨ M'∶A' , 𝐶⊢-blame ⟩ ⟩ ⟩ ⟩ ⟩ | yes refl
    with u∈
  ... | ⟨ .v , ⟨ u∈⟦M'⟧ , coerce-ok x₁ ⟩ ⟩ = u∈⟦M'⟧
  ... | ⟨ u , ⟨ u∈⟦M'⟧ , coerce-fail v∶A ¬v∶B x₁ ⟩ ⟩ = ⊥-elim (¬v∶B tt)

    -- these two might be better solved by a product-eta lemma and a lemma about
    -- pair denotations always having both fst and snd parts.
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A (cpair c d) {a} (fst v) ⟨ .(fst v) , ⟨ u∈ , coerce-ok x ⟩ ⟩ = 
    pair-fst ⟨ v , ⟨ car-fst u∈ , coerce-ok x ⟩ ⟩ {!  !}
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A (cpair c d) {a} (snd v) ⟨ .(snd v) , ⟨ u∈ , coerce-ok x ⟩ ⟩ = 
    pair-snd {!   !} ⟨ v , ⟨ cdr-snd u∈ , coerce-ok x ⟩ ⟩
  ⟦⟧-coerce-sound-⊆ V vV ρ {B = B `× C} ρ∶Γ Γ⊢V∶A (cpair c d) {a} (blame x₁) ⟨ .(blame x₁) , ⟨ u∈ , coerce-ok x ⟩ ⟩ = 
    pair-blame-fst ⟨ blame x₁ , ⟨ car-blame u∈ , coerce-ok (⟦blame∶τ⟧ B) ⟩ ⟩
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A (cpair c d) {a} .(blame _) ⟨ u , ⟨ u∈ , coerce-fail v∶A ¬v∶B x ⟩ ⟩ = {!   !}
  -- I think I should get a lemma to handle these next two
   -- not sure if it's a helper for the omniscient semantics or if it's a mutually inductive
   -- thing with this proof
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A (csum c d) {a} (inl x₁) ⟨ .(inl x₁) , ⟨ u∈ , coerce-ok x ⟩ ⟩ = 
    cond-inl u∈ (inleft-inl {!   !})
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A (csum c d) {a} (inr x₁) ⟨ .(inr x₁) , ⟨ u∈ , coerce-ok x ⟩ ⟩ = 
    cond-inr u∈ (inright-inr {!   !})
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A (csum c d) {a} (blame x₁) ⟨ .(blame x₁) , ⟨ u∈ , coerce-ok x ⟩ ⟩ = 
    cond-blame u∈
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A (csum c d) {a} .(blame _) ⟨ u , ⟨ u∈ , coerce-fail v∶A ¬v∶B x ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢V∶A (cseq c d) {a} v ⟨ u , ⟨ u∈ , u↝v ⟩ ⟩ = {!   !}
  {- 
  ⟦⟧-coerce-sound-⊆ (op-lam x ⦅ cons (bind (ast N)) nil ⦆)
                    vV ρ Γ⊢M∶A c {a} v 
                    ⟨ vs ↦ w , ⟨ Λ-↦ w∈⟦N⟧vs•ρ ne-vs , u↝v ⟩ ⟩ = {! u↝v  !}
  ⟦⟧-coerce-sound-⊆ (op-lam x ⦅ cons (bind (ast N)) nil ⦆)
                    vV ρ Γ⊢M∶A c {a} v 
                    ⟨ ν , ⟨ Λ-ν , u↝v ⟩ ⟩ = {! u∈⟦V⟧  !}
  ⟦⟧-coerce-sound-⊆ (op-lit x x₁ ⦅ nil ⦆) 
                    vV ρ Γ⊢M∶A c {a} v 
                    ⟨ u , ⟨ u∈⟦V⟧ , u↝v ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ (op-cons ⦅ cons (ast M) (cons (ast N) nil) ⦆) 
                    vV ρ Γ⊢M∶A c {a} v 
                    ⟨ u , ⟨ u∈⟦V⟧ , u↝v ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ (op-inl x ⦅ cons (ast M) nil ⦆) 
                    vV ρ Γ⊢M∶A c {a} v ⟨ u , ⟨ u∈⟦V⟧ , u↝v ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ (op-inr x ⦅ cons (ast M) nil ⦆) 
                    vV ρ Γ⊢M∶A c {a} v ⟨ u , ⟨ u∈⟦V⟧ , u↝v ⟩ ⟩ = {!   !}
  ⟦⟧-coerce-sound-⊆ (op-wrap c₁ x ⦅ cons (ast M) nil ⦆) 
                    vV ρ Γ⊢M∶A c {a} v 
                    ⟨ u , ⟨ u∈⟦V⟧ , u↝v ⟩ ⟩ = {!   !}
  -}

  lemma : ∀ V → (vV : Value V) → ∀ ρ {Γ A B}
              → (ρ∶Γ : ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧)
              → (c : Cast (A ⇒ B)) → {a : Active c}→ (Γ⊢V∶A : Γ ⊢ V ⦂ A) 
              → ∀ d → d ∈ ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ 
              → Σ[ d' ∈ Val ] d' ∈ ⟦ V ⟧ ρ × Σ[ d'∶A ∈ ⟦ d' ∶ A ⟧ ]
                  ((⟦ d' ∶ B ⟧ × d ≡ d') 
                ⊎ (Σ[ ¬d'∶B ∈ ¬ ⟦ d' ∶ B ⟧ ] 
                   Σ[ ℓ ∈ Label ] ℓ ∈ mem (get-blame-label c d' d'∶A ¬d'∶B) × d ≡ blame ℓ
                                  × d ≡ blame ℓ))
  lemma V vV ρ ρ∶Γ id {a} Γ⊢V∶A d d∈ = 
    let d∶A = ⟦⟧-typesound V ρ ρ∶Γ Γ⊢V∶A d d∈ in ⟨ d , ⟨ d∈ , ⟨ d∶A , inj₁ ⟨ d∶A , refl ⟩ ⟩ ⟩ ⟩
  lemma V vV ρ ρ∶Γ (proj _ x) {a} Γ⊢V∶A d d∈ = {!   !}
  lemma V vV ρ {Γ}{A `× A'}{B `× B'} ρ∶Γ (cpair c c₁) {a} Γ⊢V∶A (fst d) 
    (pair-fst {v = v} ⟨ u , ⟨ u∈car , u↝d ⟩ ⟩ ⟨ v' , ⟨ v'∈cdr , v'↝v ⟩ ⟩) = 
     ⟨ fst u , ⟨ {!   !} , ⟨ {!   !} , inj₁ ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩
     -- since fst d ∈ pair, d is not blame
     -- since u↝d , d is not blame, then u is not blame, and u = d
     -- since u is not blame and u is in car, u is in car by car-fst, so fst u = fst d ∈ V
  lemma V vV ρ {Γ}{A}{B} ρ∶Γ (cpair c c₁) {a} Γ⊢V∶A (snd d) (pair-snd {u = u} ⟨ u' , ⟨ u'∈car , u'↝u ⟩ ⟩ ⟨ v , ⟨ v∈cdr , v↝d ⟩ ⟩) = 
    ⟨ snd v , ⟨ {!   !} , ⟨ {!   !} , inj₁ ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩
  lemma V vV ρ {Γ}{A}{B} ρ∶Γ (cpair c c₁) {a} Γ⊢V∶A (blame ℓ) (pair-blame-fst ⟨ d , ⟨ d∈car , d↝bℓ ⟩ ⟩) = {!   !}
     -- d ∈ car V , d steps to blame
     -- so either the step is coerce-ok/seq and d is blame and that same blame is in V
     -- or the step is coerce-fail, and 
  lemma V vV ρ {Γ}{A}{B} ρ∶Γ (cpair c c₁) {a} Γ⊢V∶A (blame ℓ) (pair-blame-snd ⟨ d , ⟨ d∈cdr , d↝bℓ ⟩ ⟩) = {!   !}
  lemma V vV ρ ρ∶Γ (csum c c₁) {a} Γ⊢V∶A d d∈ = {!   !}
  lemma V vV ρ ρ∶Γ (cseq c c₁) {a} Γ⊢V∶A d d∈ = {!   !}

  ⟦⟧-coerce-sound-⊇ : ∀ V → (vV : Value V) → ∀ ρ {Γ A B}
                 → (ρ∶Γ : ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧)
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ 𝒞⟦ c ⟧ (⟦ V ⟧ ρ)
  ⟦⟧-coerce-sound-⊇ V vV ρ {Γ}{A}{B} ρ∶Γ Γ⊢V∶A c {a} d d∈ = 
    ([ (λ d∈⟦V⟧ → ⟨ d , ⟨ d∈⟦V⟧ , coerce-ok {A}{B}{c}{d} d∶B ⟩ ⟩) 
    , (λ {⟨ d' , ⟨ d'∈ , ⟨ d'∶A , ⟨ ¬d'∶B , ⟨ ℓ , ⟨ ℓ∈ , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ 
              → ⟨ d' , ⟨ d'∈ , coerce-fail {A}{B}{c}{d'} d'∶A ¬d'∶B ℓ∈ ⟩ ⟩}) ] (keylemma d))
     where
     keylemma : ∀ d →
         d ∈ ⟦ V ⟧ ρ 
       ⊎ Σ[ d' ∈ Val ] d' ∈ ⟦ V ⟧ ρ × 
         Σ[ d'∶A ∈ ⟦ d' ∶ A ⟧ ] 
         Σ[ ¬d'∶B ∈ ¬ ⟦ d' ∶ B ⟧ ] 
         Σ[ ℓ ∈ Label ] ℓ ∈ mem (get-blame-label c d' d'∶A ¬d'∶B) × d ≡ blame ℓ
     keylemma = {!   !}
     d∶B : ⟦ d ∶ B ⟧
     d∶B = ⟦⟧-typesound (applyCast V Γ⊢V∶A vV c {a}) ρ ρ∶Γ (applyCast-wt Γ⊢V∶A vV a) d d∈

  ⟦⟧-coerce-sound : ∀ V → (vV : Value V) → ∀ ρ {Γ A B}
                 → (ρ∶Γ : ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧)
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) → (c : Cast (A ⇒ B)) → {a : Active c}
                 → 𝒞⟦ c ⟧ (⟦ V ⟧ ρ) ≃ ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ
  ⟦⟧-coerce-sound V vV ρ ρ∶Γ Γ⊢M∶A c {a} = 
    ⟨ ⟦⟧-coerce-sound-⊆ V vV ρ ρ∶Γ Γ⊢M∶A c {a} , ⟦⟧-coerce-sound-⊇ V vV ρ ρ∶Γ Γ⊢M∶A c {a} ⟩

{- ∀ {Γ A B} → (M : Term) → Γ ⊢ M ⦂ A → (Value M) → (c : Cast (A ⇒ B))
              → ∀ {a : Active c} → Term-}


{-
  ⟦⟧-sound : ∀ M N → M ⟶ N → ∀ ρ → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
  ⟦⟧-sound .(plug M F) .(plug N F) (ξ {A}{B}{M}{N}{F} ⊢M∶A M⟶N) ρ = {!   !}
  ⟦⟧-sound .(plug (mkblame A ℓ) F) .(mkblame B ℓ) (ξ-blame {A}{B}{F}{ℓ}) ρ = {!   !}
  ⟦⟧-sound .((ƛ A ˙ M) · N) .(M [ N ]) (β {A}{M}{N} vN) ρ = {!   !}
  ⟦⟧-sound .(($ f # F) · ($ k # A')) .($ f k # B') (δ {A}{B}{f}{k}{F}{A'}{B'}) ρ = {!   !}
  ⟦⟧-sound .(if ($ true # B) then M else N endif) .M (β-if-true {M}{N}{B}) ρ = {!   !}
  ⟦⟧-sound .(if ($ false # B) then M else N endif) .N (β-if-false {M}{N}{B}) ρ = {!   !}
  ⟦⟧-sound .(first (⟦ V , W ⟧)) .V (β-fst {V}{W} vV vW) ρ = {!   !}
  ⟦⟧-sound .(second (⟦ V , W ⟧)) .W (β-snd {V}{W} vV vW) ρ = {!   !}
  ⟦⟧-sound .(case (inl V other B) of A ⇒ M ∣ B ⇒ N) .(M [ V ]) (β-caseL {A}{B}{V}{M}{N} vV) ρ = {!   !}
  ⟦⟧-sound .(case (inr V other A) of A ⇒ M ∣ B ⇒ N) .(N [ V ]) (β-caseR {A}{B}{V}{M}{N} vV) ρ = {!   !}
  ⟦⟧-sound .(V ⟨ c ⟩) .(applyCast V ⊢V∶A vV c {a}) (cast {A}{B}{V}{c} ⊢V∶A vV {a}) ρ = ⟨ {!   !} , {!   !} ⟩
  ⟦⟧-sound .(V ⟨ c ⟩) .(V ⟨ c ₍ i ₎⟩) (wrap {A}{B}{V}{c} vV {i}) ρ = {!   !}
  ⟦⟧-sound .(V ⟨ c ₍ i ₎⟩ · W) .((V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩) (fun-cast {A}{B}{A'}{B'}{V}{W}{c} vV vW {x}{i}) ρ = {!   !}
  ⟦⟧-sound .(first (V ⟨ c ₍ i ₎⟩)) .((first V) ⟨ fstC c x ⟩) (fst-cast {A}{B}{A'}{B'}{V}{c} vV {x}{i}) ρ = {!   !}
  ⟦⟧-sound .(second (V ⟨ c ₍ i ₎⟩)) .((second V) ⟨ sndC c x ⟩) (snd-cast {A}{B}{A'}{B'}{V}{c} vV {x}{i}) ρ = {!   !}
  ⟦⟧-sound .(case (V ⟨ c ₍ i ₎⟩) of A' ⇒ M ∣ B' ⇒ N) 
          .(case V of A ⇒ (rename (ext ⇑) M [ ` 0 ⟨ inlC c x ⟩ ])
                     ∣ B ⇒ (rename (ext ⇑) N [ ` 0 ⟨ inrC c x ⟩ ])) 
          (case-cast {A}{B}{A'}{B'}{V}{M}{N}{c} vV {x}{i}) ρ = {!   !}

{-
data _—→_ : Term → Term → Set where



    case-cast : ∀ {A B C D} {V M N : Term} {c : Cast (A `⊎ B ⇒ C `⊎ D)}
      → Value V
      → {x : Cross c} → {i : Inert c}
        --------------------------------------------
      → case (V ⟨ c ₍ i ₎⟩) of C ⇒ M ∣ D ⇒ N
           —→
         case V of A ⇒ (rename (ext ⇑) M [ ` 0 ⟨ inlC c x ⟩ ])
                 ∣ B ⇒ (rename (ext ⇑) N [ ` 0 ⟨ inrC c x ⟩ ])


-}


  ⟦⟧-adequate : {!   !}
  ⟦⟧-adequate = {!   !}

  ⟦⟧-sound : ∀ M N → M ⟶ N → ∀ ρ → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
  ⟦⟧-sound .(plug M F) .(plug N F) (ξ {A}{B}{M}{N}{F} ⊢M∶A M⟶N) ρ = {!   !}
  ⟦⟧-sound .(plug (mkblame A ℓ) F) .(mkblame B ℓ) (ξ-blame {A}{B}{F}{ℓ}) ρ = {!   !}
  ⟦⟧-sound .((ƛ A ˙ M) · N) .(M [ N ]) (β {A}{M}{N} vN) ρ = {!   !}
  ⟦⟧-sound .(($ f # F) · ($ k # A')) .($ f k # B') (δ {A}{B}{f}{k}{F}{A'}{B'}) ρ = {!   !}
  ⟦⟧-sound .(if ($ true # B) then M else N endif) .M (β-if-true {M}{N}{B}) ρ = {!   !}
  ⟦⟧-sound .(if ($ false # B) then M else N endif) .N (β-if-false {M}{N}{B}) ρ = {!   !}
  ⟦⟧-sound .(first (⟦ V , W ⟧)) .V (β-fst {V}{W} vV vW) ρ = {!   !}
  ⟦⟧-sound .(second (⟦ V , W ⟧)) .W (β-snd {V}{W} vV vW) ρ = {!   !}
  ⟦⟧-sound .(case (inl V other B) of A ⇒ M ∣ B ⇒ N) .(M [ V ]) (β-caseL {A}{B}{V}{M}{N} vV) ρ = {!   !}
  ⟦⟧-sound .(case (inr V other A) of A ⇒ M ∣ B ⇒ N) .(N [ V ]) (β-caseR {A}{B}{V}{M}{N} vV) ρ = {!   !}
  ⟦⟧-sound .(V ⟨ c ⟩) .(applyCast V ⊢V∶A vV c {a}) (cast {A}{B}{V}{c} ⊢V∶A vV {a}) ρ = {!   !}
  ⟦⟧-sound .(V ⟨ c ⟩) .(V ⟨ c ₍ i ₎⟩) (wrap {A}{B}{V}{c} vV {i}) ρ = {!   !}
  ⟦⟧-sound .(V ⟨ c ₍ i ₎⟩ · W) .((V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩) (fun-cast {A}{B}{A'}{B'}{V}{W}{c} vV vW {x}{i}) ρ = {!   !}
  ⟦⟧-sound .(first (V ⟨ c ₍ i ₎⟩)) .((first V) ⟨ fstC c x ⟩) (fst-cast {A}{B}{A'}{B'}{V}{c} vV {x}{i}) ρ = {!   !}
  ⟦⟧-sound .(second (V ⟨ c ₍ i ₎⟩)) .((second V) ⟨ sndC c x ⟩) (snd-cast {A}{B}{A'}{B'}{V}{c} vV {x}{i}) ρ = {!   !}
  ⟦⟧-sound .(case (V ⟨ c ₍ i ₎⟩) of A' ⇒ M ∣ B' ⇒ N) 
          .(case V of A ⇒ (rename (ext ⇑) M [ ` 0 ⟨ inlC c x ⟩ ])
                     ∣ B ⇒ (rename (ext ⇑) N [ ` 0 ⟨ inrC c x ⟩ ])) 
          (case-cast {A}{B}{A'}{B'}{V}{M}{N}{c} vV {x}{i}) ρ = {!   !}

  ⟦⟧-adequate : {!   !}
  ⟦⟧-adequate = {!   !}

  {-
  soundness (for Regular)
  If M —→ N, then ⟦ M ⟧ = ⟦ N ⟧

  adequacy (for Regular)
  if ⟦ M ⟧ non-empty, then M —↠ V.


  soundness of regular wrt. omniscient
  ⟦ M ⟧ ⊆ ⟦ M ⟧
  -}

  -- for soundness of Omni w.r.t Denot should just need a lemma for coercions
  -- everything else should be monotonicity and managing environment invariants
  -- thus, it would be nice to handle this using a theorem over an arbitrary DenotCastStruct
  
{- need to rewrite this to be -}


{-
  soundDenotOmni : ∀ M ρ ρ' → (∀ i → ρ i ⊆ ρ' i) → ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ'
  soundDenotOmni (` i) ρ ρ' ρ⊆ = ρ⊆ i
  soundDenotOmni (op-lam A ⦅ cons (bind (ast N)) nil ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ 
    = lower (DenotCastStruct.𝕆-mono λC𝒪.dcs (op-lam A) 
        ⟨ (λ D → ⟦ N ⟧ (D • ρ)) , ptt ⟩ ⟨ ((λ D' → ⟦ N ⟧ (D' • ρ'))) , ptt ⟩ 
        ⟨ (λ D D' D⊆D' → lift (soundDenotOmni N (D • ρ) (D' • ρ') (λ {zero → D⊆D' ; (suc n) → ρ⊆ n}))) , ptt ⟩) 
            d d∈⟦M⟧
  soundDenotOmni (op-app ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-lit x₁ x₂ ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = d∈⟦M⟧
  soundDenotOmni (op-if ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-cons ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-fst ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-snd ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-inl x₁ ⦅ cons (ast M) nil ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-inr x₁ ⦅ cons  (ast M) nil ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-case x₁ x₂ ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = {!   !}
  soundDenotOmni (op-cast c ⦅ cons (ast M) nil ⦆) ρ ρ' ρ⊆ d ⟨ u , ⟨ u∈⟦M⟧ , u↝⟨c⟩↝d ⟩ ⟩ 
    = ⟨ u , ⟨ IHu , omni-coerce-⊆ c u d u↝⟨c⟩↝d ⟩ ⟩
    where
    IHu : u ∈ ⟦ M ⟧ ρ'
    IHu = soundDenotOmni M ρ ρ' ρ⊆ u u∈⟦M⟧
  soundDenotOmni (op-wrap c x₁ ⦅ cons (ast M) nil ⦆) = soundDenotOmni M
  soundDenotOmni (op-blame x₁ x₂ ⦅ x ⦆) ρ ρ' ρ⊆ d d∈⟦M⟧ = d∈⟦M⟧
-}


  omni-coerce-blame-sound : ∀ {A B} → (c : Cast (A ⇒ B)) 
    → ∀ u {ℓ} → ⟦ u ∶ A ⟧
    → u ↝⟨ c ⟩↝ blame ℓ → u ↝⟦ c ⟧↝ blame ℓ
  omni-coerce-blame-sound₊ : ∀ {A B} → (c : Cast (A ⇒ B))
    → ∀ U V V' → ⟦ U ∶ A ⟧₊
    → ∀ {ℓ}
    → U ↝⟨ c ⟩₊↝ V
    → U ↝⟦ c ⟧₊↝ V'
    → blame ℓ ∈ mem V
    → blame ℓ ∈ mem V'
  omni-coerce-blame-sound .id .(blame _) u∶A ⟦id⟧ = coerce-ok u∶A
  omni-coerce-blame-sound .(inj _) .(blame _) u∶A ⟦inj⟧ = coerce-ok tt
  omni-coerce-blame-sound {B = B} .(proj _ _) (blame ℓ) u∶A (⟦proj⟧-ok x) = coerce-ok (⟦blame∶τ⟧ B)
  omni-coerce-blame-sound .(proj _ _) u u∶A (⟦proj⟧-fail x) = 
    coerce-fail {!   !} {!   !} {!   !}
  omni-coerce-blame-sound .(cpair _ _) .(fst _) u∶A (⟦cpair⟧-fst-fail u↝blame) = 
    coerce-fail {!   !} {!   !} {!   !}
  omni-coerce-blame-sound .(cpair _ _) .(snd _) u∶A (⟦cpair⟧-snd-fail u↝blame) = 
    coerce-fail {!   !} {!   !} {!   !}
  omni-coerce-blame-sound .(csum _ _) .(inl _) u∶A (⟦csum⟧-inl-fail x x₁ x₂) = 
    coerce-fail {!   !} {!   !} {!   !}
  omni-coerce-blame-sound .(csum _ _) .(inr _) u∶A (⟦csum⟧-inr-fail x x₁ x₂) = 
    coerce-fail {!   !} {!   !} {!   !}
  omni-coerce-blame-sound (cseq c d) u u∶A (⟦cseq⟧ {v = v} u↝v v↝blame) = 
    𝒪seq {! omni-coerce-blame-sound c u u∶A u↝v !} {!   !}
  omni-coerce-blame-sound₊ c U V V' U∶A U↝V U↝V' b∈V = {!   !}

  adequate : {! ∀ v v' →   !}
  adequate = {!   !}

-}
-}

-}

-}