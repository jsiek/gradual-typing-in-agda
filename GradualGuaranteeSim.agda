module GradualGuaranteeSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂; inspect; [_])
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

-- We're using simple cast with inert cross cast - at least for now.
open import GroundInertX using (Cast; cast; Inert; Active; Cross; applyCast;
                                pcs; cs; dom; cod; fstC; sndC; inlC; inrC; compile; inert-ground)
open import Types
open import Variables
open import Labels

open import GTLC
import ParamCastCalculus
open ParamCastCalculus Cast Inert
import ParamCastAux
open ParamCastAux pcs
import ParamCastReduction
open ParamCastReduction cs
open import TermPrecision
open import GradualGuaranteeAux


pair-cast-is-cross : ∀ {A B C D} → (c : Cast ((A `× B) ⇒ (C `× D))) → Cross c
pair-cast-is-cross (cast (A `× B) (C `× D) ℓ _) = Cross.C-pair

sim-fst-cons-v : ∀ {A A′ B B′} {V : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A′} {W′ : ∅ ⊢ B′}
  → Value V → Value V′ → Value W′
  → ∅ , ∅ ⊢ V ⊑ᶜ cons V′ W′
    ------------------------------------------
  → ∃[ M ] ((fst V —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ V′))
sim-fst-cons-v (V-pair {V = V} {W} v w) v′ w′ (⊑ᶜ-cons lpV lpW) = ⟨ V , ⟨ _ —→⟨ β-fst v w ⟩ _ ∎ , lpV ⟩ ⟩
sim-fst-cons-v (V-wrap {V = V} {c} v (Inert.I-pair _)) v′ w′ (⊑ᶜ-wrapl (lpit-pair (pair⊑ lp₁₁ lp₁₂) (pair⊑ lp₂₁ lp₂₂)) lpV)
  with sim-fst-cons-v v v′ w′ lpV
... | ⟨ M , ⟨ rd* , lpM ⟩ ⟩ =
  let x = pair-cast-is-cross c in
    ⟨ M ⟨ fstC c x ⟩ , ⟨ _ —→⟨ fst-cast v {x} ⟩ plug-cong (F-cast (fstC c x)) rd* , ⊑ᶜ-castl lp₁₁ lp₂₁ lpM ⟩ ⟩

sim-fst-cons : ∀ {A A′ B B′} {N : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A′} {W′ : ∅ ⊢ B′}
  → Value V′ → Value W′
  → ∅ , ∅ ⊢ N ⊑ᶜ cons V′ W′
    ------------------------------------------
  → ∃[ M ] ((fst N —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ V′))
sim-fst-cons v′ w′ lpN
  -- first goes to fst V where V is value
  with catchup (V-pair v′ w′) lpN
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  -- then goes from there by `sim-fst-cons-v`
  with sim-fst-cons-v v v′ w′ lpV
...   | ⟨ M , ⟨ rd*₂ , lpM ⟩ ⟩ = ⟨ M , ⟨ (↠-trans (plug-cong F-fst rd*₁) rd*₂) , lpM ⟩ ⟩

sim-snd-cons-v : ∀ {A A′ B B′} {V : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A′} {W′ : ∅ ⊢ B′}
  → Value V → Value V′ → Value W′
  → ∅ , ∅ ⊢ V ⊑ᶜ cons V′ W′
    ------------------------------------------
  → ∃[ M ] ((snd V —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ W′))
sim-snd-cons-v (V-pair {V = V} {W} v w) v′ w′ (⊑ᶜ-cons lpV lpW) = ⟨ W , ⟨ _ —→⟨ β-snd v w ⟩ _ ∎ , lpW ⟩ ⟩
sim-snd-cons-v (V-wrap {V = V} {c} v (Inert.I-pair _)) v′ w′ (⊑ᶜ-wrapl (lpit-pair (pair⊑ lp₁₁ lp₁₂) (pair⊑ lp₂₁ lp₂₂)) lpV)
  with sim-snd-cons-v v v′ w′ lpV
... | ⟨ M , ⟨ rd* , lpM ⟩ ⟩ =
  let x = pair-cast-is-cross c in
    ⟨ M ⟨ sndC c x ⟩ , ⟨ _ —→⟨ snd-cast v {x} ⟩ plug-cong (F-cast (sndC c x)) rd* , ⊑ᶜ-castl lp₁₂ lp₂₂ lpM ⟩ ⟩

sim-snd-cons : ∀ {A A′ B B′} {N : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A′} {W′ : ∅ ⊢ B′}
  → Value V′ → Value W′
  → ∅ , ∅ ⊢ N ⊑ᶜ cons V′ W′
    ------------------------------------------
  → ∃[ M ] ((snd N —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ W′))
sim-snd-cons v′ w′ lpN
  with catchup (V-pair v′ w′) lpN
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with sim-snd-cons-v v v′ w′ lpV
...   | ⟨ M , ⟨ rd*₂ , lpM ⟩ ⟩ = ⟨ M , ⟨ (↠-trans (plug-cong F-snd rd*₁) rd*₂) , lpM ⟩ ⟩

sim-fst-wrap-v : ∀ {A B A₁′ B₁′ A₂′ B₂′} {V : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A₁′ `× B₁′} {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
  → Value V → Value V′ → (i′ : Inert c′) → (x′ : Cross c′)
  → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
    ------------------------------------------------------------------
  → ∃[ M ] ((fst V —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ (fst V′) ⟨ fstC c′ x′ ⟩))
sim-fst-wrap-v (V-wrap {V = V} {c} v i) v′ i′ x′ (⊑ᶜ-wrap (lpii-pair (pair⊑ lp₁₁ lp₁₂) (pair⊑ lp₂₁ lp₂₂)) lpV) =
  let x = pair-cast-is-cross c in
    ⟨ (fst V) ⟨ fstC c x ⟩ , ⟨ _ —→⟨ fst-cast v {x} ⟩ _ ∎ , (⊑ᶜ-cast lp₁₁ lp₂₁ (⊑ᶜ-fst lpV)) ⟩ ⟩
sim-fst-wrap-v (V-wrap {V = V} {c} v i) v′ i′ x′ (⊑ᶜ-wrapl (lpit-pair (pair⊑ lp₁₁ lp₁₂) (pair⊑ lp₂₁ lp₂₂)) lpV)
  with sim-fst-wrap-v v v′ i′ x′ lpV
... | ⟨ M , ⟨ rd* , lpM ⟩ ⟩ =
  let x = pair-cast-is-cross c in
    ⟨ M ⟨ fstC c x ⟩ , ⟨ _ —→⟨ fst-cast v {x} ⟩ plug-cong (F-cast _) rd* , ⊑ᶜ-castl lp₁₁ lp₂₁ lpM ⟩ ⟩
sim-fst-wrap-v {V = V} v v′ i′ x′ (⊑ᶜ-wrapr (lpti-pair (pair⊑ lp₁₁ lp₁₂) (pair⊑ lp₂₁ lp₂₂)) lpV) =
  ⟨ fst V , ⟨ fst V ∎ , ⊑ᶜ-castr lp₁₁ lp₂₁ (⊑ᶜ-fst lpV) ⟩ ⟩

sim-fst-wrap : ∀ {A B A₁′ B₁′ A₂′ B₂′} {N : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A₁′ `× B₁′} {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
  → Value V′ → (i′ : Inert c′) → (x′ : Cross c′)
  → ∅ , ∅ ⊢ N ⊑ᶜ V′ ⟪ i′ ⟫
    ------------------------------------------------------------------
  → ∃[ M ] ((fst N —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ (fst V′) ⟨ fstC c′ x′ ⟩))
sim-fst-wrap v′ i′ x′ lpN
  with catchup (V-wrap v′ i′) lpN
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with sim-fst-wrap-v v v′ i′ x′ lpV
... | ⟨ M , ⟨ rd*₂ , lpM ⟩ ⟩ = ⟨ M , ⟨ (↠-trans (plug-cong F-fst rd*₁) rd*₂) , lpM ⟩ ⟩

sim-snd-wrap-v : ∀ {A B A₁′ B₁′ A₂′ B₂′} {V : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A₁′ `× B₁′} {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
  → Value V → Value V′ → (i′ : Inert c′) → (x′ : Cross c′)
  → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
    ------------------------------------------------------------------
  → ∃[ M ] ((snd V —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ (snd V′) ⟨ sndC c′ x′ ⟩))
sim-snd-wrap-v (V-wrap {V = V} {c} v i) v′ i′ x′ (⊑ᶜ-wrap (lpii-pair (pair⊑ lp₁₁ lp₁₂) (pair⊑ lp₂₁ lp₂₂)) lpV) =
  let x = pair-cast-is-cross c in
    ⟨ (snd V) ⟨ sndC c x ⟩ , ⟨ _ —→⟨ snd-cast v {x} ⟩ _ ∎ , (⊑ᶜ-cast lp₁₂ lp₂₂ (⊑ᶜ-snd lpV)) ⟩ ⟩
sim-snd-wrap-v (V-wrap {V = V} {c} v i) v′ i′ x′ (⊑ᶜ-wrapl (lpit-pair (pair⊑ lp₁₁ lp₁₂) (pair⊑ lp₂₁ lp₂₂)) lpV)
  with sim-snd-wrap-v v v′ i′ x′ lpV
... | ⟨ M , ⟨ rd* , lpM ⟩ ⟩ =
  let x = pair-cast-is-cross c in
    ⟨ M ⟨ sndC c x ⟩ , ⟨ _ —→⟨ snd-cast v {x} ⟩ plug-cong (F-cast _) rd* , ⊑ᶜ-castl lp₁₂ lp₂₂ lpM ⟩ ⟩
sim-snd-wrap-v {V = V} v v′ i′ x′ (⊑ᶜ-wrapr (lpti-pair (pair⊑ lp₁₁ lp₁₂) (pair⊑ lp₂₁ lp₂₂)) lpV) =
  ⟨ snd V , ⟨ snd V ∎ , ⊑ᶜ-castr lp₁₂ lp₂₂ (⊑ᶜ-snd lpV) ⟩ ⟩

sim-snd-wrap : ∀ {A B A₁′ B₁′ A₂′ B₂′} {N : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A₁′ `× B₁′} {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
  → Value V′ → (i′ : Inert c′) → (x′ : Cross c′)
  → ∅ , ∅ ⊢ N ⊑ᶜ V′ ⟪ i′ ⟫
    ------------------------------------------------------------------
  → ∃[ M ] ((snd N —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ (snd V′) ⟨ sndC c′ x′ ⟩))
sim-snd-wrap v′ i′ x′ lpN
  with catchup (V-wrap v′ i′) lpN
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with sim-snd-wrap-v v v′ i′ x′ lpV
... | ⟨ M , ⟨ rd*₂ , lpM ⟩ ⟩ = ⟨ M , ⟨ (↠-trans (plug-cong F-snd rd*₁) rd*₂) , lpM ⟩ ⟩
