module GradualGuaranteeSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
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

fun-cast-is-cross : ∀ {A B C D} → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D))) → Cross c
fun-cast-is-cross (cast (A ⇒ B) (C ⇒ D) ℓ _) = Cross.C-fun

sim-if-true : ∀ {A A′} {L : ∅ ⊢ ` 𝔹} {M N : ∅ ⊢ A} {M′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ L ⊑ᶜ ($ true) {P-Base} → ∅ , ∅ ⊢ M ⊑ᶜ M′
    --------------------------------------------------
  → ∃[ K ] ((if L M N —↠ K) × (∅ , ∅ ⊢ K ⊑ᶜ M′))
sim-if-true {M = M} {N} lpL lpM
  with catchup V-const lpL
... | ⟨ ($ true) {P-Base} , ⟨ V-const , ⟨ rd* , lpV ⟩ ⟩ ⟩ =
  ⟨ M , ⟨ ↠-trans (plug-cong (F-if M N) rd*) (_ —→⟨ β-if-true ⟩ _ ∎) , lpM ⟩ ⟩

sim-if-false : ∀ {A A′} {L : ∅ ⊢ ` 𝔹} {M N : ∅ ⊢ A} {N′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ L ⊑ᶜ ($ false) {P-Base} → ∅ , ∅ ⊢ N ⊑ᶜ N′
    ---------------------------------------------------
  → ∃[ K ] ((if L M N —↠ K) × (∅ , ∅ ⊢ K ⊑ᶜ N′))
sim-if-false {M = M} {N} lpL lpN
  with catchup V-const lpL
... | ⟨ ($ false) {P-Base} , ⟨ V-const , ⟨ rd* , lpV ⟩ ⟩ ⟩ =
  ⟨ N , ⟨ ↠-trans (plug-cong (F-if M N) rd*) (_ —→⟨ β-if-false ⟩ _ ∎) , lpN ⟩ ⟩

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

sim-app-δ : ∀ {A A′ B B′} {L : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A} {f : rep A′ → rep B′} {k : rep A′}
              {ab : Prim (A′ ⇒ B′)} {a : Prim A′} {b : Prim B′}
  → ∅ , ∅ ⊢ L ⊑ᶜ ($ f) {ab}
  → ∅ , ∅ ⊢ M ⊑ᶜ ($ k) {a}
    ----------------------------------------
  → ∃[ N ] ((L · M —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ ($ f k) {b}))
sim-app-δ-v : ∀ {A A′ B B′} {L : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A} {f : rep A′ → rep B′} {k : rep A′}
                {ab : Prim (A′ ⇒ B′)} {a : Prim A′} {b : Prim B′}
  → Value L → Value M
  → ∅ , ∅ ⊢ L ⊑ᶜ ($ f) {ab}
  → ∅ , ∅ ⊢ M ⊑ᶜ ($ k) {a}
    ----------------------------------------
  → ∃[ N ] ((L · M —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ ($ f k) {b}))

sim-app-δ-v {f = f} {k} V-const V-const ⊑ᶜ-prim ⊑ᶜ-prim =
  ⟨ $ f k , ⟨ _ —→⟨ δ ⟩ _ ∎ , ⊑ᶜ-prim ⟩ ⟩

sim-app-δ-v {ab = ()} V-const (V-wrap vM (Inert.I-inj _ _)) ⊑ᶜ-prim (⊑ᶜ-wrapl lpi lpM)
sim-app-δ-v {ab = ()} V-const (V-wrap vM (Inert.I-fun _))   ⊑ᶜ-prim (⊑ᶜ-wrapl lpi lpM)
sim-app-δ-v {ab = ()} V-const (V-wrap vM (Inert.I-pair _))  ⊑ᶜ-prim (⊑ᶜ-wrapl lpi lpM)
sim-app-δ-v {ab = ()} V-const (V-wrap vM (Inert.I-sum _))   ⊑ᶜ-prim (⊑ᶜ-wrapl lpi lpM)

sim-app-δ-v {b = b} (V-wrap vV (Inert.I-fun c)) vM (⊑ᶜ-wrapl (lpit-fun (fun⊑ lp₁₁ lp₁₂) (fun⊑ lp₂₁ lp₂₂)) lpV) lpM =
  {-
    Starting from V ⟪ c ⟫ · M, first we go to (V · (M ⟨ dom c ⟩)) ⟨ cod c ⟩ by `fun-cast`.
    Then we proceed on M ⟨ dom c ⟩ by `catchup` and step to a value W there.
    At this point we have (V · W) ⟨ cod c ⟩ so we make recursive call on V, W and use congruence.
  -}
  let x = fun-cast-is-cross c
      ⟨ W , ⟨ vW , ⟨ rd*₁ , lpW ⟩ ⟩ ⟩ = catchup V-const (⊑ᶜ-castl {c = dom c x} lp₂₁ lp₁₁ lpM)
      ⟨ N , ⟨ rd*₂ , lpN ⟩ ⟩ = sim-app-δ-v {b = b} vV vW lpV lpW in
    ⟨ N ⟨ cod c x ⟩ ,
      ⟨ _ —→⟨ fun-cast vV vM {x} ⟩ ↠-trans (plug-cong (F-cast _) (plug-cong (F-·₂ _ {vV}) rd*₁)) (plug-cong (F-cast _) rd*₂) ,
        ⊑ᶜ-castl lp₁₂ lp₂₂ lpN ⟩ ⟩

sim-app-δ {f = f} {k} {ab} {a} {b} lpL lpM
  with catchup (V-const {k = f}) lpL
... | ⟨ V₁ , ⟨ v₁ , ⟨ rd*₁ , lpV₁ ⟩ ⟩ ⟩
  with catchup (V-const {k = k}) lpM
...   | ⟨ V₂ , ⟨ v₂ , ⟨ rd*₂ , lpV₂ ⟩ ⟩ ⟩
  with sim-app-δ-v {b = b} v₁ v₂ lpV₁ lpV₂
...     | ⟨ N , ⟨ rd*₃ , lpN ⟩ ⟩ =
  ⟨ N , ⟨ ↠-trans (plug-cong (F-·₁ _) rd*₁) (↠-trans (plug-cong (F-·₂ _ {v₁}) rd*₂) rd*₃) , lpN ⟩ ⟩

sim-app-β-v : ∀ {A A′ B B′} {L : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A} {N′ : ∅ , A′ ⊢ B′} {M′ : ∅ ⊢ A′}
  → Value L → Value M → Value M′
  → ∅ , ∅ ⊢ L ⊑ᶜ (ƛ N′) → ∅ , ∅ ⊢ M ⊑ᶜ M′
    ------------------------------------------------------
  → ∃[ M₂ ] ((L · M —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ N′ [ M′ ]))
-- ƛ N ⊑ ƛ N′ . Here we need to prove subst preserves precision.
sim-app-β-v {M = M} (V-ƛ {N = N}) vM vM′ (⊑ᶜ-ƛ lp lpN) lpM =
  ⟨ N [ M ] , ⟨  _ —→⟨ β vM ⟩ _ ∎ , (subst-pres-prec (⊑ˢ-σ₀ lpM) lpN) ⟩ ⟩
-- V ⟪ i ⟫ ⊑ ƛ N′
sim-app-β-v {M = M} (V-wrap {V = V} v (Inert.I-fun c)) vM vM′ (⊑ᶜ-wrapl (lpit-fun (fun⊑ lp₁₁ lp₁₂) (fun⊑ lp₂₁ lp₂₂)) lpV) lpM =
  {- The reduction sequence:
    V ⟪ i ⟫ · M —↠ V ⟪ i ⟫ · W —→ (V · W ⟨ dom c ⟩) ⟨ cod c ⟩ —↠ (V · W₁) ⟨ cod c ⟩ —↠ N ⟨ cod c ⟩
  -}
  let x = fun-cast-is-cross c
      ⟨ W , ⟨ w , ⟨ rd*₁ , lpW ⟩ ⟩ ⟩ = catchup vM′ lpM
      ⟨ W₁ , ⟨ w₁ , ⟨ rd*₂ , lpW₁ ⟩ ⟩ ⟩ = catchup vM′ (⊑ᶜ-castl {c = dom c x} lp₂₁ lp₁₁ lpW)
      ⟨ N , ⟨ rd*₃ , lpN ⟩ ⟩ = sim-app-β-v v w₁ vM′ lpV lpW₁ in
    ⟨ N ⟨ cod c x ⟩ ,
      ⟨ ↠-trans (plug-cong (F-·₂ _ {V-wrap v _}) rd*₁)
                 (_ —→⟨ fun-cast v w {x} ⟩ ↠-trans (plug-cong (F-cast _) (plug-cong (F-·₂ _ {v}) rd*₂))
                                                      (plug-cong (F-cast _) rd*₃)) ,
        ⊑ᶜ-castl lp₁₂ lp₂₂ lpN ⟩ ⟩

sim-app-β : ∀ {A A′ B B′} {L : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A} {N′ : ∅ , A′ ⊢ B′} {M′ : ∅ ⊢ A′}
  → Value M′
  → ∅ , ∅ ⊢ L ⊑ᶜ (ƛ N′) → ∅ , ∅ ⊢ M ⊑ᶜ M′
    ------------------------------------------------------
  → ∃[ M₂ ] ((L · M —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ N′ [ M′ ]))
sim-app-β v lpL lpM
  with catchup V-ƛ lpL
... | ⟨ V₁ , ⟨ v₁ , ⟨ rd*₁ , lpV₁ ⟩ ⟩ ⟩
  with catchup v lpM
...   | ⟨ V₂ , ⟨ v₂ , ⟨ rd*₂ , lpV₂ ⟩ ⟩ ⟩
  with sim-app-β-v v₁ v₂ v lpV₁ lpV₂
...     | ⟨ M₂ , ⟨ rd*₃ , lpM₂ ⟩ ⟩ =
  ⟨ M₂ , ⟨ ↠-trans (plug-cong (F-·₁ _) rd*₁) (↠-trans (plug-cong (F-·₂ _ {v₁}) rd*₂) rd*₃) , lpM₂ ⟩ ⟩
