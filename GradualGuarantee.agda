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


-- Compilation from GTLC to CC preserves precision.
{- We assume Γ ⊢ e ↝ f ⦂ A and Γ′ ⊢ e′ ↝ f′ ⦂ A′ . -}
compile-pres-prec : ∀ {Γ Γ′ A A′} {e : Γ ⊢G A} {e′ : Γ′ ⊢G A′}
  → Γ ⊑* Γ′
  → Γ , Γ′ ⊢ e ⊑ᴳ e′
    -------------------------------
  → (A ⊑ A′) × (Γ , Γ′ ⊢ compile {Γ} {A} e ⊑ᶜ compile {Γ′} {A′} e′)
compile-pres-prec lpc (⊑ᴳ-prim {A = A}) = ⟨ Refl⊑ , ⊑ᶜ-prim ⟩
compile-pres-prec lpc (⊑ᴳ-var {x = x} {x′} eq) = ⟨ ⊑*→⊑ x x′ lpc eq , ⊑ᴳ-var eq ⟩
compile-pres-prec lpc (⊑ᴳ-ƛ lpA lpe) =
  let ⟨ lpB , lpeN ⟩ = compile-pres-prec (⊑*-, lpA lpc) lpe in
    ⟨ (fun⊑ lpA lpB) , ⊑ᶜ-ƛ lpA lpeN ⟩
compile-pres-prec lpc (⊑ᴳ-· lpeL lpeM {m = m} {m′ = m′}) =
  let ⟨ lpA , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
  let ⟨ lpB , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
  let ⟨ lpA₁ , lpA₂ ⟩ = ▹⇒-pres-prec m m′ lpA in
    ⟨ lpA₂ , ⊑ᶜ-· (⊑ᶜ-cast lpA (fun⊑ lpA₁ lpA₂) lpeL′) (⊑ᶜ-cast lpB lpA₁ lpeM′) ⟩
compile-pres-prec lpc (⊑ᴳ-if lpeL lpeM lpeN {aa = aa} {aa′}) =
  let ⟨ lpB , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
  let ⟨ lpA₁ , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
  let ⟨ lpA₂ , lpeN′ ⟩ = compile-pres-prec lpc lpeN in
  let lp⨆aa = ⨆-pres-prec aa aa′ lpA₁ lpA₂ in
    ⟨ lp⨆aa , ⊑ᶜ-if (⊑ᶜ-cast lpB base⊑ lpeL′) (⊑ᶜ-cast lpA₁ lp⨆aa lpeM′) (⊑ᶜ-cast lpA₂ lp⨆aa lpeN′) ⟩
compile-pres-prec lpc (⊑ᴳ-cons lpeM lpeN) =
  let ⟨ lpA , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
  let ⟨ lpB , lpeN′ ⟩ = compile-pres-prec lpc lpeN in
    ⟨ pair⊑ lpA lpB , ⊑ᶜ-cons lpeM′ lpeN′ ⟩
compile-pres-prec lpc (⊑ᴳ-fst lpe {m} {m′}) =
  let ⟨ lp , lpe′ ⟩ = compile-pres-prec lpc lpe in
  let ⟨ lp₁ , lp₂ ⟩ = ▹×-pres-prec m m′ lp in
    ⟨ lp₁ , ⊑ᶜ-fst (⊑ᶜ-cast lp (pair⊑ lp₁ lp₂) lpe′) ⟩
compile-pres-prec lpc (⊑ᴳ-snd lpe {m} {m′}) =
  let ⟨ lp , lpe′ ⟩ = compile-pres-prec lpc lpe in
  let ⟨ lp₁ , lp₂ ⟩ = ▹×-pres-prec m m′ lp in
    ⟨ lp₂ , ⊑ᶜ-snd (⊑ᶜ-cast lp (pair⊑ lp₁ lp₂) lpe′) ⟩
compile-pres-prec lpc (⊑ᴳ-inl lpB lpe) =
  let ⟨ lpA , lpe′ ⟩ = compile-pres-prec lpc lpe in
    ⟨ sum⊑ lpA lpB , ⊑ᶜ-inl lpe′ ⟩
compile-pres-prec lpc (⊑ᴳ-inr lpA lpe) =
  let ⟨ lpB , lpe′ ⟩ = compile-pres-prec lpc lpe in
    ⟨ sum⊑ lpA lpB , ⊑ᶜ-inr lpe′ ⟩
compile-pres-prec lpc (⊑ᴳ-case lpeL lpeM lpeN {ma} {ma′} {mb} {mb′} {mc} {mc′} {bc = bc} {bc′}) =
  let ⟨ lpA , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
  let ⟨ lpB , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
  let ⟨ lpC , lpeN′ ⟩ = compile-pres-prec lpc lpeN in
  let ⟨ lpA₁ , lpA₂ ⟩ = ▹⊎-pres-prec ma ma′ lpA in
  let ⟨ lpB₁ , lpB₂ ⟩ = ▹⇒-pres-prec mb mb′ lpB in
  let ⟨ lpC₁ , lpC₂ ⟩ = ▹⇒-pres-prec mc mc′ lpC in
  let lp⨆bc = ⨆-pres-prec bc bc′ lpB₂ lpC₂ in
    ⟨ lp⨆bc , ⊑ᶜ-case (⊑ᶜ-cast (sum⊑ lpA₁ lpA₂) (sum⊑ lpB₁ lpC₁) (⊑ᶜ-cast lpA (sum⊑ lpA₁ lpA₂) lpeL′))
                       (⊑ᶜ-cast (fun⊑ lpB₁ lpB₂) (fun⊑ lpB₁ lp⨆bc) (⊑ᶜ-cast lpB (fun⊑ lpB₁ lpB₂) lpeM′))
                       (⊑ᶜ-cast (fun⊑ lpC₁ lpC₂) (fun⊑ lpC₁ lp⨆bc) (⊑ᶜ-cast lpC (fun⊑ lpC₁ lpC₂) lpeN′)) ⟩

cast-eq-inv : ∀ {Γ A A′ B} {M : Γ ⊢ A} {M′ : Γ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B)}
  → M ⟨ c ⟩ ≡ M′ ⟨ c′ ⟩
    --------------------
  → Σ[ eq ∈ (A ≡ A′) ] (subst-eq (λ □ → Cast (□ ⇒ B)) eq c ≡ c′) × (subst-eq (λ □ → Γ ⊢ □) eq M ≡ M′)
cast-eq-inv refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

fst-pres-⊑blame : ∀ {Γ Γ′ A A′ B B′} {N : Γ ⊢ A `× B} {ℓ}
  → Γ , Γ′ ⊢ N ⊑ᶜ blame {Γ′} {A′ `× B′} ℓ
  → Γ , Γ′ ⊢ fst N ⊑ᶜ blame {Γ′} {A′} ℓ
fst-pres-⊑blame (⊑ᶜ-castl _ (pair⊑ lp₁ lp₂) lpf) = ⊑ᶜ-blame lp₁
fst-pres-⊑blame (⊑ᶜ-wrapl _ (pair⊑ lp₁ lp₂) lpf) = ⊑ᶜ-blame lp₁
fst-pres-⊑blame (⊑ᶜ-blame (pair⊑ lp₁ lp₂)) = ⊑ᶜ-blame lp₁

blame⋢V : ∀ {Γ Γ′ A A′} {V : Γ′ ⊢ A′} {ℓ}
  → Value V
    ----------------------------------
  → ¬ (Γ , Γ′ ⊢ blame {Γ} {A} ℓ ⊑ᶜ V)
blame⋢V (ParamCastAux.V-wrap v i) (⊑ᶜ-wrapr _ _ lp) = blame⋢V v lp

eq-—↠ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ≡ N
  → M —↠ N
eq-—↠ {M = M} {N} eq rewrite eq = N ∎


-- sim-fst-inert : ∀ {T A A′ B B′} {V : ∅ ⊢ T} {M′ : ∅ ⊢ A′} {N′ : ∅ ⊢ B′} {c : Cast (T ⇒ A `× B)}
--   → Value V
--   → (i : Inert c)
--   → T ⊑ A′ `× B′ → A `× B ⊑ A′ `× B′
--   → ∅ , ∅ ⊢ V ⊑ᶜ cons M′ N′
--     ----------------------------------------------------
--   → ∃[ M ] ((fst (V ⟨ c ⟩) —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ M′))
-- sim-fst-inert (V-pair vM vN) (Inert.I-pair (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~)) lp1 lp2 (⊑ᶜ-cons {M = M} {N = N} lpV _)
--   with lp1 | lp2
-- ... | pair⊑ lp11 lp12 | pair⊑ lp21 lp22 =
--     ⟨ M ⟨ fstC (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~) Cross.C-pair ⟩ , ⟨ rd* , (⊑ᶜ-castl lp11 lp21 lpV) ⟩ ⟩
--   where
--   rd* =
--     _
--       —→⟨ fst-cast (V-pair vM vN) {Cross.C-pair} ⟩
--     _
--       —→⟨ ξ {F = F-cast _} (β-fst vM vN) ⟩
--     _ ∎
-- sim-fst-inert (V-cast {i = i₀} vM) (Inert.I-pair (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~)) lp1 lp2 (⊑ᶜ-castl {M = M} {c = c₀} lp3 lp4 lpM)
--   with sim-fst-inert vM i₀ lp3 lp1 lpM | lp2 | lp4
-- ... | ⟨ M₁ , ⟨ rd* , lpM₁ ⟩ ⟩ | pair⊑ lp21 lp22 | pair⊑ lp41 lp42 =
--   ⟨ (M₁ ⟨ fstC (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~) Cross.C-pair ⟩) , ⟨ rd*′ , ⊑ᶜ-castl lp41 lp21 lpM₁ ⟩ ⟩
--   where
--   rd*′ =
--     _
--       —→⟨ fst-cast (V-cast {i = i₀} vM) {Cross.C-pair} ⟩
--     -- By congruence of multi-step reduction.
--     plug-cong (F-cast _) rd*

-- Relax on precision by using the ground type G instead of A, suppose G ~ A.
⊑-ground-relax : ∀ {A B G}
  → Ground G
  → A ⊑ B → A ~ G → A ≢ ⋆
    ------------------------
  → G ⊑ B
⊑-ground-relax _ unk⊑ unk~L nd = contradiction refl nd
⊑-ground-relax _ base⊑ base~ nd = base⊑
⊑-ground-relax G-Fun (fun⊑ lp1 lp2) (fun~ c1 c2) nd = fun⊑ unk⊑ unk⊑
⊑-ground-relax G-Pair (pair⊑ lp1 lp2) (pair~ c1 c2) nd = pair⊑ unk⊑ unk⊑
⊑-ground-relax G-Sum (sum⊑ lp1 lp2) (sum~ c1 c2) nd = sum⊑ unk⊑ unk⊑

⊑-ground-consis : ∀ {G A B}
  → Ground G
  → G ⊑ A → A ~ B → B ≢ ⋆
    ----------
  → G ⊑ B
⊑-ground-consis G-Base base⊑ unk~R nd = contradiction refl nd
⊑-ground-consis G-Base base⊑ base~ nd = base⊑
⊑-ground-consis G-Fun (fun⊑ lp1 lp2) unk~R nd = contradiction refl nd
⊑-ground-consis G-Fun (fun⊑ lp1 lp2) (fun~ c1 c2) nd = fun⊑ unk⊑ unk⊑
⊑-ground-consis G-Pair (pair⊑ lp1 lp2) unk~R nd = contradiction refl nd
⊑-ground-consis G-Pair (pair⊑ lp1 lp2) (pair~ c1 c2) nd = pair⊑ unk⊑ unk⊑
⊑-ground-consis G-Sum (sum⊑ lp1 lp2) unk~R nd = contradiction refl nd
⊑-ground-consis G-Sum (sum⊑ lp1 lp2) (sum~ c1 c2) nd = sum⊑ unk⊑ unk⊑

inert-src-¬⋆ : ∀ {S T : Type} {c : Cast (S ⇒ T)}
  → Inert c → T ≢ ⋆
  → S ≢ ⋆
inert-src-¬⋆ (Inert.I-inj x c) nd = contradiction refl nd
inert-src-¬⋆ (Inert.I-fun c) nd = λ ()
inert-src-¬⋆ (Inert.I-pair c) nd = λ ()
inert-src-¬⋆ (Inert.I-sum c) nd = λ ()

cast→~ : ∀ {S T} → Cast (S ⇒ T) → S ~ T
cast→~ (cast A B ℓ c~) = c~

castl-V-⊑ : ∀ {Γ Γ′ A A′} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′}
                          {c : Cast (A ⇒ ⋆)} {i : Inert c}
  → Value V → Value V′ → Inert c
  → A′ ≢ ⋆
  → Γ , Γ′ ⊢ V ⟪ i ⟫ ⊑ᶜ V′
    ------------------------
  → A ⊑ A′
castl-V-⊑ v (V-wrap {c = c₁} v′ i′) (Inert.I-inj a-g _) nd (⊑ᶜ-wrap lp1 lp2 lpV) =
  ⊑-ground-consis a-g lp1 (cast→~ c₁) nd
castl-V-⊑ v v′ i nd (⊑ᶜ-wrapl lp1 lp2 lpVc) = lp1
castl-V-⊑ v (V-wrap {c = c₁} v′ i₁) i nd (⊑ᶜ-wrapr _ _ lpVc) with i
... | Inert.I-inj a-g _ =
  let iH = castl-V-⊑ v v′ i (inert-src-¬⋆ i₁ nd) lpVc in
    ⊑-ground-consis a-g iH (cast→~ c₁) nd

-- ⊑-cast-switch-side : ∀ {Γ Γ′ G A′ B′} {V : Γ ⊢ G} {V′ : Γ′ ⊢ A′} {c : Cast (G ⇒ ⋆)} {c′ : Cast (A′ ⇒ B′)}
--   → Value V → Value V′ → Inert c → Inert c′
--   → B′ ≢ ⋆
--   → G ⊑ B′ → Γ , Γ′ ⊢ V ⟨ c ⟩ ⊑ᶜ V′
--     ----------------------------------
--   → Γ , Γ′ ⊢ V ⊑ᶜ V′ ⟨ c′ ⟩
-- ⊑-cast-switch-side {c′ = c′} v v′ (Inert.I-inj g-g c) i′ x lp (⊑ᶜ-cast lp1 lp2 lpV) =
--   let x′ = (inert-src-¬⋆ i′ x) in
--   let lp3 = (⊑-ground-consis g-g lp (Sym~ (cast→~ c′)) x′) in
--     ⊑ᶜ-castr lp3 lp (⊑ᶜ-castr lp1 lp3 lpV)
-- ⊑-cast-switch-side {c′ = c′} v v′ (Inert.I-inj g-g c) i′ x lp (⊑ᶜ-castl lp1 lp2 lpV) =
--   let x′ = (inert-src-¬⋆ i′ x) in
--   let lp3 = (⊑-ground-consis g-g lp (Sym~ (cast→~ c′)) x′) in
--     ⊑ᶜ-castr lp3 lp lpV
-- ⊑-cast-switch-side {c′ = c′} v (V-cast {c = c′₁} {i = i′₁} v′) i i′ x lp (⊑ᶜ-castr lp1 lp2 lpVc) with i
-- ... | Inert.I-inj g-g c =
--   let x′ = (inert-src-¬⋆ i′ x) in
--   let lp3 = (⊑-ground-consis g-g lp (Sym~ (cast→~ c′)) x′) in
--   let iH = ⊑-cast-switch-side {c′ = c′₁} v v′ i i′₁ x′ lp3 lpVc in
--     ⊑ᶜ-castr lp3 lp iH

⊑G-nd-ground : ∀ {A G}
  → Ground G → A ⊑ G  → A ≢ ⋆
  → Ground A
⊑G-nd-ground G-Base unk⊑ x = contradiction refl x
⊑G-nd-ground G-Base base⊑ x = G-Base
⊑G-nd-ground G-Fun unk⊑ x = contradiction refl x
⊑G-nd-ground G-Fun (fun⊑ unk⊑ unk⊑) x = G-Fun
⊑G-nd-ground G-Pair unk⊑ x = contradiction refl x
⊑G-nd-ground G-Pair (pair⊑ unk⊑ unk⊑) x = G-Pair
⊑G-nd-ground G-Sum unk⊑ x = contradiction refl x
⊑G-nd-ground G-Sum (sum⊑ unk⊑ unk⊑) x = G-Sum

applyCast-left : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
  → (a : Active c)
  → (vV : Value V) → Value V′
  → A ⊑ A′ → B ⊑ A′
  → Γ , Γ′ ⊢ V ⊑ᶜ V′
    ----------------------------------------------------------
  → ∃[ W ] ((Value W) × (applyCast V vV c {a} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
applyCast-left (Active.A-id _) vV vV′ lp1 lp2 lpV = ⟨ _ , ⟨ vV , ⟨ _ ∎ , lpV ⟩ ⟩ ⟩
applyCast-left (Active.A-inj _ x x₁) vV vV′ lp1 lp2 lpV = {!!}
applyCast-left (Active.A-proj _ x) vV vV′ lp1 lp2 lpV = {!!}

cast-left : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
  → Value V → Value V′
  → A ⊑ A′ → B ⊑ A′
  → Γ , Γ′ ⊢ V ⊑ᶜ V′
    ----------------------------------------------------------
  → ∃[ W ] ((Value W) × (V ⟨ c ⟩ —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
cast-left {V = V} {V′} {c} vV vV′ lp1 lp2 lpV with GroundInertX.ActiveOrInert c
... | inj₁ a = {!!}
... | inj₂ i = ⟨ V ⟪ i ⟫ , ⟨ (V-wrap vV i) , ⟨ _ —→⟨ wrap vV {i} ⟩ _ ∎ , ⊑ᶜ-wrapl lp1 lp2 lpV ⟩ ⟩ ⟩

catchup : ∀ {Γ Γ′ A A′} {M : Γ ⊢ A} {V′ : Γ′ ⊢ A′}
  → Value V′
  → Γ , Γ′ ⊢ M ⊑ᶜ V′
    -----------------------------------------------------
  → ∃[ V ] ((Value V) × (M —↠ V) × (Γ , Γ′ ⊢ V ⊑ᶜ V′))
catchup {M = $ k} v ⊑ᶜ-prim = ⟨ $ k , ⟨ V-const , ⟨ _ ∎ , ⊑ᶜ-prim ⟩ ⟩ ⟩
catchup v (⊑ᶜ-ƛ lp lpM) = ⟨ ƛ _ , ⟨ V-ƛ , ⟨ (ƛ _) ∎ , ⊑ᶜ-ƛ lp lpM ⟩ ⟩ ⟩
catchup (ParamCastAux.V-pair v₁ v₂) (⊑ᶜ-cons lpM₁ lpM₂) with catchup v₁ lpM₁ | catchup v₂ lpM₂
... | ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ₘ , lpVₘ ⟩ ⟩ ⟩ | ⟨ Vₙ , ⟨ vₙ , ⟨ rd⋆ₙ , lpVₙ ⟩ ⟩ ⟩ =
  ⟨ cons Vₘ Vₙ , ⟨ ParamCastAux.V-pair vₘ vₙ , ⟨ ↠-trans (plug-cong (F-×₂ _) rd⋆ₘ) (plug-cong (F-×₁ _) rd⋆ₙ) , ⊑ᶜ-cons lpVₘ lpVₙ ⟩ ⟩ ⟩
catchup (ParamCastAux.V-inl v) (⊑ᶜ-inl lpM) with catchup v lpM
... | ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ , lpVₘ ⟩ ⟩ ⟩ = ⟨ inl Vₘ , ⟨ V-inl vₘ , ⟨ plug-cong F-inl rd⋆ , ⊑ᶜ-inl lpVₘ ⟩ ⟩ ⟩
catchup (ParamCastAux.V-inr v) (⊑ᶜ-inr lpN) with catchup v lpN
... | ⟨ Vₙ , ⟨ vₙ , ⟨ rd* , lpVₙ ⟩ ⟩ ⟩ = ⟨ inr Vₙ , ⟨ V-inr vₙ , ⟨ plug-cong F-inr rd* , ⊑ᶜ-inr lpVₙ ⟩ ⟩ ⟩
-- catchup (ParamCastAux.V-wrap v i′) (⊑ᶜ-wrap {c = c} lp1 lp2 lpM) with catchup v lpM
-- ... | ⟨ V , ⟨ vV , ⟨ rd* , lpV ⟩ ⟩ ⟩ = {!!}
-- catchup v (⊑ᶜ-wrapl x x₁ lpM) = {!!}
-- catchup v (⊑ᶜ-wrapr x x₁ lpM) = {!!}

catchup v (⊑ᶜ-castl {c = c} lp1 lp2 lpM)
  with catchup v lpM
... | ⟨ V , ⟨ vV , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with cast-left {c = c} vV v lp1 lp2 lpV
...   | ⟨ W , ⟨ vW , ⟨ rd*₂ , lpW ⟩ ⟩ ⟩ =
  ⟨ W , ⟨ vW , ⟨ (↠-trans (plug-cong (F-cast _) rd*₁) rd*₂) , lpW ⟩ ⟩ ⟩
catchup v (⊑ᶜ-wrap x x₁ lpM) = {!!}
catchup v (⊑ᶜ-wrapl x x₁ lpM) = {!!}
catchup v (⊑ᶜ-wrapr x x₁ lpM) = {!!}

sim-fst : ∀ {A A′ B B′} {N : ∅ ⊢ A `× B} {M′ : ∅ ⊢ A′} {N′ : ∅ ⊢ B′}
  → ∅ , ∅ ⊢ N ⊑ᶜ cons M′ N′
    ------------------------------------------
  → ∃[ M ] ((fst N —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ M′))
sim-fst (⊑ᶜ-cons lpf lpf₁) = {!!}
sim-fst (⊑ᶜ-castl {A = T} {M = N₁} {c = c} lp1 lp2 lpf) = {!!}

gradual-guarantee : ∀ {A A′} {M₁ : ∅ ⊢ A} {M₁′ M₂′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ M₁ ⊑ᶜ M₁′     -- Note M₁′ is more precise here.
  → M₁′ —→ M₂′
    ---------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))

gradual-guarantee-fst : ∀ {A A′ B B′} {N₁ : ∅ ⊢ A `× B} {N₁′ : ∅ ⊢ A′ `× B′} {M₁ : ∅ ⊢ A} {M₁′ M₂′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ N₁ ⊑ᶜ N₁′
  → M₁ ≡ fst N₁ → M₁′ ≡ fst N₁′
  → M₁′ —→ M₂′
    -----------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))

gradual-guarantee-fst {N₁ = N₁} {N₁′} {M₁} {M₁′} {M₂′} N₁⊑N₁′ refl eq2 (ξ {M′ = N₂′} {F} N₁′→N₂′) with plug-inv-fst F eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩ with gradual-guarantee N₁⊑N₁′ N₁′→N₂′
...   | ⟨ N₂ , ⟨ N₁↠N₂ , N₂⊑N₂′ ⟩ ⟩ = ⟨ fst N₂ , ⟨ plug-cong F-fst N₁↠N₂ , ⊑ᶜ-fst N₂⊑N₂′ ⟩ ⟩
gradual-guarantee-fst {N₁ = N₁} lpf refl eq2 (ξ-blame {F = F}) with plug-inv-fst F eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩ = ⟨ fst N₁ , ⟨ fst N₁ ∎ , fst-pres-⊑blame lpf ⟩ ⟩
gradual-guarantee-fst {N₁ = N₁} lpf refl refl (β-fst {V = V′} {W = W′} vV′ vW′) = sim-fst lpf
gradual-guarantee-fst lpf refl refl (fst-cast x) = {!!}

-- gradual-guarantee (⊑ᶜ-prim) rd = ⊥-elim (V⌿→ V-const rd)
-- gradual-guarantee (⊑ᶜ-ƛ _ _) rd = ⊥-elim (V⌿→ V-ƛ rd)
-- gradual-guarantee (⊑ᶜ-· lpf lpf₁) rd = {!!}
-- gradual-guarantee (⊑ᶜ-if lpf lpf₁ lpf₂) rd = {!!}
-- gradual-guarantee (⊑ᶜ-cons lpf lpf₁) rd = {!!}
-- gradual-guarantee (⊑ᶜ-fst lpf) rd = gradual-guarantee-fst lpf refl refl rd
-- gradual-guarantee (⊑ᶜ-snd lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-inl lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-inr lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-case lpf lpf₁ lpf₂) rd = {!!}
-- gradual-guarantee (⊑ᶜ-cast x x₁ lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-castl x x₁ lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-castr x x₁ lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-blame _) rd = ⊥-elim (blame⌿→ rd)
