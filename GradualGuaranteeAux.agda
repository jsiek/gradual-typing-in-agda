module GradualGuaranteeAux where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
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


{-
  Compilation from GTLC to CC preserves precision.
    - We assume Γ ⊢ e ↝ f ⦂ A and Γ′ ⊢ e′ ↝ f′ ⦂ A′ .
-}
compile-pres-prec : ∀ {Γ Γ′ A A′} {e : Γ ⊢G A} {e′ : Γ′ ⊢G A′}
  → Γ ⊑* Γ′
  → Γ , Γ′ ⊢ e ⊑ᴳ e′
    -------------------------------
  → (A ⊑ A′) × (Γ , Γ′ ⊢ compile {Γ} {A} e ⊑ᶜ compile {Γ′} {A′} e′)
compile-pres-prec lpc (⊑ᴳ-prim {A = A}) = ⟨ Refl⊑ , ⊑ᶜ-prim ⟩
compile-pres-prec lpc (⊑ᴳ-var {x = x} {x′} eq) = ⟨ ⊑*→⊑ x x′ lpc eq , ⊑ᶜ-var eq ⟩
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
    ⟨ sum⊑ lpA lpB , ⊑ᶜ-inl lpB lpe′ ⟩
compile-pres-prec lpc (⊑ᴳ-inr lpA lpe) =
  let ⟨ lpB , lpe′ ⟩ = compile-pres-prec lpc lpe in
    ⟨ sum⊑ lpA lpB , ⊑ᶜ-inr lpA lpe′ ⟩
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

wrapV-⊑-inv : ∀ {Γ Γ′ A A′} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ ⋆)}
  → Value V → Value V′ → (i : Inert c) → A′ ≢ ⋆
  → Γ , Γ′ ⊢ V ⟪ i ⟫ ⊑ᶜ V′
  → Γ , Γ′ ⊢ V ⊑ᶜ V′
wrapV-⊑-inv v v' (Inert.I-inj g c) nd (⊑ᶜ-wrap (lpii-inj .g) lpVi) = contradiction refl nd
wrapV-⊑-inv v v' i nd (⊑ᶜ-wrapl x lpVi) = lpVi

ground-to-ndng-inert : ∀ {H B} {ℓ}
  → (c~ : H ~ B)
  → Ground H → B ≢ ⋆ → ¬ Ground B
  → Inert (cast H B ℓ c~)
ground-to-ndng-inert unk~R h-g b-nd b-ng = contradiction refl b-nd
ground-to-ndng-inert base~ h-g b-nd b-ng = contradiction h-g b-ng
ground-to-ndng-inert (fun~ c~ c~₁) h-g b-nd b-ng = Inert.I-fun _
ground-to-ndng-inert (pair~ c~ c~₁) h-g b-nd b-ng = Inert.I-pair _
ground-to-ndng-inert (sum~ c~ c~₁) h-g b-nd b-ng = Inert.I-sum _


private
  {-
    We write them as separate lemmas to get around Agda's termination checker.
    This is because the first, ground one does not make any recursive call and the
    second, non-ground one calls into the first one, which serves as a base case.
  -}
  applyCast-proj-g-left : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
    → (nd : B ≢ ⋆) → Ground B   -- B ≢ ⋆ is actually implied since B is ground.
    → (vV : Value V) → Value V′
    → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
      ----------------------------------------------------------
    → ∃[ W ] ((Value W) × (applyCast V vV c {Active.A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))

  applyCast-proj-ng-left : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
    → (nd : B ≢ ⋆) → ¬ Ground B
    → (vV : Value V) → Value V′
    → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
      ----------------------------------------------------------
    → ∃[ W ] ((Value W) × (applyCast V vV c {Active.A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))

  {-
    Finally, we case on whether the target type of the cast, B, is ground, for which
    we've already proved both cases. As is mentioned above, we make it very sure that
    the proof terminates - even if in the expansion case, the term grows bigger by one cast.
  -}
  applyCast-proj-left : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
    → (nd : B ≢ ⋆)
    → (vV : Value V) → Value V′
    → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
      ----------------------------------------------------------
    → ∃[ W ] ((Value W) × (applyCast V vV c {Active.A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))

applyCast-proj-g-left {c = cast .⋆ B ℓ _} nd g v v′ lp lpV with ground? B
... | yes b-g
  with canonical⋆ _ v
...   | ⟨ G , ⟨ V₁ , ⟨ c₁ , ⟨ i , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with gnd-eq? G B {inert-ground c₁ i} {b-g}
...     | yes ap-b rewrite ap-b with v
...       | V-wrap vV₁ .i = ⟨ V₁ , ⟨ vV₁ , ⟨ V₁ ∎ , wrapV-⊑-inv vV₁ v′ i (lp-¬⋆ nd lp) lpV ⟩ ⟩ ⟩
applyCast-proj-g-left {c = cast .⋆ B ℓ _} nd g v v′ lp lpV | yes b-g | ⟨ G , ⟨ V₁ , ⟨ c₁ , ⟨ Inert.I-inj g₁ _ , meq ⟩ ⟩ ⟩ ⟩ | no ap-b
  with lpV
...       | ⊑ᶜ-wrapl (lpit-inj _ lp₁) _ = contradiction (lp-consis-ground-eq g₁ g Refl~ lp₁ lp) ap-b
...       | ⊑ᶜ-wrap (lpii-inj _) _ = contradiction lp (nd⋢⋆ nd)
applyCast-proj-g-left {c = cast .⋆ B ℓ _} nd g v v′ lp lpV | no b-ng = contradiction g b-ng

applyCast-proj-ng-left {c = cast .⋆ B ℓ _} nd ng v v′ lp lpV
  with ground? B
... | yes b-g = contradiction b-g ng
... | no b-ng
  with ground B {nd}
...   | ⟨ H , ⟨ h-g , c~ ⟩ ⟩
  with applyCast-proj-g-left {c = cast ⋆ H ℓ unk~L} (ground-nd h-g) h-g v v′ (⊑-ground-relax h-g lp c~ nd) lpV
...     | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ =
  {- The important observation here is that the expanded casts are an active projection to ground followed by an inert cross cast. -}
  let a = Active.A-proj (cast ⋆ H ℓ unk~L) (ground-nd h-g) in   -- The 1st cast ⋆ ⇒ H is active since H is ground.
  let i = ground-to-ndng-inert {ℓ = ℓ} (Sym~ c~) h-g nd ng in   -- The 2nd cast H ⇒ B is inert since it is cross.
  ⟨ (W ⟪ i ⟫) ,
    ⟨ (V-wrap vW i) ,
      ⟨ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {a} ⟩ rd*)) (_ —→⟨ wrap vW {i} ⟩ _ ∎) ,
        (⊑ᶜ-wrapl (⊑→lpit i (⊑-ground-relax h-g lp c~ nd) lp) lpW) ⟩ ⟩ ⟩

applyCast-proj-left {B = B} {c = c} nd v v′ lp lpV
  with ground? B
... | yes g = applyCast-proj-g-left {c = c} nd g v v′ lp lpV
... | no ng = applyCast-proj-ng-left {c = c} nd ng v v′ lp lpV


applyCast-left : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
  → (a : Active c)
  → (vV : Value V) → Value V′
  → A ⊑ A′ → B ⊑ A′
  → Γ , Γ′ ⊢ V ⊑ᶜ V′
    ----------------------------------------------------------
  → ∃[ W ] ((Value W) × (applyCast V vV c {a} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))

cast-left : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
  → Value V → Value V′
  → A ⊑ A′ → B ⊑ A′
  → Γ , Γ′ ⊢ V ⊑ᶜ V′
    ----------------------------------------------------------
  → ∃[ W ] ((Value W) × (V ⟨ c ⟩ —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))

applyCast-left (Active.A-id _) vV vV′ lp1 lp2 lpV = ⟨ _ , ⟨ vV , ⟨ _ ∎ , lpV ⟩ ⟩ ⟩
applyCast-left {A = A} {V = V} {c = cast A ⋆ ℓ _} (Active.A-inj c a-ng a-nd) vV vV′ lp1 lp2 lpV
  with ground A {a-nd}
... | ⟨ G , ⟨ g , c~ ⟩ ⟩
  with g | c~ | lp1
...   | G-Base | base~ | _ =
  let i = Inert.I-inj g (cast G ⋆ ℓ unk~R) in
    ⟨ V ⟪ i ⟫ , ⟨ V-wrap vV i , ⟨ _ —→⟨ ξ (cast vV {Active.A-id {a = A-Base} _}) ⟩ _ —→⟨ wrap vV {i} ⟩ _ ∎ , ⊑ᶜ-wrapl (lpit-inj g lp1) lpV ⟩ ⟩ ⟩
...   | G-Base | unk~L | _ = contradiction refl a-nd
...   | G-Fun | fun~ c~₁ c~₂ | fun⊑ lp11 lp12 =
  let i₁ = Inert.I-fun (cast A G ℓ (fun~ c~₁ c~₂)) in
  let i₂ = Inert.I-inj g (cast G ⋆ ℓ unk~R) in
    ⟨ V ⟪ i₁ ⟫ ⟪ i₂ ⟫ , ⟨ V-wrap (V-wrap vV i₁) i₂ ,
      ⟨ _ —→⟨ ξ (wrap vV {i₁}) ⟩ _ —→⟨ wrap (V-wrap vV i₁) {i₂} ⟩ _ ∎ ,
        (⊑ᶜ-wrapl (lpit-inj g (⊑-ground-relax g lp1 c~ a-nd)) (⊑ᶜ-wrapl (lpit-fun lp1 ground-fun-⊑) lpV)) ⟩ ⟩ ⟩
...   | G-Fun | unk~L | _ = contradiction refl a-nd
...   | G-Pair | pair~ c~₁ c~₂ | pair⊑ lp11 lp12 =
  let i₁ = Inert.I-pair (cast A G ℓ (pair~ c~₁ c~₂)) in
  let i₂ = Inert.I-inj g (cast G ⋆ ℓ unk~R) in
    ⟨ V ⟪ i₁ ⟫ ⟪ i₂ ⟫ , ⟨ V-wrap (V-wrap vV i₁) i₂ ,
      ⟨ _ —→⟨ ξ (wrap vV {i₁}) ⟩ _ —→⟨ wrap (V-wrap vV i₁) {i₂} ⟩ _ ∎ ,
        (⊑ᶜ-wrapl (lpit-inj g (⊑-ground-relax g lp1 c~ a-nd)) (⊑ᶜ-wrapl (lpit-pair lp1 ground-pair-⊑) lpV)) ⟩ ⟩ ⟩
...   | G-Pair | unk~L | _ = contradiction refl a-nd
...   | G-Sum | sum~ c~₁ c~₂ | sum⊑ lp11 lp12 =
  let i₁ = Inert.I-sum (cast A G ℓ (sum~ c~₁ c~₂)) in
  let i₂ = Inert.I-inj g (cast G ⋆ ℓ unk~R) in
    ⟨ V ⟪ i₁ ⟫ ⟪ i₂ ⟫ , ⟨ V-wrap (V-wrap vV i₁) i₂ ,
      ⟨ _ —→⟨ ξ (wrap vV {i₁}) ⟩ _ —→⟨ wrap (V-wrap vV i₁) {i₂} ⟩ _ ∎ ,
        (⊑ᶜ-wrapl (lpit-inj g (⊑-ground-relax g lp1 c~ a-nd)) (⊑ᶜ-wrapl (lpit-sum lp1 ground-sum-⊑) lpV)) ⟩ ⟩ ⟩
...   | G-Sum | unk~L | _ = contradiction refl a-nd
applyCast-left (Active.A-proj c b-nd) vV vV′ lp1 lp2 lpV = applyCast-proj-left {c = c} b-nd vV vV′ lp2 lpV

cast-left {V = V} {V′} {c} vV vV′ lp1 lp2 lpV
  with GroundInertX.ActiveOrInert c
... | inj₁ a
  with applyCast-left a vV vV′ lp1 lp2 lpV
...   | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ (_ —→⟨ cast vV {a} ⟩ rd*) , lpW ⟩ ⟩ ⟩
cast-left {V = V} {V′} {c} vV vV′ lp1 lp2 lpV | inj₂ i =
  ⟨ V ⟪ i ⟫ , ⟨ (V-wrap vV i) , ⟨ _ —→⟨ wrap vV {i} ⟩ _ ∎ , ⊑ᶜ-wrapl (⊑→lpit i lp1 lp2) lpV ⟩ ⟩ ⟩

catchup : ∀ {Γ Γ′ A A′} {M : Γ ⊢ A} {V′ : Γ′ ⊢ A′}
  → Value V′
  → Γ , Γ′ ⊢ M ⊑ᶜ V′
    -----------------------------------------------------
  → ∃[ V ] ((Value V) × (M —↠ V) × (Γ , Γ′ ⊢ V ⊑ᶜ V′))
catchup {M = $ k} v′ ⊑ᶜ-prim = ⟨ $ k , ⟨ V-const , ⟨ _ ∎ , ⊑ᶜ-prim ⟩ ⟩ ⟩
catchup v′ (⊑ᶜ-ƛ lp lpM) = ⟨ ƛ _ , ⟨ V-ƛ , ⟨ (ƛ _) ∎ , ⊑ᶜ-ƛ lp lpM ⟩ ⟩ ⟩
catchup (V-pair v′₁ v′₂) (⊑ᶜ-cons lpM₁ lpM₂)
  with catchup v′₁ lpM₁ | catchup v′₂ lpM₂
... | ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ₘ , lpVₘ ⟩ ⟩ ⟩ | ⟨ Vₙ , ⟨ vₙ , ⟨ rd⋆ₙ , lpVₙ ⟩ ⟩ ⟩ =
  ⟨ cons Vₘ Vₙ , ⟨ ParamCastAux.V-pair vₘ vₙ ,
                   ⟨ ↠-trans (plug-cong (F-×₂ _) rd⋆ₘ) (plug-cong (F-×₁ _) rd⋆ₙ) , ⊑ᶜ-cons lpVₘ lpVₙ ⟩ ⟩ ⟩
catchup (V-inl v′) (⊑ᶜ-inl lp lpM)
  with catchup v′ lpM
... | ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ , lpVₘ ⟩ ⟩ ⟩ = ⟨ inl Vₘ , ⟨ V-inl vₘ , ⟨ plug-cong F-inl rd⋆ , ⊑ᶜ-inl lp lpVₘ ⟩ ⟩ ⟩
catchup (V-inr v′) (⊑ᶜ-inr lp lpN)
  with catchup v′ lpN
... | ⟨ Vₙ , ⟨ vₙ , ⟨ rd* , lpVₙ ⟩ ⟩ ⟩ = ⟨ inr Vₙ , ⟨ V-inr vₙ , ⟨ plug-cong F-inr rd* , ⊑ᶜ-inr lp lpVₙ ⟩ ⟩ ⟩
catchup v′ (⊑ᶜ-castl {c = c} lp1 lp2 lpM)
  with catchup v′ lpM
... | ⟨ V , ⟨ vV , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with cast-left {c = c} vV v′ lp1 lp2 lpV  -- this is the more involved case
...   | ⟨ W , ⟨ vW , ⟨ rd*₂ , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ (↠-trans (plug-cong (F-cast _) rd*₁) rd*₂) , lpW ⟩ ⟩ ⟩
catchup (V-wrap v′ i′) (⊑ᶜ-wrap {i = i} lp lpM)
  with catchup v′ lpM  -- just recur in all 3 wrap cases
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W ⟪ i ⟫ , ⟨ V-wrap vW i , ⟨ plug-cong (F-wrap _) rd* , ⊑ᶜ-wrap lp lpW ⟩ ⟩ ⟩
catchup v′ (⊑ᶜ-wrapl {i = i} lp lpM)
  with catchup v′ lpM
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W ⟪ i ⟫ , ⟨ V-wrap vW i , ⟨ plug-cong (F-wrap _) rd* , ⊑ᶜ-wrapl lp lpW ⟩ ⟩ ⟩
catchup (V-wrap v′ _) (⊑ᶜ-wrapr lp lpM)
  with catchup v′ lpM
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ rd* , ⊑ᶜ-wrapr lp lpW ⟩ ⟩ ⟩




infix 6 _,_,_,_⊢_⊑ˢ_

data _,_,_,_⊢_⊑ˢ_ : (Γ Δ Γ′ Δ′ : Context) → Subst Γ Δ → Subst Γ′ Δ′ → Set where

  ⊑ˢ-σ₀ : ∀ {Δ Δ′ A A′} {M : Δ ⊢ A} {M′ : Δ′ ⊢ A′}
    → Δ , Δ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → (Δ , A) , Δ , (Δ′ , A′) , Δ′ ⊢ (subst-zero M) ⊑ˢ (subst-zero M′)

  ⊑ˢ-exts : ∀ {Γ Γ′ Δ Δ′ B B′} {σ : Subst Γ Δ} {σ′ : Subst Γ′ Δ′}
    → Γ , Δ , Γ′ , Δ′ ⊢ σ ⊑ˢ σ′
      -------------------------------------------------------------------
    → (Γ ,  B) , (Δ , B) , (Γ′ , B′) , (Δ′ , B′) ⊢ (exts σ) ⊑ˢ (exts σ′)

ρ-Cong : ∀ {Γ Γ′ Δ Δ′} → (ρ : Rename Γ Δ) → (ω : Rename Γ′ Δ′) → Set
ρ-Cong {Γ} {Γ′} {Δ} {Δ′} ρ ω =
  ∀ {A B} {x : Γ ∋ A} {y : Γ′ ∋ B} → ∋→ℕ x ≡ ∋→ℕ y → ∋→ℕ (ρ x) ≡ ∋→ℕ (ω y)

S-Cong : ∀ {Γ Γ′ A A′} → ρ-Cong {Γ} {Γ′} {Γ , A} {Γ′ , A′} S_ S_
S-Cong eq = cong suc eq

ext-pres-ρ-Cong : ∀ {Γ Γ′ Δ Δ′} {B B′} {ρ : Rename Γ Δ} {ω : Rename Γ′ Δ′}
  → ρ-Cong ρ ω
    -----------------------------------------------------------
  → ρ-Cong {Γ , B} {Γ′ , B′} {Δ , B}  {Δ′ , B′} (ext ρ) (ext ω)
ext-pres-ρ-Cong f {x = Z} {Z} eq = refl
ext-pres-ρ-Cong f {x = S x} {S y} eq = let ρx≡ωy = f (suc-injective eq) in cong suc ρx≡ωy

rename-pres-prec : ∀ {Γ Γ′ Δ Δ′ A A′} {ρ : Rename Γ Δ} {ρ′ : Rename Γ′ Δ′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
  → ρ-Cong ρ ρ′
  → Γ , Γ′ ⊢ M ⊑ᶜ M′
    ------------------------------------
  → Δ , Δ′ ⊢ rename ρ M ⊑ᶜ rename ρ′ M′
rename-pres-prec f ⊑ᶜ-prim = ⊑ᶜ-prim
rename-pres-prec f (⊑ᶜ-var eq) = ⊑ᶜ-var (f eq)
rename-pres-prec f (⊑ᶜ-ƛ lp lpM) = ⊑ᶜ-ƛ lp (rename-pres-prec (ext-pres-ρ-Cong f) lpM)
rename-pres-prec f (⊑ᶜ-· lpL lpM) = ⊑ᶜ-· (rename-pres-prec f lpL) (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-if lpL lpM lpN) =
  ⊑ᶜ-if (rename-pres-prec f lpL) (rename-pres-prec f lpM) (rename-pres-prec f lpN)
rename-pres-prec f (⊑ᶜ-cons lpM lpN) =
  ⊑ᶜ-cons (rename-pres-prec f lpM) (rename-pres-prec f lpN)
rename-pres-prec f (⊑ᶜ-fst lpM)    = ⊑ᶜ-fst (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-snd lpM)    = ⊑ᶜ-snd (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-inl lp lpM) = ⊑ᶜ-inl lp (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-inr lp lpM) = ⊑ᶜ-inr lp (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-case lpL lpM lpN) =
  ⊑ᶜ-case (rename-pres-prec f lpL) (rename-pres-prec f lpM) (rename-pres-prec f lpN)
rename-pres-prec f (⊑ᶜ-cast lp1 lp2 lpM)  = ⊑ᶜ-cast  lp1 lp2 (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-castl lp1 lp2 lpM) = ⊑ᶜ-castl lp1 lp2 (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-castr lp1 lp2 lpM) = ⊑ᶜ-castr lp1 lp2 (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-wrap lpi lpM)  = ⊑ᶜ-wrap  lpi (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-wrapl lpi lpM) = ⊑ᶜ-wrapl lpi (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-wrapr lpi lpM) = ⊑ᶜ-wrapr lpi (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-blame lp) = ⊑ᶜ-blame lp

S-pres-prec : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ B} {M′ : Γ′ ⊢ B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      --------------------------------------------------
    → (Γ , A) , (Γ′ , A′) ⊢ rename S_ M ⊑ᶜ rename S_ M′
S-pres-prec {A = A} {A′} lpM = rename-pres-prec (S-Cong {A = A} {A′}) lpM

{-
  Here we need to prove a lemma : σ ⊑ σ′ → σ x ⊑ σ y if x ≡ y
-}
⊑ˢ→⊑ᶜ : ∀ {Γ Γ′ Δ Δ′ A A′} {σ : Subst Γ Δ} {σ′ : Subst Γ′ Δ′} {x : Γ ∋ A} {y : Γ′ ∋ A′}
  → Γ , Δ , Γ′ , Δ′ ⊢ σ ⊑ˢ σ′
  → ∋→ℕ x ≡ ∋→ℕ y
    --------------------------
  → Δ , Δ′ ⊢ σ x ⊑ᶜ σ′ y
⊑ˢ→⊑ᶜ {x = Z} {Z} (⊑ˢ-σ₀ lpM) eq = lpM
⊑ˢ→⊑ᶜ {x = Z} {Z} (⊑ˢ-exts lps) eq = ⊑ᶜ-var refl
⊑ˢ→⊑ᶜ {x = S x} {S y} (⊑ˢ-σ₀ x₁) eq = ⊑ᶜ-var (suc-injective eq)
⊑ˢ→⊑ᶜ {x = S x} {S y} (⊑ˢ-exts lps) eq = S-pres-prec (⊑ˢ→⊑ᶜ lps (suc-injective eq))

{-
  Substitution (σ on the left and σ′ on the right hand side) preserves term precision.
-}
subst-pres-prec : ∀ {Γ Γ′ Δ Δ′ A A′} {σ : Subst Γ Δ} {σ′ : Subst Γ′ Δ′} {N : Γ ⊢ A} {N′ : Γ′ ⊢ A′}
  → Γ , Δ , Γ′ , Δ′ ⊢ σ ⊑ˢ σ′
  → Γ , Γ′ ⊢ N ⊑ᶜ N′
    ------------------------------
  → Δ , Δ′ ⊢ subst σ N ⊑ᶜ subst σ′ N′
subst-pres-prec lps ⊑ᶜ-prim = ⊑ᶜ-prim
subst-pres-prec (⊑ˢ-σ₀ lpM) (⊑ᶜ-var {x = Z} {Z} eq) = lpM
subst-pres-prec (⊑ˢ-σ₀ lpM) (⊑ᶜ-var {x = S x} {S y} eq) = ⊑ᶜ-var (suc-injective eq)
subst-pres-prec (⊑ˢ-exts lps) (⊑ᶜ-var {x = Z} {Z} eq) = ⊑ᶜ-var refl
subst-pres-prec (⊑ˢ-exts lps) (⊑ᶜ-var {x = S x} {S y} eq) = S-pres-prec (⊑ˢ→⊑ᶜ lps (suc-injective eq))
subst-pres-prec lps (⊑ᶜ-ƛ lp lpN) = ⊑ᶜ-ƛ lp (subst-pres-prec (⊑ˢ-exts lps) lpN)
subst-pres-prec lps (⊑ᶜ-· lpL lpM) =
  ⊑ᶜ-· (subst-pres-prec lps lpL) (subst-pres-prec lps lpM)
subst-pres-prec lps (⊑ᶜ-if lpL lpM lpN) =
  ⊑ᶜ-if (subst-pres-prec lps lpL) (subst-pres-prec lps lpM) (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-cons lpM lpN) =
  ⊑ᶜ-cons (subst-pres-prec lps lpM) (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-fst lpN) = ⊑ᶜ-fst (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-snd lpN) = ⊑ᶜ-snd (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-inl lp lpN) = ⊑ᶜ-inl lp (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-inr lp lpN) = ⊑ᶜ-inr lp (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-case lpL lpM lpN) =
  ⊑ᶜ-case (subst-pres-prec lps lpL) (subst-pres-prec lps lpM) (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-cast lp1 lp2 lpN)  = ⊑ᶜ-cast  lp1 lp2 (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-castl lp1 lp2 lpN) = ⊑ᶜ-castl lp1 lp2 (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-castr lp1 lp2 lpN) = ⊑ᶜ-castr lp1 lp2 (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-wrap lpi lpN)  = ⊑ᶜ-wrap  lpi (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-wrapl lpi lpN) = ⊑ᶜ-wrapl lpi (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-wrapr lpi lpN) = ⊑ᶜ-wrapr lpi (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-blame lp) = ⊑ᶜ-blame lp
