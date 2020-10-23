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
open import GroundInertX using (Cast; cast; Inert; Active; Cross; applyCast; pcs; cs; dom; cod; fstC; sndC; inlC; inrC; compile)
open import Types
open import Variables
open import Labels

open import GTLC
import ParamCastCalculus
open ParamCastCalculus Cast
import ParamCastAux
open ParamCastAux pcs using (Value; Frame; plug; canonical⋆)
import ParamCastReduction
open ParamCastReduction cs
open import TermPrecision

open Value
open Frame


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
fst-pres-⊑blame (⊑ᶜ-blame (pair⊑ lp₁ lp₂)) = ⊑ᶜ-blame lp₁

blame⋢V : ∀ {Γ Γ′ A A′} {V : Γ′ ⊢ A′} {ℓ}
  → Value V
    ----------------------------------
  → ¬ (Γ , Γ′ ⊢ blame {Γ} {A} ℓ ⊑ᶜ V)
blame⋢V (ParamCastAux.V-cast v) (⊑ᶜ-castr _ _ lp) = blame⋢V v lp

eq-—↠ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ≡ N
  → M —↠ N
eq-—↠ {M = M} {N} eq rewrite eq = N ∎


-- applyCast-pres-⊑V : ∀ {Γ Γ′ S T T′} {V : Γ ⊢ S} {V′ : Γ′ ⊢ T′} {vV : Value V} {c : Cast (S ⇒ T)}
--   → Value V′ → (a : Active c)
--   → S ⊑ T′ → T ⊑ T′
--   → Γ , Γ′ ⊢ V ⊑ᶜ V′
--     ------------------------------------
--   → Γ , Γ′ ⊢ applyCast V vV c {a} ⊑ᶜ V′
-- applyCast-pres-⊑V _ (Active.activeId (cast A .A _)) lp1 lp2 ⊑ᶜ-prim = ⊑ᶜ-prim
-- applyCast-pres-⊑V _ (Active.activeId (cast A .A _)) _ _ (⊑ᶜ-cast lp1 lp2 lpV) = ⊑ᶜ-cast lp1 lp2 lpV
-- applyCast-pres-⊑V _ (Active.activeId (cast A .A _)) _ _ (⊑ᶜ-castl lp1 lp2 lpV) = ⊑ᶜ-castl lp1 lp2 lpV
-- applyCast-pres-⊑V _ (Active.activeId (cast A .A _)) _ _ (⊑ᶜ-castr lp1 lp2 lpV) = ⊑ᶜ-castr lp1 lp2 lpV
-- applyCast-pres-⊑V {V = V} {vV = vV} _ (Active.activeProj (cast ⋆ T _) neq) lp1 lp2 (⊑ᶜ-cast {c = cast A ⋆ _} {cast A′ B′ _ {c~′}} lp3 lp4 lpV)
--   with canonical⋆ V vV
-- ... | ⟨ A₁ , ⟨ M₁ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with cast-eq-inv meq
-- ...   | ⟨ refl , ⟨ refl , refl ⟩ ⟩ with A₁ `~ T
-- ...     | yes _ = ⊑ᶜ-cast lp3 lp2 lpV
-- ...     | no A₁≁T = contradiction (lp-consis c~′ lp3 lp2) A₁≁T
-- applyCast-pres-⊑V {V = V} {vV = vV} _ (Active.activeProj (cast ⋆ T _) neq) lp1 lp2 (⊑ᶜ-castl lp3 lp4 lpV)
--   with canonical⋆ V vV
-- ... | ⟨ A₁ , ⟨ M₁ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with cast-eq-inv meq
-- ...   | ⟨ refl , ⟨ refl , refl ⟩ ⟩ with A₁ `~ T
-- ...     | yes _ = ⊑ᶜ-castl lp3 lp2 lpV
-- ...     | no A₁≁T = contradiction (lp-consis Refl~ lp3 lp2) A₁≁T
-- applyCast-pres-⊑V {V = V} {vV = vV} (ParamCastAux.V-cast {i = i} v) (Active.activeProj (cast ⋆ T _) neq) lp1 lp2 (⊑ᶜ-castr lp3 lp4 lpV)
--   with canonical⋆ V vV
-- ... | ⟨ A₁ , ⟨ M₁ , ⟨ c₁ , ⟨ i₁ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A₁ `~ T
-- ...   | yes _ = {!!}
-- ...   | no _ = {!!}

sim-fst-inert : ∀ {T A A′ B B′} {V : ∅ ⊢ T} {M′ : ∅ ⊢ A′} {N′ : ∅ ⊢ B′} {c : Cast (T ⇒ A `× B)}
  → Value V
  → (i : Inert c)
  → T ⊑ A′ `× B′ → A `× B ⊑ A′ `× B′
  → ∅ , ∅ ⊢ V ⊑ᶜ cons M′ N′
    ----------------------------------------------------
  → ∃[ M ] ((fst (V ⟨ c ⟩) —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ M′))
sim-fst-inert (V-pair vM vN) (Inert.I-pair (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~)) lp1 lp2 (⊑ᶜ-cons {M = M} {N = N} lpV _)
  with lp1 | lp2
... | pair⊑ lp11 lp12 | pair⊑ lp21 lp22 =
    ⟨ M ⟨ fstC (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~) Cross.C-pair ⟩ , ⟨ rd* , (⊑ᶜ-castl lp11 lp21 lpV) ⟩ ⟩
  where
  rd* =
    _
      —→⟨ fst-cast (V-pair vM vN) {Cross.C-pair} ⟩
    _
      —→⟨ ξ {F = F-cast _} (β-fst vM vN) ⟩
    _ ∎
sim-fst-inert (V-cast {i = i₀} vM) (Inert.I-pair (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~)) lp1 lp2 (⊑ᶜ-castl {M = M} {c = c₀} lp3 lp4 lpM)
  with sim-fst-inert vM i₀ lp3 lp1 lpM | lp2 | lp4
... | ⟨ M₁ , ⟨ rd* , lpM₁ ⟩ ⟩ | pair⊑ lp21 lp22 | pair⊑ lp41 lp42 =
  ⟨ (M₁ ⟨ fstC (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~) Cross.C-pair ⟩) , ⟨ rd*′ , ⊑ᶜ-castl lp41 lp21 lpM₁ ⟩ ⟩
  where
  rd*′ =
    _
      —→⟨ fst-cast (V-cast {i = i₀} vM) {Cross.C-pair} ⟩
    -- By congruence of multi-step reduction.
    plug-cong (F-cast _) rd*

applyCast-castl : ∀ {Γ Γ′ A A′ B B′} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
  → (vV : Value V) → Value V′
  → (a : Active c) → Inert c′
  → A ⊑ A′ → B ⊑ B′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
    -------------------------------------------
  → Γ , Γ′ ⊢ applyCast V vV c {a} ⊑ᶜ V′ ⟨ c′ ⟩
applyCast-castl _ _ (Active.A-id c) (Inert.I-inj x c₁) lp1 lp2 ⊑ᶜ-prim = ⊑ᶜ-castr lp1 lp2 ⊑ᶜ-prim
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-ƛ x lpV) = {!!}
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-cons lpV lpV₁) = {!!}
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-inl lpV) = {!!}
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-inr lpV) = {!!}
applyCast-castl vV vV′ (Active.A-id c) _ lp1 lp2 (⊑ᶜ-cast x x₁ lpV) = ⊑ᶜ-castr x₁ lp2 (⊑ᶜ-cast x x₁ lpV)
applyCast-castl {c′ = cast _ _ _ c~′} vV vV′ (Active.A-proj (cast ⋆ B _ _) x₂) i lp1 lp2 (⊑ᶜ-cast x x₁ lpV)
  with ground? B
... | yes b-g with canonical⋆ _ vV
...   | ⟨ G , ⟨ V₁ , ⟨ c₁ , ⟨ i₁ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq
  with gnd-eq? G B {GroundInertX.inert-ground c₁ i₁} {b-g}
...     | yes ap-b = {!!}
...     | no  ap-b = {!!}
applyCast-castl {c′ = cast _ _ _ c~′} vV vV′ (Active.A-proj (cast ⋆ B _ _) x₂) i lp1 lp2 (⊑ᶜ-cast x x₁ lpV)
    | no b-ng = {!!}

applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-castl x x₁ lpV) = {!!}
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-castr x x₁ lpV) = {!!}

catchup : ∀ {Γ Γ′ A A′} {M : Γ ⊢ A} {V′ : Γ′ ⊢ A′}
  → Value V′
  → Γ , Γ′ ⊢ M ⊑ᶜ V′
  → ∃[ V ] ((Value V) × (M —↠ V) × (Γ , Γ′ ⊢ V ⊑ᶜ V′))
catchup {M = $ k} v ⊑ᶜ-prim = ⟨ $ k , ⟨ V-const , ⟨ _ ∎ , ⊑ᶜ-prim ⟩ ⟩ ⟩
catchup v (⊑ᶜ-ƛ x lpM) = {!!}
catchup v (⊑ᶜ-cons lpM lpM₁) = {!!}
catchup v (⊑ᶜ-inl lpM) = {!!}
catchup v (⊑ᶜ-inr lpM) = {!!}
catchup (ParamCastAux.V-cast v) (⊑ᶜ-cast {c = c} lp1 lp2 lpM) with catchup v lpM
... | ⟨ V , ⟨ vV , ⟨ rd* , lpV ⟩ ⟩ ⟩ with GroundInertX.ActiveOrInert c
...   | inj₁ a = ⟨ applyCast V vV c {a} , ⟨ {!!} , ⟨ rd*′ , {!!} ⟩ ⟩ ⟩
  where
  rd*′ = ↠-trans (plug-cong (F-cast c) rd*) ( _ —→⟨ _—→_.cast vV {a} ⟩ _ ∎)
...   | inj₂ i = ⟨ V ⟨ c ⟩ , ⟨ ParamCastAux.V-cast {i = i} vV , ⟨ plug-cong (F-cast c) rd* , ⊑ᶜ-cast lp1 lp2 lpV ⟩ ⟩ ⟩
catchup v (⊑ᶜ-castl x x₁ lpM) = {!!}
catchup v (⊑ᶜ-castr x x₁ lpM) = {!!}

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
