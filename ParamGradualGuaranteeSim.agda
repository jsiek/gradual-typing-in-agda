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

open import Types
open import Variables
open import Labels
open import CastStructureWithPrecision

module ParamGradualGuaranteeSim (csp : CastStructWithPrecision) where

open CastStructWithPrecision csp

open import ParamCastCalculus Cast Inert
open import ParamCastAux precast
open import ParamCastReduction cs
open import ParamCCPrecision pcsp

cast-eq-inv : ∀ {Γ A A′ B} {M : Γ ⊢ A} {M′ : Γ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B)}
  → M ⟨ c ⟩ ≡ M′ ⟨ c′ ⟩
    --------------------
  → Σ[ eq ∈ (A ≡ A′) ] (subst-eq (λ □ → Cast (□ ⇒ B)) eq c ≡ c′) × (subst-eq (λ □ → Γ ⊢ □) eq M ≡ M′)
cast-eq-inv refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

cast-catchup : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
  → Value V → Value V′
  → A ⊑ A′ → B ⊑ A′
  → Γ , Γ′ ⊢ V ⊑ᶜ V′
    ----------------------------------------------------------
  → ∃[ W ] ((Value W) × (V ⟨ c ⟩ —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
cast-catchup {V = V} {V′} {c} vV vV′ lp1 lp2 lpV
  with ActiveOrInert c
... | inj₁ a
  with applyCast-catchup a vV vV′ lp1 lp2 lpV
...   | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ (_ —→⟨ cast vV {a} ⟩ rd*) , lpW ⟩ ⟩ ⟩
cast-catchup {V = V} {V′} {c} vV vV′ lp1 lp2 lpV | inj₂ i =
  ⟨ V ⟪ i ⟫ , ⟨ (V-wrap vV i) , ⟨ _ —→⟨ wrap vV {i} ⟩ _ ∎ , ⊑ᶜ-wrapl (⊑→lpit i lp1 lp2) lpV ⟩ ⟩ ⟩

{- Catching up on the less precise side. -}
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
  ⟨ cons Vₘ Vₙ , ⟨ V-pair vₘ vₙ ,
    ⟨ ↠-trans (plug-cong (F-×₂ _) rd⋆ₘ) (plug-cong (F-×₁ _ vₘ) rd⋆ₙ) ,
      ⊑ᶜ-cons lpVₘ lpVₙ ⟩ ⟩ ⟩
catchup (V-inl v′) (⊑ᶜ-inl lp lpM)
  with catchup v′ lpM
... | ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ , lpVₘ ⟩ ⟩ ⟩ = ⟨ inl Vₘ , ⟨ V-inl vₘ , ⟨ plug-cong F-inl rd⋆ , ⊑ᶜ-inl lp lpVₘ ⟩ ⟩ ⟩
catchup (V-inr v′) (⊑ᶜ-inr lp lpN)
  with catchup v′ lpN
... | ⟨ Vₙ , ⟨ vₙ , ⟨ rd* , lpVₙ ⟩ ⟩ ⟩ = ⟨ inr Vₙ , ⟨ V-inr vₙ , ⟨ plug-cong F-inr rd* , ⊑ᶜ-inr lp lpVₙ ⟩ ⟩ ⟩
catchup v′ (⊑ᶜ-castl {c = c} lp1 lp2 lpM)
  with catchup v′ lpM
... | ⟨ V , ⟨ vV , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  -- this is the more involved case so we prove it in a separate lemma
  with cast-catchup {c = c} vV v′ lp1 lp2 lpV
...   | ⟨ W , ⟨ vW , ⟨ rd*₂ , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ ↠-trans (plug-cong (F-cast _) rd*₁) rd*₂ , lpW ⟩ ⟩ ⟩
catchup (V-wrap v′ i′) (⊑ᶜ-wrap {i = i} lp lpM imp)
  -- just recur in all 3 wrap cases
  with catchup v′ lpM
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W ⟪ i ⟫ , ⟨ V-wrap vW i , ⟨ plug-cong (F-wrap _) rd* , ⊑ᶜ-wrap lp lpW imp ⟩ ⟩ ⟩
catchup v′ (⊑ᶜ-wrapl {i = i} lp lpM)
  with catchup v′ lpM
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W ⟪ i ⟫ , ⟨ V-wrap vW i , ⟨ plug-cong (F-wrap _) rd* , ⊑ᶜ-wrapl lp lpW ⟩ ⟩ ⟩
catchup (V-wrap v′ _) (⊑ᶜ-wrapr lp lpM A≢⋆)
  with catchup v′ lpM
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ rd* , ⊑ᶜ-wrapr lp lpW A≢⋆ ⟩ ⟩ ⟩

{- Renaming preserves term precision. -}
rename-pres-prec : ∀ {Γ Γ′ Δ Δ′ A A′} {ρ : Rename Γ Δ} {ρ′ : Rename Γ′ Δ′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
  → RenameIso ρ ρ′
  → Γ , Γ′ ⊢ M ⊑ᶜ M′
    ------------------------------------
  → Δ , Δ′ ⊢ rename ρ M ⊑ᶜ rename ρ′ M′
rename-pres-prec f ⊑ᶜ-prim = ⊑ᶜ-prim
rename-pres-prec f (⊑ᶜ-var eq) = ⊑ᶜ-var (f eq)
rename-pres-prec f (⊑ᶜ-ƛ lp lpM) = ⊑ᶜ-ƛ lp (rename-pres-prec (ext-pres-RenameIso f) lpM)
rename-pres-prec f (⊑ᶜ-· lpL lpM) = ⊑ᶜ-· (rename-pres-prec f lpL) (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-if lpL lpM lpN) =
  ⊑ᶜ-if (rename-pres-prec f lpL) (rename-pres-prec f lpM) (rename-pres-prec f lpN)
rename-pres-prec f (⊑ᶜ-cons lpM lpN) =
  ⊑ᶜ-cons (rename-pres-prec f lpM) (rename-pres-prec f lpN)
rename-pres-prec f (⊑ᶜ-fst lpM)    = ⊑ᶜ-fst (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-snd lpM)    = ⊑ᶜ-snd (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-inl lp lpM) = ⊑ᶜ-inl lp (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-inr lp lpM) = ⊑ᶜ-inr lp (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-case lpL lp1 lp2 lpM lpN) =
  ⊑ᶜ-case (rename-pres-prec f lpL) lp1 lp2 (rename-pres-prec (ext-pres-RenameIso f) lpM) (rename-pres-prec (ext-pres-RenameIso f) lpN)
rename-pres-prec f (⊑ᶜ-cast lp1 lp2 lpM)  = ⊑ᶜ-cast  lp1 lp2 (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-castl lp1 lp2 lpM) = ⊑ᶜ-castl lp1 lp2 (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-castr lp1 lp2 lpM) = ⊑ᶜ-castr lp1 lp2 (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-wrap lpi lpM imp)  = ⊑ᶜ-wrap  lpi (rename-pres-prec f lpM) imp
rename-pres-prec f (⊑ᶜ-wrapl lpi lpM) = ⊑ᶜ-wrapl lpi (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-wrapr lpi lpM A≢⋆) = ⊑ᶜ-wrapr lpi (rename-pres-prec f lpM) A≢⋆
rename-pres-prec f (⊑ᶜ-blame lp) = ⊑ᶜ-blame lp

S-pres-prec : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ B} {M′ : Γ′ ⊢ B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      --------------------------------------------------
    → (Γ , A) , (Γ′ , A′) ⊢ rename S_ M ⊑ᶜ rename S_ M′
S-pres-prec {A = A} {A′} lpM = rename-pres-prec (S-iso {A = A} {A′}) lpM


{- Term precision implies type precision. -}
⊑ᶜ→⊑ : ∀ {Γ Γ′ A A′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
  → Γ ⊑* Γ′
  → Γ , Γ′ ⊢ M ⊑ᶜ M′
    -----------------
  → A ⊑ A′
⊑ᶜ→⊑ lp* ⊑ᶜ-prim = Refl⊑
⊑ᶜ→⊑ lp* (⊑ᶜ-var eq) = ⊑*→⊑ _ _ lp* eq
⊑ᶜ→⊑ lp* (⊑ᶜ-ƛ lp lpN) = fun⊑ lp (⊑ᶜ→⊑ (⊑*-, lp lp*) lpN)
⊑ᶜ→⊑ lp* (⊑ᶜ-· lpL lpM) with ⊑ᶜ→⊑ lp* lpL
... | (fun⊑ lp1 lp2) = lp2
⊑ᶜ→⊑ lp* (⊑ᶜ-if lpL lpM lpN) = ⊑ᶜ→⊑ lp* lpN
⊑ᶜ→⊑ lp* (⊑ᶜ-cons lpM lpN) = pair⊑ (⊑ᶜ→⊑ lp* lpM) (⊑ᶜ→⊑ lp* lpN)
⊑ᶜ→⊑ lp* (⊑ᶜ-fst lpM) with ⊑ᶜ→⊑ lp* lpM
... | (pair⊑ lp1 lp2) = lp1
⊑ᶜ→⊑ lp* (⊑ᶜ-snd lpM) with ⊑ᶜ→⊑ lp* lpM
... | (pair⊑ lp1 lp2) = lp2
⊑ᶜ→⊑ lp* (⊑ᶜ-inl lp lpM) = sum⊑ (⊑ᶜ→⊑ lp* lpM) lp
⊑ᶜ→⊑ lp* (⊑ᶜ-inr lp lpM) = sum⊑ lp (⊑ᶜ→⊑ lp* lpM)
⊑ᶜ→⊑ lp* (⊑ᶜ-case lpL lp1 lp2 lpM lpN) = ⊑ᶜ→⊑ (⊑*-, lp1 lp*) lpM
⊑ᶜ→⊑ lp* (⊑ᶜ-cast lp1 lp2 lpM) = lp2
⊑ᶜ→⊑ lp* (⊑ᶜ-castl lp1 lp2 lpM) = lp2
⊑ᶜ→⊑ lp* (⊑ᶜ-castr lp1 lp2 lpM) = lp2
⊑ᶜ→⊑ lp* (⊑ᶜ-wrap lpi lpM imp) = proj₂ (lpii→⊑ lpi)
⊑ᶜ→⊑ lp* (⊑ᶜ-wrapl lpi lpM) = proj₂ (lpit→⊑ lpi)
⊑ᶜ→⊑ lp* (⊑ᶜ-wrapr lpi lpM A≢⋆) = proj₂ (lpti→⊑ lpi)
⊑ᶜ→⊑ lp* (⊑ᶜ-blame lp) = lp

{- Substitution precision implies term precision: σ ⊑ σ′ → σ x ⊑ σ y if x ≡ y . -}
⊑ˢ→⊑ᶜ : ∀ {Γ Γ′ Δ Δ′ A A′} {σ : Subst Γ Δ} {σ′ : Subst Γ′ Δ′} {x : Γ ∋ A} {y : Γ′ ∋ A′}
  → Γ , Δ , Γ′ , Δ′ ⊢ σ ⊑ˢ σ′
  → ∋→ℕ x ≡ ∋→ℕ y
    --------------------------
  → Δ , Δ′ ⊢ σ x ⊑ᶜ σ′ y
⊑ˢ→⊑ᶜ {x = Z} {Z} (⊑ˢ-σ₀ lpM) eq = lpM
⊑ˢ→⊑ᶜ {x = Z} {Z} (⊑ˢ-exts lps) eq = ⊑ᶜ-var refl
⊑ˢ→⊑ᶜ {x = S x} {S y} (⊑ˢ-σ₀ x₁) eq = ⊑ᶜ-var (suc-injective eq)
⊑ˢ→⊑ᶜ {x = S x} {S y} (⊑ˢ-exts lps) eq = S-pres-prec (⊑ˢ→⊑ᶜ lps (suc-injective eq))


{- Substitution preserves term precision. -}
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
subst-pres-prec lps (⊑ᶜ-case lpL lp1 lp2 lpM lpN) =
  ⊑ᶜ-case (subst-pres-prec lps lpL) lp1 lp2 (subst-pres-prec (⊑ˢ-exts lps) lpM) (subst-pres-prec (⊑ˢ-exts lps) lpN)
subst-pres-prec lps (⊑ᶜ-cast lp1 lp2 lpN)  = ⊑ᶜ-cast  lp1 lp2 (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-castl lp1 lp2 lpN) = ⊑ᶜ-castl lp1 lp2 (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-castr lp1 lp2 lpN) = ⊑ᶜ-castr lp1 lp2 (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-wrap lpi lpN imp)  = ⊑ᶜ-wrap  lpi (subst-pres-prec lps lpN) imp
subst-pres-prec lps (⊑ᶜ-wrapl lpi lpN) = ⊑ᶜ-wrapl lpi (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-wrapr lpi lpN A≢⋆) = ⊑ᶜ-wrapr lpi (subst-pres-prec lps lpN) A≢⋆
subst-pres-prec lps (⊑ᶜ-blame lp) = ⊑ᶜ-blame lp


cast-Z-⊑ : ∀ {A B A′ X X′} {M : ∅ , A ⊢ X} {M′ : ∅ , A′ ⊢ X′} {c : Cast (B ⇒ A)}
  → A ⊑ A′ → B ⊑ A′
  → (∅ , A) , (∅ , A′) ⊢ M ⊑ᶜ M′
    -----------------------------------------------------------
  → (∅ , B) , (∅ , A′) ⊢ rename (ext S_) M [ ` Z ⟨ c ⟩ ] ⊑ᶜ M′
cast-Z-⊑ {A} {B} {A′} {M = M} {M′} {c} lp1 lp2 lpM = subst-eq (λ □ → _ , _ ⊢ _ ⊑ᶜ □) eq lp-rename
  where
  lp-rename : (∅ , B) , (∅ , A′) ⊢ rename (ext S_) M [ ` Z ⟨ c ⟩ ] ⊑ᶜ rename (ext S_) M′ [ ` Z ]
  lp-rename = subst-pres-prec (⊑ˢ-σ₀ (⊑ᶜ-castl lp2 lp1 (⊑ᶜ-var refl)))
                              (rename-pres-prec (ext-pres-RenameIso (S-iso {A = B} {A′ = A′})) lpM)
  eq : rename (ext S_) M′ [ ` Z ] ≡ M′
  eq = sym (substitution-Z-eq M′)

⊑-cast-Z : ∀ {A A′ B′ X X′} {M : ∅ , A ⊢ X} {M′ : ∅ , A′ ⊢ X′} {c′ : Cast (B′ ⇒ A′)}
  → A ⊑ A′ → A ⊑ B′
  → (∅ , A) , (∅ , A′) ⊢ M ⊑ᶜ M′
    ------------------------------
  → (∅ , A) , (∅ , B′) ⊢ M ⊑ᶜ rename (ext S_) M′ [ ` Z ⟨ c′ ⟩ ]
⊑-cast-Z {A} {A′} {B′} {M = M} {M′} {c′} lp1 lp2 lpM = subst-eq (λ □ → _ , _ ⊢ □ ⊑ᶜ _) eq lp-rename
  where
  lp-rename : (∅ , A) , (∅ , B′) ⊢ rename (ext S_) M [ ` Z ] ⊑ᶜ rename (ext S_) M′ [ ` Z ⟨ c′ ⟩ ]
  lp-rename = subst-pres-prec (⊑ˢ-σ₀ (⊑ᶜ-castr lp2 lp1 (⊑ᶜ-var refl)))
                              (rename-pres-prec (ext-pres-RenameIso (S-iso {A = A} {A′ = B′})) lpM)
  eq : rename (ext S_) M [ ` Z ] ≡ M
  eq = sym (substitution-Z-eq M)

sim-if-true : ∀ {A A′} {L : ∅ ⊢ ` 𝔹} {M N : ∅ ⊢ A} {M′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ L ⊑ᶜ ($ true) {P-Base} → ∅ , ∅ ⊢ M ⊑ᶜ M′
    --------------------------------------------------
  → ∃[ K ] ((if L M N —↠ K) × (∅ , ∅ ⊢ K ⊑ᶜ M′))
sim-if-true {M = M} {N} lpL lpM
  with catchup V-const lpL
... | ⟨ ($ true) {P-Base} , ⟨ V-const , ⟨ rd* , lpV ⟩ ⟩ ⟩ =
  ⟨ M , ⟨ ↠-trans (plug-cong (F-if M N) rd*) (_ —→⟨ β-if-true ⟩ _ ∎) , lpM ⟩ ⟩
... | ⟨ V ⟪ i ⟫ , ⟨ V-wrap v .i , ⟨ rd* , lpVi ⟩ ⟩ ⟩ = contradiction i (baseNotInert _)

sim-if-false : ∀ {A A′} {L : ∅ ⊢ ` 𝔹} {M N : ∅ ⊢ A} {N′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ L ⊑ᶜ ($ false) {P-Base} → ∅ , ∅ ⊢ N ⊑ᶜ N′
    ---------------------------------------------------
  → ∃[ K ] ((if L M N —↠ K) × (∅ , ∅ ⊢ K ⊑ᶜ N′))
sim-if-false {M = M} {N} lpL lpN
  with catchup V-const lpL
... | ⟨ ($ false) {P-Base} , ⟨ V-const , ⟨ rd* , lpV ⟩ ⟩ ⟩ =
  ⟨ N , ⟨ ↠-trans (plug-cong (F-if M N) rd*) (_ —→⟨ β-if-false ⟩ _ ∎) , lpN ⟩ ⟩
... | ⟨ V ⟪ i ⟫ , ⟨ V-wrap v .i , ⟨ rd* , lpVi ⟩ ⟩ ⟩ = contradiction i (baseNotInert _)

private
  sim-case-caseL-v : ∀ {A A′ B B′ C C′} {L : ∅ ⊢ A `⊎ B} {M : ∅ , A ⊢ C} {N : ∅ , B ⊢ C}
                                        {V′ : ∅ ⊢ A′} {M′ : ∅ , A′ ⊢ C′} {N′ : ∅ , B′ ⊢ C′}
    → Value L → Value V′
    → A ⊑ A′ → B ⊑ B′
    → ∅ , ∅ ⊢ L ⊑ᶜ inl {B = B′} V′ → (∅ , A) , (∅ , A′) ⊢ M ⊑ᶜ M′ → (∅ , B) , (∅ , B′) ⊢ N ⊑ᶜ N′
      --------------------------------------------------------
    → ∃[ K ] ((case L M N —↠ K) × (∅ , ∅ ⊢ K ⊑ᶜ M′ [ V′ ]))
  sim-case-caseL-v (V-inl v) v′ lp1 lp2 (⊑ᶜ-inl _ lpV) lpM lpN =
    ⟨ _ , ⟨ _ —→⟨ β-caseL v ⟩ _ ∎ , subst-pres-prec (⊑ˢ-σ₀ lpV) lpM ⟩ ⟩
  sim-case-caseL-v (V-wrap {c = c} v i) v′ lp1 lp2 (⊑ᶜ-wrapl lpit lpV) lpM lpN
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , sum⊑ lp21 lp22 ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ sum⊑ lp₁₁ lp₁₂ , sum⊑ lp₂₁ lp₂₂ ⟩ =
    let x = proj₁ (Inert-Cross⊎ _ i)
        cₗ = inlC _ x
        cᵣ = inrC _ x
        ⟨ K , ⟨ rd* , lpK ⟩ ⟩ =
          sim-case-caseL-v v v′ lp₁₁ lp₁₂ lpV (cast-Z-⊑ {c = cₗ} lp1 lp₁₁ lpM)
                                              (cast-Z-⊑ {c = cᵣ} lp2 lp₁₂ lpN) in
      ⟨ K , ⟨ _ —→⟨ case-cast v {x} ⟩ rd* , lpK ⟩ ⟩

sim-case-caseL : ∀ {A A′ B B′ C C′} {L : ∅ ⊢ A `⊎ B} {M : ∅ , A ⊢ C} {N : ∅ , B ⊢ C}
                                    {V′ : ∅ ⊢ A′} {M′ : ∅ , A′ ⊢ C′} {N′ : ∅ , B′ ⊢ C′}
  → Value V′
  → A ⊑ A′ → B ⊑ B′
  → ∅ , ∅ ⊢ L ⊑ᶜ inl {B = B′} V′ → (∅ , A) , (∅ , A′) ⊢ M ⊑ᶜ M′ → (∅ , B) , (∅ , B′) ⊢ N ⊑ᶜ N′
    --------------------------------------------------------
  → ∃[ K ] ((case L M N —↠ K) × (∅ , ∅ ⊢ K ⊑ᶜ M′ [ V′ ]))
sim-case-caseL v′ lp1 lp2 lpL lpM lpN
  with catchup (V-inl v′) lpL
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with sim-case-caseL-v v v′ lp1 lp2 lpV lpM lpN
...   | ⟨ K , ⟨ rd*₂ , lpK ⟩ ⟩ = ⟨ K , ⟨ ↠-trans (plug-cong (F-case _ _) rd*₁) rd*₂ , lpK ⟩ ⟩

private
  sim-case-caseR-v : ∀ {A A′ B B′ C C′} {L : ∅ ⊢ A `⊎ B} {M : ∅ , A ⊢ C} {N : ∅ , B ⊢ C}
                                        {V′ : ∅ ⊢ B′} {M′ : ∅ , A′ ⊢ C′} {N′ : ∅ , B′ ⊢ C′}
    → Value L → Value V′
    → A ⊑ A′ → B ⊑ B′
    → ∅ , ∅ ⊢ L ⊑ᶜ inr {A = A′} V′ → (∅ , A) , (∅ , A′) ⊢ M ⊑ᶜ M′ → (∅ , B) , (∅ , B′) ⊢ N ⊑ᶜ N′
      --------------------------------------------------------
    → ∃[ K ] ((case L M N —↠ K) × (∅ , ∅ ⊢ K ⊑ᶜ N′ [ V′ ]))
  sim-case-caseR-v (V-inr v) v′ lp1 lp2 (⊑ᶜ-inr _ lpV) lpM lpN =
    ⟨ _ , ⟨ _ —→⟨ β-caseR v ⟩ _ ∎ , subst-pres-prec (⊑ˢ-σ₀ lpV) lpN ⟩ ⟩
  sim-case-caseR-v (V-wrap {c = c} v i) v′ lp1 lp2 (⊑ᶜ-wrapl lpit lpV) lpM lpN
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , sum⊑ lp21 lp22 ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ sum⊑ lp₁₁ lp₁₂ , sum⊑ lp₂₁ lp₂₂ ⟩ =
    let x = proj₁ (Inert-Cross⊎ _ i)
        cₗ = inlC _ x
        cᵣ = inrC _ x
        ⟨ K , ⟨ rd* , lpK ⟩ ⟩ =
          sim-case-caseR-v v v′ lp₁₁ lp₁₂ lpV (cast-Z-⊑ {c = cₗ} lp1 lp₁₁ lpM)
                                              (cast-Z-⊑ {c = cᵣ} lp2 lp₁₂ lpN) in
      ⟨ K , ⟨ _ —→⟨ case-cast v {x} ⟩ rd* , lpK ⟩ ⟩

sim-case-caseR : ∀ {A A′ B B′ C C′} {L : ∅ ⊢ A `⊎ B} {M : ∅ , A ⊢ C} {N : ∅ , B ⊢ C}
                                    {V′ : ∅ ⊢ B′} {M′ : ∅ , A′ ⊢ C′} {N′ : ∅ , B′ ⊢ C′}
  → Value V′
  → A ⊑ A′ → B ⊑ B′
  → ∅ , ∅ ⊢ L ⊑ᶜ inr {A = A′} V′ → (∅ , A) , (∅ , A′) ⊢ M ⊑ᶜ M′ → (∅ , B) , (∅ , B′) ⊢ N ⊑ᶜ N′
    --------------------------------------------------------
  → ∃[ K ] ((case L M N —↠ K) × (∅ , ∅ ⊢ K ⊑ᶜ N′ [ V′ ]))
sim-case-caseR v′ lp1 lp2 lpL lpM lpN
  with catchup (V-inr v′) lpL
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with sim-case-caseR-v v v′ lp1 lp2 lpV lpM lpN
...   | ⟨ K , ⟨ rd*₂ , lpK ⟩ ⟩ = ⟨ K , ⟨ ↠-trans (plug-cong (F-case _ _) rd*₁) rd*₂ , lpK ⟩ ⟩

private
  sim-fst-cons-v : ∀ {A A′ B B′} {V : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A′} {W′ : ∅ ⊢ B′}
    → Value V → Value V′ → Value W′
    → ∅ , ∅ ⊢ V ⊑ᶜ cons V′ W′
      ------------------------------------------
    → ∃[ M ] ((fst V —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ V′))
  sim-fst-cons-v (V-pair {V = V} {W} v w) v′ w′ (⊑ᶜ-cons lpV lpW) =
    ⟨ V , ⟨ _ —→⟨ β-fst v w ⟩ _ ∎ , lpV ⟩ ⟩
  sim-fst-cons-v (V-wrap {V = V} {c} v i) v′ w′ (⊑ᶜ-wrapl lpit lpV)
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , pair⊑ lp21 lp22 ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ pair⊑ lp₁₁ lp₁₂ , pair⊑ lp₂₁ lp₂₂ ⟩
    with sim-fst-cons-v v v′ w′ lpV
  ...   | ⟨ M , ⟨ rd* , lpM ⟩ ⟩ =
    let x = proj₁ (Inert-Cross× _ i) in
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
...   | ⟨ M , ⟨ rd*₂ , lpM ⟩ ⟩ = ⟨ M , ⟨ ↠-trans (plug-cong F-fst rd*₁) rd*₂ , lpM ⟩ ⟩

private
  sim-snd-cons-v : ∀ {A A′ B B′} {V : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A′} {W′ : ∅ ⊢ B′}
    → Value V → Value V′ → Value W′
    → ∅ , ∅ ⊢ V ⊑ᶜ cons V′ W′
      ------------------------------------------
    → ∃[ M ] ((snd V —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ W′))
  sim-snd-cons-v (V-pair {V = V} {W} v w) v′ w′ (⊑ᶜ-cons lpV lpW) = ⟨ W , ⟨ _ —→⟨ β-snd v w ⟩ _ ∎ , lpW ⟩ ⟩
  sim-snd-cons-v (V-wrap {V = V} {c} v i) v′ w′ (⊑ᶜ-wrapl lpit lpV)
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , pair⊑ lp21 lp22 ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ pair⊑ lp₁₁ lp₁₂ , pair⊑ lp₂₁ lp₂₂ ⟩
    with sim-snd-cons-v v v′ w′ lpV
  ...   | ⟨ M , ⟨ rd* , lpM ⟩ ⟩ =
    let x = proj₁ (Inert-Cross× _ i) in
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
...   | ⟨ M , ⟨ rd*₂ , lpM ⟩ ⟩ = ⟨ M , ⟨ ↠-trans (plug-cong F-snd rd*₁) rd*₂ , lpM ⟩ ⟩

private
  sim-fst-wrap-v : ∀ {A B A₁′ B₁′ A₂′ B₂′} {V : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A₁′ `× B₁′}
                                           {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
    → Value V → Value V′
    → (i′ : Inert c′) → (x′ : Cross c′)
    → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
      ------------------------------------------------------------------
    → ∃[ M ] ((fst V —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ (fst V′) ⟨ fstC c′ x′ ⟩))
  sim-fst-wrap-v (V-wrap {V = V} {c} v i) v′ i′ x′ (⊑ᶜ-wrap lpii lpV imp)
    with lpii→⊑ lpii
  ... | ⟨ unk⊑ , pair⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ pair⊑ lp₁₁ lp₁₂ , pair⊑ lp₂₁ lp₂₂ ⟩ =
    let x = proj₁ (Inert-Cross× _ i) in
      ⟨ (fst V) ⟨ fstC c x ⟩ , ⟨ _ —→⟨ fst-cast v {x} ⟩ _ ∎ , (⊑ᶜ-cast lp₁₁ lp₂₁ (⊑ᶜ-fst lpV)) ⟩ ⟩
  sim-fst-wrap-v (V-wrap {V = V} {c} v i) v′ i′ x′ (⊑ᶜ-wrapl lpit lpV)
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , pair⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ pair⊑ lp₁₁ lp₁₂ , pair⊑ lp₂₁ lp₂₂ ⟩
    with sim-fst-wrap-v v v′ i′ x′ lpV
  ...   | ⟨ M , ⟨ rd* , lpM ⟩ ⟩ =
    let x = proj₁ (Inert-Cross× _ i) in
      ⟨ M ⟨ fstC c x ⟩ , ⟨ _ —→⟨ fst-cast v {x} ⟩ plug-cong (F-cast _) rd* , ⊑ᶜ-castl lp₁₁ lp₂₁ lpM ⟩ ⟩
  sim-fst-wrap-v {V = V} v v′ i′ x′ (⊑ᶜ-wrapr lpti lpV A≢⋆)
    with lpti→⊑ lpti
  ... | ⟨ pair⊑ lp₁₁ lp₁₂ , pair⊑ lp₂₁ lp₂₂ ⟩ = ⟨ fst V , ⟨ fst V ∎ , ⊑ᶜ-castr lp₁₁ lp₂₁ (⊑ᶜ-fst lpV) ⟩ ⟩

sim-fst-wrap : ∀ {A B A₁′ B₁′ A₂′ B₂′} {N : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A₁′ `× B₁′}
                                       {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
  → Value V′ → (i′ : Inert c′) → (x′ : Cross c′)
  → ∅ , ∅ ⊢ N ⊑ᶜ V′ ⟪ i′ ⟫
    ------------------------------------------------------------------
  → ∃[ M ] ((fst N —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ (fst V′) ⟨ fstC c′ x′ ⟩))
sim-fst-wrap v′ i′ x′ lpN
  with catchup (V-wrap v′ i′) lpN
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with sim-fst-wrap-v v v′ i′ x′ lpV
...   | ⟨ M , ⟨ rd*₂ , lpM ⟩ ⟩ = ⟨ M , ⟨ ↠-trans (plug-cong F-fst rd*₁) rd*₂ , lpM ⟩ ⟩

private
  sim-snd-wrap-v : ∀ {A B A₁′ B₁′ A₂′ B₂′} {V : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A₁′ `× B₁′}
                                           {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
    → Value V → Value V′
    → (i′ : Inert c′) → (x′ : Cross c′)
    → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
      ------------------------------------------------------------------
    → ∃[ M ] ((snd V —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ (snd V′) ⟨ sndC c′ x′ ⟩))
  sim-snd-wrap-v (V-wrap {V = V} {c} v i) v′ i′ x′ (⊑ᶜ-wrap lpii lpV imp)
    with lpii→⊑ lpii
  ... | ⟨ unk⊑ , pair⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ pair⊑ lp₁₁ lp₁₂ , pair⊑ lp₂₁ lp₂₂ ⟩ =
    let x = proj₁ (Inert-Cross× _ i) in
      ⟨ (snd V) ⟨ sndC c x ⟩ , ⟨ _ —→⟨ snd-cast v {x} ⟩ _ ∎ , (⊑ᶜ-cast lp₁₂ lp₂₂ (⊑ᶜ-snd lpV)) ⟩ ⟩
  sim-snd-wrap-v (V-wrap {V = V} {c} v i) v′ i′ x′ (⊑ᶜ-wrapl lpit lpV)
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , pair⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ pair⊑ lp₁₁ lp₁₂ , pair⊑ lp₂₁ lp₂₂ ⟩
    with sim-snd-wrap-v v v′ i′ x′ lpV
  ...   | ⟨ M , ⟨ rd* , lpM ⟩ ⟩ =
    let x = proj₁ (Inert-Cross× _ i) in
      ⟨ M ⟨ sndC c x ⟩ , ⟨ _ —→⟨ snd-cast v {x} ⟩ plug-cong (F-cast _) rd* , ⊑ᶜ-castl lp₁₂ lp₂₂ lpM ⟩ ⟩
  sim-snd-wrap-v {V = V} v v′ i′ x′ (⊑ᶜ-wrapr lpti lpV A≢⋆)
    with lpti→⊑ lpti
  ... | ⟨ pair⊑ lp₁₁ lp₁₂ , pair⊑ lp₂₁ lp₂₂ ⟩ = ⟨ snd V , ⟨ snd V ∎ , ⊑ᶜ-castr lp₁₂ lp₂₂ (⊑ᶜ-snd lpV) ⟩ ⟩

sim-snd-wrap : ∀ {A B A₁′ B₁′ A₂′ B₂′} {N : ∅ ⊢ A `× B} {V′ : ∅ ⊢ A₁′ `× B₁′} {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
  → Value V′ → (i′ : Inert c′) → (x′ : Cross c′)
  → ∅ , ∅ ⊢ N ⊑ᶜ V′ ⟪ i′ ⟫
    ------------------------------------------------------------------
  → ∃[ M ] ((snd N —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ (snd V′) ⟨ sndC c′ x′ ⟩))
sim-snd-wrap v′ i′ x′ lpN
  with catchup (V-wrap v′ i′) lpN
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with sim-snd-wrap-v v v′ i′ x′ lpV
... | ⟨ M , ⟨ rd*₂ , lpM ⟩ ⟩ = ⟨ M , ⟨ ↠-trans (plug-cong F-snd rd*₁) rd*₂ , lpM ⟩ ⟩


private
  sim-case-wrap-v : ∀ {A B C A₁′ B₁′ A₂′ B₂′ C′}
                      {V : ∅ ⊢ A `⊎ B} {M : ∅ , A ⊢ C} {N : ∅ , B ⊢ C}
                      {V′ : ∅ ⊢ A₁′ `⊎ B₁′} {M′ : ∅ , A₂′ ⊢ C′} {N′ : ∅ , B₂′ ⊢ C′} {c′ : Cast ((A₁′ `⊎ B₁′) ⇒ (A₂′ `⊎ B₂′))}
    → Value V → Value V′ → (i′ : Inert c′) → (x′ : Cross c′)
    → A ⊑ A₂′ → B ⊑ B₂′
    → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫ → (∅ , A) , (∅ , A₂′) ⊢ M ⊑ᶜ M′ → (∅ , B) , (∅ , B₂′) ⊢ N ⊑ᶜ N′
      ------------------------------------------------------------------
    → ∃[ K ] ((case V M N —↠ K) ×
               (∅ , ∅ ⊢ K ⊑ᶜ case V′ (rename (ext S_) M′ [ ` Z ⟨ inlC c′ x′ ⟩ ])
                                     (rename (ext S_) N′ [ ` Z ⟨ inrC c′ x′ ⟩ ])))
  sim-case-wrap-v {A₂′ = A₂′} {B₂′} (V-wrap v i) v′ i′ x′ lp1 lp2 (⊑ᶜ-wrap lpii lpV imp) lpM lpN
    with lpii→⊑ lpii
  ... | ⟨ unk⊑ , sum⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ sum⊑ {A = A₁} {B = B₁} lp₁₁ lp₁₂ , sum⊑ lp₂₁ lp₂₂ ⟩ =
    let x = proj₁ (Inert-Cross⊎ _ i) in
      ⟨ _ , ⟨ _ —→⟨ case-cast v {x} ⟩ _ ∎ ,
              ⊑ᶜ-case lpV lp₁₁ lp₁₂
                      (subst-pres-prec (⊑ˢ-σ₀ (⊑ᶜ-cast lp₁₁ lp₂₁ (⊑ᶜ-var refl)))
                                       (rename-pres-prec (ext-pres-RenameIso (S-iso {A = A₁} {A′ = A₂′})) lpM))
                      (subst-pres-prec (⊑ˢ-σ₀ (⊑ᶜ-cast lp₁₂ lp₂₂ (⊑ᶜ-var refl)))
                                       (rename-pres-prec (ext-pres-RenameIso (S-iso {A = B₁} {A′ = B₂′})) lpN)) ⟩ ⟩
  sim-case-wrap-v {A₂} {B₂} {A₂′ = A₂′} {B₂′} {M = M} {N} {M′ = M′} {N′}
                  (V-wrap {c = c} v i) v′ i′ x′ lp1 lp2 (⊑ᶜ-wrapl lpit lpV) lpM lpN
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , sum⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ sum⊑ {A = A₁} {B = B₁} lp3 lp4 , _ ⟩ =
    let ⟨ K , ⟨ rd* , lpK ⟩ ⟩ = sim-case-wrap-v v v′ i′ x′ lp3 lp4 lpV lpM† lpN† in
      ⟨ K , ⟨ _ —→⟨ case-cast v {x} ⟩ rd* , lpK ⟩ ⟩
    where
    x = proj₁ (Inert-Cross⊎ _ i)
    lpM† : (∅ , A₁) , (∅ , A₂′) ⊢ rename (ext S_) M [ ` Z ⟨ inlC c x ⟩ ] ⊑ᶜ M′
    lpM† = cast-Z-⊑ lp1 lp3 lpM
    lpN† : (∅ , B₁) , (∅ , B₂′) ⊢ rename (ext S_) N [ ` Z ⟨ inrC c x ⟩ ] ⊑ᶜ N′
    lpN† = cast-Z-⊑ lp2 lp4 lpN
  sim-case-wrap-v {A = A} {B} {A₁′ = A₁′} {B₁′} {M = M} {N} {M′ = M′} {N′} {c′}
                  v v′ i′ x′ lp1 lp2 (⊑ᶜ-wrapr lpti lpV A≢⋆) lpM lpN
    with lpti→⊑ lpti
  ... | ⟨ sum⊑ lp₁₁ lp₁₂ , sum⊑ lp₂₁ lp₂₂ ⟩ =
    ⟨ _ , ⟨ _ ∎ , ⊑ᶜ-case lpV lp₁₁ lp₁₂ lpM† lpN† ⟩ ⟩
    where
    lpM† : (∅ , A) , (∅ , A₁′) ⊢ M ⊑ᶜ rename (ext S_) M′ [ ` Z ⟨ inlC c′ x′ ⟩ ]
    lpM† = ⊑-cast-Z lp₂₁ lp₁₁ lpM
    lpN† : (∅ , B) , (∅ , B₁′) ⊢ N ⊑ᶜ rename (ext S_) N′ [ ` Z ⟨ inrC c′ x′ ⟩ ]
    lpN† = ⊑-cast-Z lp₂₂ lp₁₂ lpN

sim-case-wrap : ∀ {A B C A₁′ B₁′ A₂′ B₂′ C′}
                  {L : ∅ ⊢ A `⊎ B} {M : ∅ , A ⊢ C} {N : ∅ , B ⊢ C}
                  {V′ : ∅ ⊢ A₁′ `⊎ B₁′} {M′ : ∅ , A₂′ ⊢ C′} {N′ : ∅ , B₂′ ⊢ C′} {c′ : Cast ((A₁′ `⊎ B₁′) ⇒ (A₂′ `⊎ B₂′))}
  → Value V′ → (i′ : Inert c′) → (x′ : Cross c′)
  → A ⊑ A₂′ → B ⊑ B₂′
  → ∅ , ∅ ⊢ L ⊑ᶜ V′ ⟪ i′ ⟫ → (∅ , A) , (∅ , A₂′) ⊢ M ⊑ᶜ M′ → (∅ , B) , (∅ , B₂′) ⊢ N ⊑ᶜ N′
    ----------------------------------------
  → ∃[ K ] ((case L M N —↠ K) ×
             (∅ , ∅ ⊢ K ⊑ᶜ case V′ (rename (ext S_) M′ [ ` Z ⟨ inlC c′ x′ ⟩ ])
                                   (rename (ext S_) N′ [ ` Z ⟨ inrC c′ x′ ⟩ ])))
sim-case-wrap v′ i′ x′ lp1 lp2 lpL lpM lpN
  with catchup (V-wrap v′ i′) lpL
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with sim-case-wrap-v v v′ i′ x′ lp1 lp2 lpV lpM lpN
...   | ⟨ K , ⟨ rd*₂ , lpK ⟩ ⟩ = ⟨ K , ⟨ ↠-trans (plug-cong (F-case _ _) rd*₁) rd*₂ , lpK ⟩ ⟩


private
  sim-app-δ-v : ∀ {A A′ B B′} {L : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A} {f : rep A′ → rep B′} {k : rep A′}
                  {ab : Prim (A′ ⇒ B′)} {a : Prim A′} {b : Prim B′}
    → Value L → Value M
    → ∅ , ∅ ⊢ L ⊑ᶜ ($ f) {ab}
    → ∅ , ∅ ⊢ M ⊑ᶜ ($ k) {a}
      ----------------------------------------
    → ∃[ N ] ((L · M —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ ($ f k) {b}))
  sim-app-δ-v {f = f} {k} V-const V-const ⊑ᶜ-prim ⊑ᶜ-prim =
    ⟨ $ f k , ⟨ _ —→⟨ δ ⟩ _ ∎ , ⊑ᶜ-prim ⟩ ⟩
  sim-app-δ-v {ab = P-Fun _} V-const (V-wrap vM i) ⊑ᶜ-prim (⊑ᶜ-wrapl lpi lpM) = contradiction i (baseNotInert _)
  sim-app-δ-v {b = b} (V-wrap {c = c} vV i) vM (⊑ᶜ-wrapl lpit lpV) lpM
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , fun⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ fun⊑ lp₁₁ lp₁₂ , fun⊑ lp₂₁ lp₂₂ ⟩ =
    {-
      Starting from V ⟪ c ⟫ · M, first we go to (V · (M ⟨ dom c ⟩)) ⟨ cod c ⟩ by `fun-cast`.
      Then we proceed on M ⟨ dom c ⟩ by `catchup` and step to a value W there.
      At this point we have (V · W) ⟨ cod c ⟩ so we make recursive call on V, W and use congruence.
    -}
    let x = proj₁ (Inert-Cross⇒ _ i)
        ⟨ W , ⟨ vW , ⟨ rd*₁ , lpW ⟩ ⟩ ⟩ = catchup V-const (⊑ᶜ-castl {c = dom c x} lp₂₁ lp₁₁ lpM)
        ⟨ N , ⟨ rd*₂ , lpN ⟩ ⟩ = sim-app-δ-v {b = b} vV vW lpV lpW in
      ⟨ N ⟨ cod c x ⟩ ,
        ⟨ _ —→⟨ fun-cast vV vM {x} ⟩ ↠-trans (plug-cong (F-cast _) (plug-cong (F-·₂ _ {vV}) rd*₁)) (plug-cong (F-cast _) rd*₂) ,
          ⊑ᶜ-castl lp₁₂ lp₂₂ lpN ⟩ ⟩

sim-app-δ : ∀ {A A′ B B′} {L : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A} {f : rep A′ → rep B′} {k : rep A′}
              {ab : Prim (A′ ⇒ B′)} {a : Prim A′} {b : Prim B′}
  → ∅ , ∅ ⊢ L ⊑ᶜ ($ f) {ab}
  → ∅ , ∅ ⊢ M ⊑ᶜ ($ k) {a}
    ----------------------------------------
  → ∃[ N ] ((L · M —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ ($ f k) {b}))
sim-app-δ {f = f} {k} {ab} {a} {b} lpL lpM
  with catchup (V-const {k = f}) lpL
... | ⟨ V₁ , ⟨ v₁ , ⟨ rd*₁ , lpV₁ ⟩ ⟩ ⟩
  with catchup (V-const {k = k}) lpM
...   | ⟨ V₂ , ⟨ v₂ , ⟨ rd*₂ , lpV₂ ⟩ ⟩ ⟩
  with sim-app-δ-v {b = b} v₁ v₂ lpV₁ lpV₂
...     | ⟨ N , ⟨ rd*₃ , lpN ⟩ ⟩ =
  ⟨ N , ⟨ ↠-trans (plug-cong (F-·₁ _) rd*₁) (↠-trans (plug-cong (F-·₂ _ {v₁}) rd*₂) rd*₃) , lpN ⟩ ⟩


private
  sim-app-β-v : ∀ {A A′ B B′} {L : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A} {N′ : ∅ , A′ ⊢ B′} {M′ : ∅ ⊢ A′}
    → Value L → Value M → Value M′
    → ∅ , ∅ ⊢ L ⊑ᶜ (ƛ N′) → ∅ , ∅ ⊢ M ⊑ᶜ M′
      ------------------------------------------------------
    → ∃[ M₂ ] ((L · M —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ N′ [ M′ ]))
  -- ƛ N ⊑ ƛ N′ . Here we need to prove subst preserves precision.
  sim-app-β-v {M = M} (V-ƛ {N = N}) vM vM′ (⊑ᶜ-ƛ lp lpN) lpM =
    ⟨ N [ M ] , ⟨  _ —→⟨ β vM ⟩ _ ∎ , (subst-pres-prec (⊑ˢ-σ₀ lpM) lpN) ⟩ ⟩
  -- V ⟪ i ⟫ ⊑ ƛ N′
  sim-app-β-v {M = M} (V-wrap {V = V} {c = c} v i) vM vM′ (⊑ᶜ-wrapl lpit lpV) lpM
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , fun⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ fun⊑ lp₁₁ lp₁₂ , fun⊑ lp₂₁ lp₂₂ ⟩ =
    {- The reduction sequence:
      V ⟪ i ⟫ · M —↠ V ⟪ i ⟫ · W —→ (V · W ⟨ dom c ⟩) ⟨ cod c ⟩ —↠ (V · W₁) ⟨ cod c ⟩ —↠ N ⟨ cod c ⟩
    -}
    let x = proj₁ (Inert-Cross⇒ _ i)
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


private
  sim-app-wrap-v : ∀ {A A′ B B′ C′ D′} {V : ∅ ⊢ A ⇒ B} {W : ∅ ⊢ A}
                     {V′ : ∅ ⊢ A′ ⇒ B′} {W′ : ∅ ⊢ C′} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
    → Value V → Value W → Value V′ → Value W′
    → (i′ : Inert c′) → (x′ : Cross c′)
    → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫ → ∅ , ∅ ⊢ W ⊑ᶜ W′
      ----------------------------------------------------------------------------------
    → ∃[ N ] ((V · W —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ (V′ · (W′ ⟨ dom c′ x′ ⟩)) ⟨ cod c′ x′ ⟩))
  -- Case 1
  --     V ⊑ᶜ V′
  --     ---------------------- ⊑ᶜ-wrap
  -- V = V ⟪ i ⟫ ⊑ᶜ V′ ⟪ i′ ⟫
  sim-app-wrap-v {W = W} (V-wrap {c = c} v i) w v′ w′ i′ x′ (⊑ᶜ-wrap {M = V} lpii lpV imp) lpW
    with lpii→⊑ lpii
  ... | ⟨ unk⊑ , fun⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ fun⊑ lp₁₁ lp₁₂ , fun⊑ lp₂₁ lp₂₂ ⟩ =
    let x = proj₁ (Inert-Cross⇒ _ i) in
      -- V ⟨ c ⟩ · W --> (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩
      -- have V ⊑ᶜ V′
      -- have W ⊑ᶜ W′  so W ⟨ dom c x ⟩ ⊑ᶜ W′ ⟨ dom c′ x′ ⟩
      -- 
      -- -------------------------------------------------------------------------------
      -- (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩ ⊑ᶜ (V′ · (W′ ⟨ dom c′ x′ ⟩)) ⟨ cod c′ x′ ⟩))
      ⟨ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩ ,
        ⟨ _ —→⟨ fun-cast v w {x} ⟩ _ ∎ , ⊑ᶜ-cast lp₁₂ lp₂₂ (⊑ᶜ-· lpV (⊑ᶜ-cast lp₂₁ lp₁₁ lpW)) ⟩ ⟩
  -- Case 2
  --     V₁ ⊑ᶜ V′ ⟪ i′ ⟫
  --     ---------------------- ⊑ᶜ-wrapl
  -- V = V₁ ⟪ i ⟫ ⊑ᶜ V′ ⟪ i′ ⟫
  sim-app-wrap-v {W = W} (V-wrap {c = c} v i) w v′ w′ i′ x′ (⊑ᶜ-wrapl {M = V} lpit lpV) lpW
    with lpit→⊑ lpit
  ... | ⟨ unk⊑ , fun⊑ lp₂₁ lp₂₂ ⟩ = contradiction i (projNotInert (λ ()) _)
  ... | ⟨ fun⊑ lp₁₁ lp₁₂ , fun⊑ lp₂₁ lp₂₂ ⟩ =
    let x = proj₁ (Inert-Cross⇒ _ i)
        ⟨ W₁ , ⟨ w₁ , ⟨ rd*₁ , lpW₁ ⟩ ⟩ ⟩ = catchup w′ (⊑ᶜ-castl {c = dom c x} lp₂₁ lp₁₁ lpW)
        --  W<dom c> -->* W₁
        ⟨ N , ⟨ rd*₂ , lpN ⟩ ⟩ = sim-app-wrap-v v w₁ v′ w′ i′ x′ lpV lpW₁ in
        --  V · W₁ -->* N
        -- (V< dom(c) -> cod(c) > · W) --> (V · W<dom(c)>)<cod(c)> -->* (V · W₁)<cod(c)> -->* N<cod(c)>
      ⟨ N ⟨ cod c x ⟩ , 
        ⟨ _ —→⟨ fun-cast v w {x} ⟩ ↠-trans (plug-cong (F-cast _) (plug-cong (F-·₂ _ {v}) rd*₁)) (plug-cong (F-cast _) rd*₂) ,
          ⊑ᶜ-castl lp₁₂ lp₂₂ lpN ⟩ ⟩
  sim-app-wrap-v {V = V} {W} v w v′ w′ i′ x′ (⊑ᶜ-wrapr lpti lpV A≢⋆) lpW
    with lpti→⊑ lpti
  ... | ⟨ fun⊑ lp₁₁ lp₁₂ , fun⊑ lp₂₁ lp₂₂ ⟩ =
    ⟨ V · W , ⟨ V · W ∎ , ⊑ᶜ-castr lp₁₂ lp₂₂ (⊑ᶜ-· lpV (⊑ᶜ-castr lp₂₁ lp₁₁ lpW)) ⟩ ⟩

sim-app-wrap : ∀ {A A′ B B′ C′ D′} {L : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A}
                 {V′ : ∅ ⊢ A′ ⇒ B′} {W′ : ∅ ⊢ C′} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
  → Value V′ → Value W′
  → (i′ : Inert c′) → (x′ : Cross c′)
  → ∅ , ∅ ⊢ L ⊑ᶜ V′ ⟪ i′ ⟫ → ∅ , ∅ ⊢ M ⊑ᶜ W′
    ------------------------------------------------------------------------------------
  → ∃[ N ] ((L · M —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ (V′ · (W′ ⟨ dom c′ x′ ⟩)) ⟨ cod c′ x′ ⟩))
sim-app-wrap v′ w′ i′ x′ lpL lpM
  with catchup (V-wrap v′ i′) lpL
... | ⟨ V , ⟨ v , ⟨ rd*₁ , lpV ⟩ ⟩ ⟩
  with catchup w′ lpM
...   | ⟨ W , ⟨ w , ⟨ rd*₂ , lpW ⟩ ⟩ ⟩
  with sim-app-wrap-v v w v′ w′ i′ x′ lpV lpW
...     | ⟨ N , ⟨ rd*₃ , lpN ⟩ ⟩ =
  ⟨ N , ⟨ ↠-trans (plug-cong (F-·₁ _) rd*₁) (↠-trans (plug-cong (F-·₂ _ {v}) rd*₂) rd*₃) , lpN ⟩ ⟩
