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

module ParamGradualGuaranteeAux (csp : CastStructWithPrecision) where

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
  -- this is the more involved case so we prove it in a separate lemma
  with cast-catchup {c = c} vV v′ lp1 lp2 lpV
...   | ⟨ W , ⟨ vW , ⟨ rd*₂ , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ (↠-trans (plug-cong (F-cast _) rd*₁) rd*₂) , lpW ⟩ ⟩ ⟩
catchup (V-wrap v′ i′) (⊑ᶜ-wrap {i = i} lp lpM)
  -- just recur in all 3 wrap cases
  with catchup v′ lpM
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W ⟪ i ⟫ , ⟨ V-wrap vW i , ⟨ plug-cong (F-wrap _) rd* , ⊑ᶜ-wrap lp lpW ⟩ ⟩ ⟩
catchup v′ (⊑ᶜ-wrapl {i = i} lp lpM)
  with catchup v′ lpM
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W ⟪ i ⟫ , ⟨ V-wrap vW i , ⟨ plug-cong (F-wrap _) rd* , ⊑ᶜ-wrapl lp lpW ⟩ ⟩ ⟩
catchup (V-wrap v′ _) (⊑ᶜ-wrapr lp lpM)
  with catchup v′ lpM
... | ⟨ W , ⟨ vW , ⟨ rd* , lpW ⟩ ⟩ ⟩ = ⟨ W , ⟨ vW , ⟨ rd* , ⊑ᶜ-wrapr lp lpW ⟩ ⟩ ⟩

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
rename-pres-prec f (⊑ᶜ-wrap lpi lpM)  = ⊑ᶜ-wrap  lpi (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-wrapl lpi lpM) = ⊑ᶜ-wrapl lpi (rename-pres-prec f lpM)
rename-pres-prec f (⊑ᶜ-wrapr lpi lpM) = ⊑ᶜ-wrapr lpi (rename-pres-prec f lpM)
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
⊑ᶜ→⊑ lp* (⊑ᶜ-wrap lpi lpM) = proj₂ (lpii→⊑ lpi)
⊑ᶜ→⊑ lp* (⊑ᶜ-wrapl lpi lpM) = proj₂ (lpit→⊑ lpi)
⊑ᶜ→⊑ lp* (⊑ᶜ-wrapr lpi lpM) = proj₂ (lpti→⊑ lpi)
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
subst-pres-prec lps (⊑ᶜ-wrap lpi lpN)  = ⊑ᶜ-wrap  lpi (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-wrapl lpi lpN) = ⊑ᶜ-wrapl lpi (subst-pres-prec lps lpN)
subst-pres-prec lps (⊑ᶜ-wrapr lpi lpN) = ⊑ᶜ-wrapr lpi (subst-pres-prec lps lpN)
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
