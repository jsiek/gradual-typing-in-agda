
open import Types hiding (_⊔_)
open import Labels
open import Variables
open import CastStructure
import EfficientParamCasts
open import Data.Bool using (true; false)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open Data.Nat.Properties.≤-Reasoning
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Pow2

{-

  The height of casts is monotonically decreasing with reduction.

-}

module PreserveHeight (ecs : EfficientCastStructHeight) where

  open EfficientCastStructHeight ecs
  open EfficientParamCasts (EfficientCastStructHeight.effcast ecs)

  import ParamCastCalculusOrig
  open ParamCastCalculusOrig Cast
  open import EfficientParamCastAux precast

  plug-height : ∀ {Γ A B} (M : Γ ⊢ A) (M′ : Γ ⊢ A) (F : Frame A B)
      → c-height M′ ≤ c-height M
      → c-height (plug M′ F) ≤ c-height (plug M F)
  plug-height M M′ (F-·₁ x) M′≤M = ⊔-mono-≤ M′≤M ≤-refl
  plug-height M M′ (F-·₂ M₁) M′≤M = ⊔-mono-≤ ≤-refl M′≤M
  plug-height M M′ (F-if x x₁) M′≤M = ⊔-mono-≤ (⊔-mono-≤ M′≤M ≤-refl) ≤-refl
  plug-height M M′ (F-×₁ x) M′≤M = ⊔-mono-≤ ≤-refl M′≤M
  plug-height M M′ (F-×₂ x) M′≤M = ⊔-mono-≤ M′≤M ≤-refl
  plug-height M M′ F-fst M′≤M = M′≤M
  plug-height M M′ F-snd M′≤M = M′≤M
  plug-height M M′ F-inl M′≤M = M′≤M
  plug-height M M′ F-inr M′≤M = M′≤M
  plug-height M M′ (F-case x x₁) M′≤M = ⊔-mono-≤ (⊔-mono-≤ M′≤M ≤-refl) ≤-refl

  rename-height : ∀{Γ Δ A} (M : Γ ⊢ A) (ρ : ∀ {C} → Γ ∋ C → Δ ∋ C)
      → c-height M ≡ c-height (rename ρ M)
  rename-height (` x) ρ = refl
  rename-height (ƛ M) ρ rewrite rename-height M (ext ρ) = refl
  rename-height (L · M) ρ rewrite rename-height L ρ | rename-height M ρ = refl
  rename-height ($ x) ρ = refl
  rename-height (if L M N) ρ rewrite rename-height L ρ | rename-height M ρ
     | rename-height N ρ = refl
  rename-height (cons M N) ρ rewrite rename-height M ρ | rename-height N ρ = refl
  rename-height (fst M) ρ rewrite rename-height M ρ = refl
  rename-height (snd M) ρ rewrite rename-height M ρ = refl
  rename-height (inl M) ρ rewrite rename-height M ρ = refl
  rename-height (inr M) ρ rewrite rename-height M ρ = refl
  rename-height (case L M N) ρ rewrite rename-height L ρ | rename-height M ρ
     | rename-height N ρ = refl
  rename-height (M ⟨ c ⟩) ρ rewrite rename-height M ρ = refl
  rename-height (blame ℓ) ρ = refl

  SubstHeight : ∀{Γ Δ} (σ : ∀ {C} → Γ ∋ C → Δ ⊢ C) (m : ℕ) → Set
  SubstHeight {Γ}{Δ} σ m = ∀{C} (x : Γ ∋ C) → c-height (σ x) ≤ m

  SubstHeight-exts : ∀{Γ Δ B} (σ : ∀ {C} → Γ ∋ C → Δ ⊢ C) (m : ℕ) 
        → SubstHeight σ m
        → SubstHeight (exts σ {B = B}) m
  SubstHeight-exts σ m σ≤m Z = z≤n
  SubstHeight-exts {B = B} σ m σ≤m (S ∋x) =
      let eq = rename-height (σ ∋x) S_ in
      ≤-trans (≤-reflexive (sym eq)) (σ≤m ∋x)

  sub-height-3 : ∀ {Γ Δ A B C} (L : Γ ⊢ A)(M : Γ ⊢ B)(N : Γ ⊢ C)(σ : {D : Type} → Γ ∋ D → Δ ⊢ D)(m : ℕ)
      → c-height (subst σ L) ≤ c-height L ⊔ m
      → c-height (subst σ M) ≤ c-height M ⊔ m
      → c-height (subst σ N) ≤ c-height N ⊔ m
      → c-height (subst σ L) ⊔ c-height (subst σ M) ⊔ c-height (subst σ N)
         ≤ ((c-height L ⊔ c-height M) ⊔ c-height N) ⊔ m
  sub-height-3 L M N σ m IH1 IH2 IH3 =
      begin
      c-height (subst σ L) ⊔ c-height (subst σ M) ⊔ c-height (subst σ N)
      ≤⟨ ⊔-mono-≤ (⊔-mono-≤ IH1 IH2) IH3 ⟩
      ((c-height L ⊔ m) ⊔ (c-height M ⊔ m)) ⊔ (c-height N ⊔ m)
      ≤⟨ ≤-reflexive (cong (λ X → X ⊔ (c-height N ⊔ m)) (⊔-assoc (c-height L) _ _)) ⟩
      (c-height L ⊔ (m ⊔ (c-height M ⊔ m))) ⊔ (c-height N ⊔ m)
      ≤⟨ ≤-reflexive (cong (λ X → (c-height L ⊔ X) ⊔ (c-height N ⊔ m)) (⊔-comm m _)) ⟩
      (c-height L ⊔ ((c-height M ⊔ m) ⊔ m)) ⊔ (c-height N ⊔ m)
      ≤⟨ ≤-reflexive (cong (λ X → (c-height L ⊔ X) ⊔ (c-height N ⊔ m)) (⊔-assoc (c-height M) _ _)) ⟩
      (c-height L ⊔ (c-height M ⊔ (m ⊔ m))) ⊔ (c-height N ⊔ m)
      ≤⟨ ≤-reflexive (cong (λ X → (c-height L ⊔ (c-height M ⊔ X)) ⊔ (c-height N ⊔ m)) (⊔-idem m)) ⟩
      (c-height L ⊔ (c-height M ⊔ m)) ⊔ (c-height N ⊔ m)
      ≤⟨ ≤-reflexive (⊔-assoc (c-height L) _ _) ⟩
      c-height L ⊔ ((c-height M ⊔ m) ⊔ (c-height N ⊔ m))
      ≤⟨ ⊔-monoʳ-≤ (c-height L) (≤-reflexive (⊔-assoc (c-height M) _ _)) ⟩
      c-height L ⊔ (c-height M ⊔ (m ⊔ (c-height N ⊔ m)))
      ≤⟨ ⊔-monoʳ-≤ (c-height L) (⊔-monoʳ-≤ (c-height M) (≤-reflexive (⊔-comm m _))) ⟩
      c-height L ⊔ (c-height M ⊔ ((c-height N ⊔ m) ⊔ m))
      ≤⟨ ≤-reflexive (cong (λ X → c-height L ⊔ (c-height M ⊔ X)) (⊔-assoc (c-height N) _ _)) ⟩
      c-height L ⊔ (c-height M ⊔ (c-height N ⊔ (m ⊔ m)))
      ≤⟨ ≤-reflexive (cong (λ X → c-height L ⊔ (c-height M ⊔ (c-height N ⊔ X))) (⊔-idem m)) ⟩
      c-height L ⊔ (c-height M ⊔ (c-height N ⊔ m))
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height L) _ _)) ⟩
      (c-height L ⊔ c-height M) ⊔ (c-height N ⊔ m)
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height L ⊔ c-height M) _ _)) ⟩
      ((c-height L ⊔ c-height M) ⊔ c-height N) ⊔ m
    ∎

  sub-height : ∀{Γ Δ A} (M : Γ ⊢ A) (σ : ∀ {C} → Γ ∋ C → Δ ⊢ C) (m : ℕ)
      → SubstHeight σ m
      → c-height (subst σ M) ≤ c-height M ⊔ m
  sub-height (` x) σ m σ≤m = σ≤m x
  sub-height (ƛ M) σ m σ≤m = sub-height M (exts σ) m (SubstHeight-exts σ m σ≤m)
  sub-height (L · M) σ m σ≤m =
    begin
      c-height (subst σ L) ⊔ c-height (subst σ M)
      ≤⟨ ⊔-mono-≤ (sub-height L σ m σ≤m) (sub-height M σ m σ≤m) ⟩
      (c-height L ⊔ m) ⊔ (c-height M ⊔ m)
      ≤⟨ ≤-reflexive (⊔-assoc (c-height L) m _) ⟩
      c-height L ⊔ (m ⊔ (c-height M ⊔ m))
      ≤⟨ ⊔-monoʳ-≤ (c-height L) (≤-reflexive (⊔-comm m _)) ⟩
      c-height L ⊔ ((c-height M ⊔ m) ⊔ m)
      ≤⟨ ⊔-monoʳ-≤ (c-height L) (≤-reflexive (⊔-assoc (c-height M) _ _)) ⟩
      c-height L ⊔ (c-height M ⊔ (m ⊔ m))
      ≤⟨ ⊔-monoʳ-≤ (c-height L) (⊔-monoʳ-≤ (c-height M) (≤-reflexive (⊔-idem m))) ⟩
      c-height L ⊔ (c-height M ⊔ m)
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height L) _ _)) ⟩
      (c-height L ⊔ c-height M) ⊔ m
    ∎
  sub-height ($ x) σ m σ≤m = z≤n
  sub-height (if L M N) σ m σ≤m =
     sub-height-3 L M N σ m (sub-height L σ m σ≤m) (sub-height M σ m σ≤m)
                            (sub-height N σ m σ≤m)
  sub-height (cons M N) σ m σ≤m =
    begin
      c-height (subst σ M) ⊔ c-height (subst σ N)
      ≤⟨ ⊔-mono-≤ (sub-height M σ m σ≤m) (sub-height N σ m σ≤m) ⟩
      (c-height M ⊔ m) ⊔ (c-height N ⊔ m)
      ≤⟨ ≤-reflexive (⊔-assoc (c-height M) m _) ⟩
      c-height M ⊔ (m ⊔ (c-height N ⊔ m))
      ≤⟨ ⊔-monoʳ-≤ (c-height M) (≤-reflexive (⊔-comm m _)) ⟩
      c-height M ⊔ ((c-height N ⊔ m) ⊔ m)
      ≤⟨ ⊔-monoʳ-≤ (c-height M) (≤-reflexive (⊔-assoc (c-height N) _ _)) ⟩
      c-height M ⊔ (c-height N ⊔ (m ⊔ m))
      ≤⟨ ⊔-monoʳ-≤ (c-height M) (⊔-monoʳ-≤ (c-height N) (≤-reflexive (⊔-idem m))) ⟩
      c-height M ⊔ (c-height N ⊔ m)
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height M) _ _)) ⟩
      (c-height M ⊔ c-height N) ⊔ m
    ∎
  sub-height (fst M) σ m σ≤m = sub-height M σ m σ≤m
  sub-height (snd M) σ m σ≤m = sub-height M σ m σ≤m
  sub-height (inl M) σ m σ≤m = sub-height M σ m σ≤m
  sub-height (inr M) σ m σ≤m = sub-height M σ m σ≤m
  sub-height (case L M N) σ m σ≤m =
     sub-height-3 L M N σ m (sub-height L σ m σ≤m) (sub-height M σ m σ≤m)
                            (sub-height N σ m σ≤m)
  sub-height (M ⟨ c ⟩) σ m σ≤m =
    begin
      c-height (subst σ M) ⊔ height c
      ≤⟨ ⊔-mono-≤ (sub-height M σ m σ≤m) ≤-refl ⟩
      (c-height M ⊔ m) ⊔ height c
      ≤⟨ ≤-reflexive (⊔-assoc (c-height M) _ _) ⟩
      c-height M ⊔ (m ⊔ height c)
      ≤⟨ ⊔-monoʳ-≤ (c-height M) (≤-reflexive (⊔-comm m _)) ⟩
      c-height M ⊔ (height c ⊔ m)
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height M) _ _)) ⟩
      (c-height M ⊔ height c) ⊔ m
    ∎
  sub-height (blame ℓ) σ m σ≤m = z≤n

  subst-height : ∀ {Γ A B} (N : Γ , A ⊢ B) (W : Γ ⊢ A)
      → c-height (N [ W ]) ≤ c-height N ⊔ c-height W
  subst-height N W = sub-height N (subst-zero W) (c-height W) SH
    where
    SH : SubstHeight (subst-zero W) (c-height W)
    SH Z = ≤-refl
    SH (S ∋x) = z≤n

  preserve-height : ∀ {Γ A} {M M′ : Γ ⊢ A} {ctx : ReductionCtx}
       → ctx / M —→ M′ → c-height M′ ≤ c-height M
  preserve-height (ξ {M = M₁}{M₁′}{F} M₁—→M₁′) =
    let IH = preserve-height M₁—→M₁′ in plug-height M₁ M₁′ F IH
  preserve-height (ξ-cast {M = M₁}{M₁′} M₁—→M₁′) =
    let IH = preserve-height M₁—→M₁′ in ⊔-mono-≤ IH ≤-refl
  preserve-height ξ-blame = z≤n
  preserve-height ξ-cast-blame = z≤n
  preserve-height (β{N = N}{W = W} vW) = subst-height N W
  preserve-height δ = z≤n
  preserve-height β-if-true = m≤m⊔n _ _
  preserve-height β-if-false = m≤n⊔m _ _
  preserve-height (β-fst vV vW) = m≤m⊔n _ _
  preserve-height (β-snd vV vW) = m≤n⊔m _ _
  preserve-height (β-caseL {V = V}{L}{M} vV) =
    begin
      c-height L ⊔ c-height V       ≤⟨ ≤-reflexive (⊔-comm (c-height L) _) ⟩ 
      c-height V ⊔ c-height L       ≤⟨ m≤m⊔n _ _ ⟩ 
      (c-height V ⊔ c-height L) ⊔ c-height M
    ∎ 
  preserve-height (β-caseR {V = V}{L}{M} vV) =
    begin
      c-height M ⊔ c-height V       ≤⟨ ≤-reflexive (⊔-comm (c-height M) _) ⟩ 
      c-height V ⊔ c-height M       ≤⟨ ⊔-mono-≤ (m≤m⊔n (c-height V) _) ≤-refl ⟩ 
      (c-height V ⊔ c-height L) ⊔ c-height M
    ∎ 
  preserve-height (cast v) = applyCast-height 
  preserve-height (fun-cast {V = V}{W}{c} vV vW {x}) =
    begin
      (c-height V ⊔ (c-height W ⊔ height (dom c x))) ⊔ height (cod c x)
        ≤⟨ ≤-reflexive (⊔-assoc (c-height V) _ _) ⟩
      c-height V ⊔ ((c-height W ⊔ height (dom c x)) ⊔ height (cod c x))
        ≤⟨ ⊔-monoʳ-≤  (c-height V) (≤-reflexive (⊔-assoc (c-height W) _ _)) ⟩
      c-height V ⊔ (c-height W ⊔ (height (dom c x) ⊔ height (cod c x)))
        ≤⟨ ⊔-monoʳ-≤  (c-height V) (⊔-monoʳ-≤ (c-height W) (⊔-lub dom-height
                                                                    cod-height)) ⟩
      c-height V ⊔ (c-height W ⊔ height c)
        ≤⟨ ⊔-monoʳ-≤  (c-height V) (≤-reflexive (⊔-comm (c-height W) _)) ⟩
      c-height V ⊔ (height c ⊔ c-height W)
        ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height V) _ _)) ⟩
      (c-height V ⊔ height c) ⊔ c-height W
    ∎
  preserve-height (fst-cast {V = V} vV {x}) = ⊔-monoʳ-≤  (c-height V) fst-height
  preserve-height (snd-cast {V = V} vV {x}) = ⊔-monoʳ-≤  (c-height V) snd-height
  preserve-height (case-cast {V = V}{W₁}{W₂}{c} vV {x}) =
    begin
      (c-height V ⊔ (c-height (rename S_ W₁) ⊔ height (inlC c x))) ⊔
                    (c-height (rename S_ W₂) ⊔ height (inrC c x))
      ≤⟨ ⊔-mono-≤ (⊔-monoʳ-≤ (c-height V) (≤-reflexive (⊔-comm (c-height (rename S_ W₁)) _)))
             (≤-reflexive (⊔-comm (c-height (rename S_ W₂)) _)) ⟩
      (c-height V ⊔ (height (inlC c x) ⊔ c-height (rename S_ W₁))) ⊔
                    (height (inrC c x) ⊔ c-height (rename S_ W₂))
      ≤⟨ ≤-reflexive (⊔-assoc (c-height V) _ _) ⟩
      c-height V ⊔ ((height (inlC c x) ⊔ c-height (rename S_ W₁)) ⊔
                    (height (inrC c x) ⊔ c-height (rename S_ W₂)))
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-reflexive (⊔-assoc (height (inlC c x)) _ _)) ⟩
      c-height V ⊔ (height (inlC c x) ⊔ (c-height (rename S_ W₁) ⊔
                    (height (inrC c x) ⊔ c-height (rename S_ W₂))))
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoʳ-≤ (height (inlC c x))
                 (≤-reflexive (sym (⊔-assoc (c-height (rename S_ W₁)) _ _)))) ⟩        
      c-height V ⊔ (height (inlC c x) ⊔ ((c-height (rename S_ W₁) ⊔ height (inrC c x))
                        ⊔ c-height (rename S_ W₂)))
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoʳ-≤ (height (inlC c x)) (⊔-monoˡ-≤ (c-height (rename S_ W₂))
                 (≤-reflexive (⊔-comm (c-height (rename S_ W₁)) _)))) ⟩        
      c-height V ⊔ (height (inlC c x) ⊔ ((height (inrC c x) ⊔ c-height (rename S_ W₁))
                        ⊔ c-height (rename S_ W₂)))
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoʳ-≤ (height (inlC c x)) (≤-reflexive (⊔-assoc (height (inrC c x)) _ _))) ⟩ 
      c-height V ⊔ (height (inlC c x) ⊔ (height (inrC c x)
              ⊔ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂))))
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-reflexive (sym (⊔-assoc (height (inlC c x)) _ _))) ⟩
      c-height V ⊔ ((height (inlC c x) ⊔ height (inrC c x))
              ⊔ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂)))
      ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoˡ-≤ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂))
                 (⊔-lub inlC-height inrC-height)) ⟩
      c-height V ⊔ (height c ⊔ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂)))
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height V) _ _)) ⟩
      (c-height V ⊔ height c) ⊔ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂))
      ≤⟨ ⊔-monoʳ-≤ (c-height V ⊔ height c) (⊔-mono-≤ (≤-reflexive (sym (rename-height W₁ S_)))
                   (≤-reflexive (sym (rename-height W₂ S_)))) ⟩
      (c-height V ⊔ height c) ⊔ (c-height W₁ ⊔ c-height W₂)
      ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height V ⊔ height c) _ _)) ⟩
      ((c-height V ⊔ height c) ⊔ c-height W₁) ⊔ c-height W₂
    ∎
  preserve-height (compose-casts {M = M}{c}{d}) =
    begin
      c-height M ⊔ height (compose c d) ≤⟨ ⊔-monoʳ-≤ (c-height M) (compose-height c d) ⟩
      c-height M ⊔ (height c ⊔ height d) ≤⟨ ≤-reflexive (sym (⊔-assoc(c-height M) _ _)) ⟩
      (c-height M ⊔ height c) ⊔ height d
    ∎

  multi-preserve-height : ∀ {Γ A} {M M′ : Γ ⊢ A} {ctx : ReductionCtx}
       → ctx / M —↠ M′ → c-height M′ ≤ c-height M
  multi-preserve-height {M = M}(M ■) = ≤-refl
  multi-preserve-height {M = M}{M′} (ct / M —→⟨ M→M₂ ⟩ M—↠M′) =
      let x = preserve-height M→M₂ in
      let IH = multi-preserve-height M—↠M′ in
      ≤-trans IH x

  open import SpaceEfficient effcast

  csize = EfficientCastStructHeight.size ecs
  tsize = ParamCastCalculusOrig.size Cast

  real-size : ∀{Γ A} → Γ ⊢ A → ℕ
  real-size (` x) = 1
  real-size (ƛ M) = suc (real-size M)
  real-size (L · M) = suc (real-size L + real-size M)
  real-size ($ x) = 1
  real-size (if L M N) = suc (real-size L + real-size M + real-size N)
  real-size (cons M N) = suc (real-size M + real-size N)
  real-size (fst M) = suc (real-size M)
  real-size (snd M) = suc (real-size M)
  real-size (inl M) = suc (real-size M)
  real-size (inr M) = suc (real-size M)
  real-size (case L M N) = suc (real-size L + real-size M + real-size N)
  real-size (M ⟨ c ⟩) = csize c + (real-size M)
  real-size (blame ℓ) = 1

  k : ℕ
  k = proj₁ (proj₂ (size-height))

  j : ℕ
  j = proj₁ (size-height)

  k-pos : 1 ≤ k
  k-pos = proj₁ (proj₂ (proj₂ (size-height)))

  k-size-height : ∀{A B}(c : Cast (A ⇒ B)) → j + csize c ≤ k * pow2 (height c)
  k-size-height = proj₂ (proj₂ (proj₂ (size-height)))

  tsize-pos : ∀{Γ A} (M : Γ ⊢ A) → 1 ≤ tsize M
  tsize-pos (` x) = s≤s z≤n
  tsize-pos (ƛ M) = s≤s z≤n
  tsize-pos (L · M) = s≤s z≤n
  tsize-pos ($ k) = s≤s z≤n
  tsize-pos (if L M N) = s≤s z≤n
  tsize-pos (cons M M₁) = s≤s z≤n
  tsize-pos (fst M) = s≤s z≤n
  tsize-pos (snd M) = s≤s z≤n
  tsize-pos (inl M) = s≤s z≤n
  tsize-pos (inr M) = s≤s z≤n
  tsize-pos (case L M N) = s≤s z≤n
  tsize-pos (M ⟨ c ⟩) = s≤s z≤n
  tsize-pos (blame ℓ) = s≤s z≤n

  real-size-tsize-one : ∀{Γ A} (M : Γ ⊢ A) 
    → real-size M ≤ k * pow2 (c-height M) * tsize M
    → suc (real-size M) ≤ k * pow2 (c-height M) * suc (tsize M)
  real-size-tsize-one M IH =
      begin
        suc (real-size M)
        ≤⟨ s≤s IH ⟩
        suc (k * pow2 (c-height M) * tsize M)
        ≤⟨ +-mono-≤ {x = 1}{y = k * pow2 (c-height M)} (*-mono-≤ k-pos (pow2-pos (c-height M))) ≤-refl ⟩
        k * pow2 (c-height M) + (k * pow2 (c-height M)) * (tsize M)
        ≤⟨ ≤-reflexive (solve 2 (λ x y → x :+ x :* y := x :* (con 1 :+ y)) refl (k * pow2 (c-height M)) (tsize M)) ⟩
        k * pow2 (c-height M) * suc (tsize M)
      ∎ 
      where
      open +-*-Solver

  real-size-tsize-two : ∀{Γ A B} (M : Γ ⊢ A) (N : Γ ⊢ B)
    → real-size M ≤ k * pow2 (c-height M) * tsize M
    → real-size N ≤ k * pow2 (c-height N) * tsize N
    → suc (real-size M + real-size N) ≤ k * pow2 (c-height M ⊔ c-height N) * suc (tsize M + tsize N)
  real-size-tsize-two M N IH1 IH2 =
    begin
      suc (real-size M + real-size N)
    ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
      suc (((k * pow2 (c-height M)) * tsize M) + ((k * pow2 (c-height N)) * tsize N))
    ≤⟨ s≤s (+-mono-≤ (*-mono-≤{x = (k * pow2 (c-height M))}{y = (k * pow2 (c-height M ⊔ c-height N))}{u = tsize M}{v = tsize M}
                              (*-mono-≤{x = k}{y = k} ≤-refl (pow2-mono-≤ ((m≤m⊔n (c-height M) (c-height N))))) ≤-refl)
                     (*-mono-≤{u = tsize N}
                             (*-mono-≤{x = k}{y = k}{u = pow2 (c-height N)} ≤-refl
                                   (pow2-mono-≤{n = c-height N}{m = c-height M ⊔ c-height N} (m≤n⊔m _ _))) ≤-refl)) ⟩
      suc (((k * pow2 (c-height M ⊔ c-height N)) * tsize M) + ((k * pow2 (c-height M ⊔ c-height N)) * tsize N))
    ≤⟨ s≤s (≤-reflexive (solve 3 (λ x y z → x :* y :+ x :* z := x :* (y :+ z)) refl ((k * pow2 (c-height M ⊔ c-height N))) (tsize M) (tsize N))) ⟩
      suc ((k * pow2 (c-height M ⊔ c-height N)) * (tsize M + tsize N))
    ≤⟨ +-mono-≤ (*-mono-≤ k-pos (pow2-pos (c-height M ⊔ c-height N))) ≤-refl ⟩
      (k * pow2 (c-height M ⊔ c-height N)) + (k * pow2 (c-height M ⊔ c-height N)) * (tsize M + tsize N)
    ≤⟨ ≤-reflexive (solve 2 (λ x y → x :+ x :* y := x :* (con 1 :+ y)) refl (k * pow2 (c-height M ⊔ c-height N)) (tsize M + tsize N)) ⟩
      (k * pow2 (c-height M ⊔ c-height N)) * suc (tsize M + tsize N)
    ∎
    where
    open +-*-Solver

  *-distrib-suc : ∀(x y : ℕ) → x + x * y ≡ x * (suc y)
  *-distrib-suc x y = (solve 2 (λ x y → x :+ x :* y := x :* (con 1 :+ y)) refl x y)
    where open +-*-Solver

  real-size-tsize-three : ∀{Γ A B C} (L : Γ ⊢ C) (M : Γ ⊢ A) (N : Γ ⊢ B)
    → real-size L ≤ k * pow2 (c-height L) * tsize L
    → real-size M ≤ k * pow2 (c-height M) * tsize M
    → real-size N ≤ k * pow2 (c-height N) * tsize N
    → suc (real-size L + real-size M + real-size N)
      ≤ k * pow2 (c-height L ⊔ c-height M ⊔ c-height N) * suc (tsize L + tsize M + tsize N)
  real-size-tsize-three L M N IH1 IH2 IH3 = 
    begin
       suc (real-size L + real-size M + real-size N)
    ≤⟨ s≤s (+-mono-≤ (+-mono-≤ IH1 IH2) IH3) ⟩
       suc ((k * pow2 (c-height L) * tsize L) + (k * pow2 (c-height M) * tsize M) + (k * pow2 (c-height N) * tsize N))
    ≤⟨ s≤s (+-mono-≤ (+-mono-≤ (*-mono-≤ (*-mono-≤ (≤-refl{x = k}) (pow2-mono-≤ L≤LMN)) ≤-refl)
                               (*-mono-≤ (*-mono-≤ (≤-refl{x = k}) (pow2-mono-≤ M≤LMN)) ≤-refl))
                               (*-mono-≤ (*-mono-≤ (≤-refl{x = k}) (pow2-mono-≤ N≤LMN)) ≤-refl)) ⟩
       suc ((k * pow2 (c-height L ⊔ c-height M ⊔ c-height N) * tsize L)
            + (k * pow2 (c-height L ⊔ c-height M ⊔ c-height N) * tsize M)
            + (k * pow2 (c-height L ⊔ c-height M ⊔ c-height N) * tsize N))
    ≤⟨ s≤s (≤-reflexive (solve 4 (λ x y z w → x :* y :+ x :* z :+ x :* w := x :* (y :+ z :+ w)) refl (k * pow2 (c-height L ⊔ c-height M ⊔ c-height N)) (tsize L) (tsize M) (tsize N))) ⟩
       suc ((k * pow2 (c-height L ⊔ c-height M ⊔ c-height N)) * (tsize L + tsize M + tsize N))
    ≤⟨ +-mono-≤ (*-mono-≤ k-pos (pow2-pos (c-height L ⊔ c-height M ⊔ c-height N))) ≤-refl ⟩
       k * pow2 (c-height L ⊔ c-height M ⊔ c-height N)
       + (k * pow2 (c-height L ⊔ c-height M ⊔ c-height N)) * (tsize L + tsize M + tsize N)
    ≤⟨ ≤-reflexive (*-distrib-suc (k * pow2 (c-height L ⊔ c-height M ⊔ c-height N)) _) ⟩
       k * pow2 (c-height L ⊔ c-height M ⊔ c-height N) * suc (tsize L + tsize M + tsize N)
    ∎
    where
    open +-*-Solver
    L≤LMN : c-height L ≤ c-height L ⊔ c-height M ⊔ c-height N
    L≤LMN = ≤-trans (m≤m⊔n (c-height L) (c-height M)) (m≤m⊔n (c-height L ⊔ c-height M) _)
    M≤LMN : c-height M ≤ c-height L ⊔ c-height M ⊔ c-height N
    M≤LMN = ≤-trans (m≤n⊔m (c-height L) (c-height M)) (m≤m⊔n (c-height L ⊔ c-height M) _)
    N≤LMN : c-height N ≤ c-height L ⊔ c-height M ⊔ c-height N
    N≤LMN = ≤-trans ((m≤n⊔m (c-height M) (c-height N))) (≤-trans (m≤n⊔m (c-height L) (c-height M ⊔ c-height N)) (≤-reflexive (sym (⊔-assoc (c-height L) (c-height M) (c-height N)))))

  real-size-tsize : ∀{Γ A} (M : Γ ⊢ A)
    → real-size M ≤ (k * pow2 (c-height M)) * tsize M
  real-size-tsize (` x) =
    begin
      (1 * 1) * 1
      ≤⟨ *-mono-≤ (*-mono-≤ k-pos ≤-refl) (tsize-pos (` x)) ⟩
      (k * 1) * tsize (` x)
    ∎
  real-size-tsize (ƛ M) = real-size-tsize-one M (real-size-tsize M)
  real-size-tsize (M · N) = real-size-tsize-two M N (real-size-tsize M) (real-size-tsize N)
  real-size-tsize {Γ}{A} ($_ lit {f}) =
    begin
      (1 * 1) * 1
      ≤⟨ *-mono-≤ (*-mono-≤ k-pos ≤-refl) (tsize-pos{Γ}{A} ($_ lit{f})) ⟩
      (k * 1) * tsize {Γ}{A} ($_ lit {f})
    ∎
  real-size-tsize (if L M N) =
    real-size-tsize-three L M N (real-size-tsize L) (real-size-tsize M) (real-size-tsize N)
  real-size-tsize (cons M N) = real-size-tsize-two M N (real-size-tsize M) (real-size-tsize N)
  real-size-tsize (fst M) = real-size-tsize-one M (real-size-tsize M)
  real-size-tsize (snd M) = real-size-tsize-one M (real-size-tsize M)
  real-size-tsize (inl M) = real-size-tsize-one M (real-size-tsize M)
  real-size-tsize (inr M) = real-size-tsize-one M (real-size-tsize M)
  real-size-tsize (case L M N) =
    real-size-tsize-three L M N (real-size-tsize L) (real-size-tsize M) (real-size-tsize N)
  real-size-tsize (M ⟨ c ⟩) =
    let IH = real-size-tsize M in
    begin
      csize c + real-size M
    ≤⟨ +-mono-≤ ≤-refl IH ⟩
      csize c + (k * pow2 (c-height M) * tsize M)
    ≤⟨ +-mono-≤ (≤-trans (m≤n+m (csize c) j) (k-size-height c)) ≤-refl ⟩      
      (k * pow2 (height c)) + ((k * pow2 (c-height M)) * tsize M)
    ≤⟨ +-mono-≤ (*-mono-≤{x = k} ≤-refl (pow2-mono-≤ {n = height c}{m = (c-height M ⊔ height c)} (m≤n⊔m _ _))) (*-mono-≤ (*-mono-≤{x = k} ≤-refl (pow2-mono-≤{n = c-height M}{m = c-height M ⊔ height c} (m≤m⊔n _ _))) ≤-refl) ⟩      
      k * pow2 (c-height M ⊔ height c) + (k * pow2 (c-height M ⊔ height c)) * (tsize M)
    ≤⟨ ≤-reflexive (solve 3 (λ x y z → x :* y :+ x :* y :* z := x :* y :* (con 1 :+ z)) refl k (pow2 (c-height M ⊔ height c)) (tsize M)) ⟩      
      (k * pow2 (c-height M ⊔ height c)) * suc (tsize M)
    ≤⟨ ≤-refl ⟩      
      k * pow2 (c-height (M ⟨ c ⟩)) * tsize (M ⟨ c ⟩)
    ∎
    where
    open +-*-Solver
  real-size-tsize (blame ℓ) =
    begin
      (1 * 1) * 1
      ≤⟨ *-mono-≤ (*-mono-≤ k-pos ≤-refl) ≤-refl ⟩
      (k * 1) * 1
    ∎

  module SpaceTheorem
    (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
    where

    open import GTLC
    open import GTLC2CCOrig Cast cast
    open EfficientCompile cast

    space-consumption : ∀{Γ M A}  (d : Γ ⊢G M ⦂ A)
      → Σ[ c1 ∈ ℕ ] Σ[ c2 ∈ ℕ ] ∀ (M' : Γ ⊢ A) {ctx}
      → (ctx / (compile M d) —↠ M')
      → real-size M' ≤ c1 + c2 * ideal-size M'
    space-consumption {Γ}{M}{A} d
        with compile-efficient M d false
    ... | ⟨ n , ⟨ cMok  , k≤1 ⟩ ⟩ =
      ⟨ c1 , ⟨ c2 , G ⟩ ⟩
      where
      open +-*-Solver
      c1 = (k * pow2 (c-height (compile M d))) * 3
      c2 = (k * pow2 (c-height (compile M d))) * 10
      G : (M' : (Cast ParamCastCalculusOrig.⊢ Γ) A) {ctx : ReductionCtx} →
                     ctx / compile M d —↠ M' →
                     real-size M' ≤ c1 + c2 * ideal-size M'
      G M' {ct} rd
          with multi-preserve-ok cMok rd
      ... | ⟨ m , M'ok ⟩ =
          let siM' : tsize M' ≤ m + 10 * ideal-size M'
              siM' = size-OK M'ok in
          let rsM' : real-size M' ≤ (k * pow2 (c-height M')) * tsize M'
              rsM' = real-size-tsize M' in
          let pH = multi-preserve-height rd in
          begin
            real-size M'
          ≤⟨ real-size-tsize M' ⟩ 
            (k * pow2 (c-height M')) * tsize M'
          ≤⟨ *-mono-≤ {x = (k * pow2 (c-height M'))} ≤-refl siM' ⟩
            (k * pow2 (c-height M')) * (m + 10 * ideal-size M')
          ≤⟨ ≤-reflexive (*-distribˡ-+ (k * pow2 (c-height M')) _ _) ⟩
            (k * pow2 (c-height M')) * m + (k * pow2 (c-height M')) * (10 * ideal-size M')
          ≤⟨ ≤-reflexive (solve 3 (λ x y z → x :+ (y :* (con 10 :* z)) := x :+ ((y :* con 10) :* z)) refl ((k * pow2 (c-height M')) * m) (k * pow2 (c-height M')) (ideal-size M')) ⟩
            (k * pow2 (c-height M')) * m + ((k * pow2 (c-height M')) * 10) * ideal-size M'
          ≤⟨ +-mono-≤ (*-mono-≤ (*-mono-≤ {x = k} ≤-refl (pow2-mono-≤ pH)) (OK→3 M'ok)) (*-mono-≤ {x = k * pow2 (c-height M') * 10}{y = c2}{u = ideal-size M'}{v = ideal-size M'} (*-mono-≤{u = 10}{v = 10} (*-mono-≤{x = k}{y = k} ≤-refl (pow2-mono-≤ pH)) ≤-refl) ≤-refl) ⟩
            c1 + c2 * ideal-size M'
          ∎
