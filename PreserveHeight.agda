open import Types hiding (_⊔_)
open import Labels
open import Variables
open import CastStructure
import EfficientParamCasts
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open Data.Nat.Properties.≤-Reasoning
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

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


{-
  module PreserveHeightParams
    (applyCast-height : ∀{Γ}{A B}{V}{v : Value {Γ} V}{c : Cast (A ⇒ B)}
        {a : Active c}
      → c-height (applyCast V v c {a}) ≤ c-height V ⊔ height c)
    (dom-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}{x : Cross c}
       → height (dom c x) ≤ height c)
    (cod-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}{x : Cross c}
       → height (cod c x) ≤ height c)
    (fst-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}{x : Cross c}
       → height (fstC c x) ≤ height c)
    (snd-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}{x : Cross c}
       → height (sndC c x) ≤ height c)
    (inlC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}{x : Cross c}
       → height (inlC c x) ≤ height c)
    (inrC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}{x : Cross c}
       → height (inrC c x) ≤ height c)
      where
-}
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
