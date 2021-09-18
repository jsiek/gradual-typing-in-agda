open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product
  using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)

open import Types
open import Labels
open import CastStructureABT
open import CastStructureWithBlameSafetyABT


module ParamBlameSubtypingABT (css : CastStructWithBlameSafety) where

  open CastStructWithBlameSafety css
  open import ParamCastCalculusABT precast
  open import ParamCastAuxABT precast
  open import ParamCastReductionABT cs

  open import ParamCastSubtypingABT pcss


  {-
    If we plug `blame ℓ′` into some frame and the result term is
    safe for ℓ, then ℓ ≢ ℓ′ .
  -}
  plug-blame-safe-for-diff-ℓ : ∀ {ℓ ℓ′}
    → (F : Frame)
    → (plug (blame ℓ′) F) SafeFor ℓ
      -------------------------------------
    → ℓ ≢̂ ℓ′
  plug-blame-safe-for-diff-ℓ (F-·₁ _)         (⊢· (⊢blame _ ℓ≢ℓ′) _ 𝐶ₛ-·)             ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-·₂ _ _)       (⊢· _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-·)             ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-if _ _)       (⊢if (⊢blame _ ℓ≢ℓ′) _ _ 𝐶ₛ-if)         ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-×₁ _ _)       (⊢cons _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-cons)       ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-×₂ _)         (⊢cons (⊢blame _ ℓ≢ℓ′) _ 𝐶ₛ-cons)       ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ F-fst            (⊢fst (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-fst)           ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ F-snd            (⊢snd (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-snd)           ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-inl _)        (⊢inl _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-inl)         ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-inr _)        (⊢inr _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-inr)         ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-case _ _ _ _) (⊢case _ _ (⊢blame _ ℓ≢ℓ′) _ _ 𝐶ₛ-case) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-cast _)       (⊢cast _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-cast)       ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-wrap _ _)     (⊢wrap _ _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-wrap)     ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′

  -- WARNING: this lemma can be removed
  -- plug-blame→¬safefor : ∀ {ℓ}
  --   → (F : Frame)
  --   → ¬ (CastsSafefor (plug (blame ℓ) F) ℓ)
  -- plug-blame→¬safefor F safefor = plug-blame-safe-for-diff-ℓ F safefor ≡̂-refl

  preserve-SafeFor : ∀ {M M′ : Term} {ℓ}
    → M SafeFor ℓ
    → M —→ M′
      --------------------
    → M′ SafeFor ℓ

  preserve-SafeFor-plug : ∀ {M M′ : Term} {ℓ}
    → (F : Frame)
    → (plug M F) SafeFor ℓ
    → M —→ M′
      -----------------------------
    → (plug M′ F) SafeFor ℓ

  preserve-SafeFor-plug (F-·₁ _) (⊢· safeforₗ safeforₘ 𝐶ₛ-·) R =
    ⊢· (preserve-SafeFor safeforₗ R) safeforₘ 𝐶ₛ-·
  preserve-SafeFor-plug (F-·₂ _ _) (⊢· safeforₗ safeforₘ 𝐶ₛ-·) R =
    ⊢· safeforₗ (preserve-SafeFor safeforₘ R) 𝐶ₛ-·
  preserve-SafeFor-plug (F-if _ _) (⊢if safeforₗ safeforₘ safeforₙ 𝐶ₛ-if) R =
    ⊢if (preserve-SafeFor safeforₗ R) safeforₘ safeforₙ 𝐶ₛ-if
  preserve-SafeFor-plug (F-×₁ _ _) (⊢cons safeforₘ safeforₙ 𝐶ₛ-cons) R =
    ⊢cons safeforₘ (preserve-SafeFor safeforₙ R) 𝐶ₛ-cons
  preserve-SafeFor-plug (F-×₂ _) (⊢cons safeforₘ safeforₙ 𝐶ₛ-cons) R =
    ⊢cons (preserve-SafeFor safeforₘ R) safeforₙ 𝐶ₛ-cons
  preserve-SafeFor-plug F-fst (⊢fst safeforₘ 𝐶ₛ-fst) R =
    ⊢fst (preserve-SafeFor safeforₘ R) 𝐶ₛ-fst
  preserve-SafeFor-plug F-snd (⊢snd safeforₘ 𝐶ₛ-snd) R =
    ⊢snd (preserve-SafeFor safeforₘ R) 𝐶ₛ-snd
  preserve-SafeFor-plug (F-inl B) (⊢inl .B safeforₘ 𝐶ₛ-inl) R =
    ⊢inl B (preserve-SafeFor safeforₘ R) 𝐶ₛ-inl
  preserve-SafeFor-plug (F-inr A) (⊢inr .A safeforₘ 𝐶ₛ-inr) R =
    ⊢inr A (preserve-SafeFor safeforₘ R) 𝐶ₛ-inr
  preserve-SafeFor-plug (F-case A B _ _) (⊢case .A .B safeforₗ safeforₘ safeforₙ 𝐶ₛ-case) R =
    ⊢case A B (preserve-SafeFor safeforₗ R) safeforₘ safeforₙ 𝐶ₛ-case
  preserve-SafeFor-plug (F-cast c) (⊢cast .c safeforₘ ⟨ safe , refl ⟩) R =
    ⊢cast c (preserve-SafeFor safeforₘ R) ⟨ safe , refl ⟩
  preserve-SafeFor-plug (F-wrap c i) (⊢wrap .c .i safeforₘ ⟨ safe , refl ⟩) R =
    ⊢wrap c i (preserve-SafeFor safeforₘ R) ⟨ safe , refl ⟩

  preserve-SafeFor safefor (ξ {F = F} rd) =
    preserve-SafeFor-plug F safefor rd
  preserve-SafeFor safefor (ξ-blame {F = F}) =
    ⊢blame _ (plug-blame-safe-for-diff-ℓ F safefor)
  preserve-SafeFor (⊢· (⊢ƛ _ safeforₙ 𝐶⊢-ƛ) safeforₘ 𝐶ₛ-·) (β v) =
    substitution-SafeFor _ _ safeforₙ safeforₘ
  preserve-SafeFor _ δ = ⊢$ _ _ 𝐶ₛ-$
  preserve-SafeFor (⊢if _ safeforₘ _ 𝐶ₛ-if) β-if-true = safeforₘ
  preserve-SafeFor (⊢if _ _ safeforₙ 𝐶ₛ-if) β-if-false = safeforₙ
  preserve-SafeFor (⊢fst (⊢cons safeforₘ _ 𝐶ₛ-cons) 𝐶ₛ-fst) (β-fst _ _) = safeforₘ
  preserve-SafeFor (⊢snd (⊢cons _ safeforₙ 𝐶ₛ-cons) 𝐶ₛ-snd) (β-snd _ _) = safeforₙ
  preserve-SafeFor (⊢case _ _ (⊢inl _ safeforₗ 𝐶ₛ-inl) safeforₘ _ 𝐶ₛ-case) (β-caseL _) =
    substitution-SafeFor _ _ safeforₘ safeforₗ
  preserve-SafeFor (⊢case _ _ (⊢inr _ safeforₗ 𝐶ₛ-inr) _ safeforₙ 𝐶ₛ-case) (β-caseR _) =
    substitution-SafeFor _ _ safeforₙ safeforₗ
  preserve-SafeFor (⊢cast c safeforₘ ⟨ safe , refl ⟩) (cast v {a}) = applyCast-pres-SafeFor a safe safeforₘ
  preserve-SafeFor (⊢cast c safeforₘ ⟨ safe , refl ⟩) (wrap v {i}) = ⊢wrap c i safeforₘ ⟨ safe , refl ⟩
  preserve-SafeFor (⊢· (⊢wrap c i safeforₗ ⟨ safe , refl ⟩) safeforₘ 𝐶ₛ-·) (fun-cast {c = c} v w {x}) =
    ⊢cast _ (⊢· safeforₗ (⊢cast _ safeforₘ ⟨ domBlameSafe safe x , refl ⟩) 𝐶ₛ-·) ⟨ codBlameSafe safe x , refl ⟩
  preserve-SafeFor (⊢fst (⊢wrap _ _ safeforₘ ⟨ safe , refl ⟩) 𝐶ₛ-fst) (fst-cast v {x}) =
    ⊢cast _ (⊢fst safeforₘ 𝐶ₛ-fst) ⟨ fstBlameSafe safe x , refl ⟩
  preserve-SafeFor (⊢snd (⊢wrap _ _ safeforₘ ⟨ safe , refl ⟩) 𝐶ₛ-snd) (snd-cast v {x}) =
    ⊢cast _ (⊢snd safeforₘ 𝐶ₛ-snd) ⟨ sndBlameSafe safe x , refl ⟩
  preserve-SafeFor (⊢case _ _ (⊢wrap _ _ safeforₗ ⟨ safe , refl ⟩) safeforₘ safeforₙ 𝐶ₛ-case) (case-cast v {x}) =
    ⊢case _ _ safeforₗ
      (substitution-SafeFor _ _
        (rename-pres-SafeFor _ safeforₘ λ {x} ∋x → ⟨ _ , ⟨ ext-suc-∋x x ∋x , refl ⟩ ⟩)
        (⊢cast _ (⊢` refl) ⟨ inlBlameSafe safe x , refl ⟩))
      (substitution-SafeFor _ _
        (rename-pres-SafeFor _ safeforₙ λ {x} ∋x → ⟨ _ , ⟨ ext-suc-∋x x ∋x , refl ⟩ ⟩)
        (⊢cast _ (⊢` refl) ⟨ inrBlameSafe safe x , refl ⟩))
      𝐶ₛ-case
