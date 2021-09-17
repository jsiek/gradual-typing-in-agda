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
    CastsAllSafe w.r.t ℓ, then ℓ ≢ ℓ′ .
  -}
  plug-blame-allsafe-diff-ℓ : ∀ {ℓ ℓ′}
    → (F : Frame)
    → CastsAllSafe (plug (blame ℓ′) F) ℓ
      -------------------------------------
    → ℓ ≢̂ ℓ′
  plug-blame-allsafe-diff-ℓ (F-·₁ _)         (⊢· (⊢blame _ ℓ≢ℓ′) _ 𝐶ₛ-·)             ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-·₂ _ _)       (⊢· _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-·)             ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-if _ _)       (⊢if (⊢blame _ ℓ≢ℓ′) _ _ 𝐶ₛ-if)         ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-×₁ _ _)       (⊢cons _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-cons)       ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-×₂ _)         (⊢cons (⊢blame _ ℓ≢ℓ′) _ 𝐶ₛ-cons)       ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ F-fst            (⊢fst (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-fst)           ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ F-snd            (⊢snd (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-snd)           ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-inl _)        (⊢inl _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-inl)         ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-inr _)        (⊢inr _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-inr)         ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-case _ _ _ _) (⊢case _ _ (⊢blame _ ℓ≢ℓ′) _ _ 𝐶ₛ-case) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-cast _)       (⊢cast _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-cast)       ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-diff-ℓ (F-wrap _ _)     (⊢wrap _ _ (⊢blame _ ℓ≢ℓ′) 𝐶ₛ-wrap)     ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′

  -- WARNING: this lemma can be removed
  plug-blame→¬allsafe : ∀ {ℓ}
    → (F : Frame)
    → ¬ (CastsAllSafe (plug (blame ℓ) F) ℓ)
  plug-blame→¬allsafe F allsafe = plug-blame-allsafe-diff-ℓ F allsafe ≡̂-refl

  preserve-allsafe : ∀ {M M′ : Term} {ℓ}
    → CastsAllSafe M ℓ
    → M —→ M′
      --------------------
    → CastsAllSafe M′ ℓ

  preserve-allsafe-plug : ∀ {M M′ : Term} {ℓ}
    → (F : Frame)
    → CastsAllSafe (plug M F) ℓ
    → M —→ M′
      -----------------------------
    → CastsAllSafe (plug M′ F) ℓ

  preserve-allsafe-plug (F-·₁ _) (⊢· allsafeₗ allsafeₘ 𝐶ₛ-·) R =
    ⊢· (preserve-allsafe allsafeₗ R) allsafeₘ 𝐶ₛ-·
  preserve-allsafe-plug (F-·₂ _ _) (⊢· allsafeₗ allsafeₘ 𝐶ₛ-·) R =
    ⊢· allsafeₗ (preserve-allsafe allsafeₘ R) 𝐶ₛ-·
  preserve-allsafe-plug (F-if _ _) (⊢if allsafeₗ allsafeₘ allsafeₙ 𝐶ₛ-if) R =
    ⊢if (preserve-allsafe allsafeₗ R) allsafeₘ allsafeₙ 𝐶ₛ-if
  preserve-allsafe-plug (F-×₁ _ _) (⊢cons allsafeₘ allsafeₙ 𝐶ₛ-cons) R =
    ⊢cons allsafeₘ (preserve-allsafe allsafeₙ R) 𝐶ₛ-cons
  preserve-allsafe-plug (F-×₂ _) (⊢cons allsafeₘ allsafeₙ 𝐶ₛ-cons) R =
    ⊢cons (preserve-allsafe allsafeₘ R) allsafeₙ 𝐶ₛ-cons
  preserve-allsafe-plug F-fst (⊢fst allsafeₘ 𝐶ₛ-fst) R =
    ⊢fst (preserve-allsafe allsafeₘ R) 𝐶ₛ-fst
  preserve-allsafe-plug F-snd (⊢snd allsafeₘ 𝐶ₛ-snd) R =
    ⊢snd (preserve-allsafe allsafeₘ R) 𝐶ₛ-snd
  preserve-allsafe-plug (F-inl B) (⊢inl .B allsafeₘ 𝐶ₛ-inl) R =
    ⊢inl B (preserve-allsafe allsafeₘ R) 𝐶ₛ-inl
  preserve-allsafe-plug (F-inr A) (⊢inr .A allsafeₘ 𝐶ₛ-inr) R =
    ⊢inr A (preserve-allsafe allsafeₘ R) 𝐶ₛ-inr
  preserve-allsafe-plug (F-case A B _ _) (⊢case .A .B allsafeₗ allsafeₘ allsafeₙ 𝐶ₛ-case) R =
    ⊢case A B (preserve-allsafe allsafeₗ R) allsafeₘ allsafeₙ 𝐶ₛ-case
  preserve-allsafe-plug (F-cast c) (⊢cast .c allsafeₘ ⟨ safe , refl ⟩) R =
    ⊢cast c (preserve-allsafe allsafeₘ R) ⟨ safe , refl ⟩
  preserve-allsafe-plug (F-wrap c i) (⊢wrap .c .i allsafeₘ ⟨ safe , refl ⟩) R =
    ⊢wrap c i (preserve-allsafe allsafeₘ R) ⟨ safe , refl ⟩

  preserve-allsafe allsafe (ξ {F = F} rd) =
    preserve-allsafe-plug F allsafe rd
  preserve-allsafe allsafe (ξ-blame {F = F}) =
    ⊢blame _ (plug-blame-allsafe-diff-ℓ F allsafe)
  preserve-allsafe (⊢· (⊢ƛ _ allsafeₙ 𝐶⊢-ƛ) allsafeₘ 𝐶ₛ-·) (β v) =
    substitution-allsafe _ _ allsafeₙ allsafeₘ
  preserve-allsafe _ δ = ⊢$ _ _ 𝐶ₛ-$
  preserve-allsafe (⊢if _ allsafeₘ _ 𝐶ₛ-if) β-if-true = allsafeₘ
  preserve-allsafe (⊢if _ _ allsafeₙ 𝐶ₛ-if) β-if-false = allsafeₙ
  preserve-allsafe (⊢fst (⊢cons allsafeₘ _ 𝐶ₛ-cons) 𝐶ₛ-fst) (β-fst _ _) = allsafeₘ
  preserve-allsafe (⊢snd (⊢cons _ allsafeₙ 𝐶ₛ-cons) 𝐶ₛ-snd) (β-snd _ _) = allsafeₙ
  preserve-allsafe (⊢case _ _ (⊢inl _ allsafeₗ 𝐶ₛ-inl) allsafeₘ _ 𝐶ₛ-case) (β-caseL _) =
    substitution-allsafe _ _ allsafeₘ allsafeₗ
  preserve-allsafe (⊢case _ _ (⊢inr _ allsafeₗ 𝐶ₛ-inr) _ allsafeₙ 𝐶ₛ-case) (β-caseR _) =
    substitution-allsafe _ _ allsafeₙ allsafeₗ
  preserve-allsafe (⊢cast c allsafeₘ ⟨ safe , refl ⟩) (cast v {a}) = applyCast-pres-allsafe a safe allsafeₘ
  preserve-allsafe (⊢cast c allsafeₘ ⟨ safe , refl ⟩) (wrap v {i}) = ⊢wrap c i allsafeₘ ⟨ safe , refl ⟩
