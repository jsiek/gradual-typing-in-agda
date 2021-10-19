open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
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

open import Utils


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
  plug-blame-safe-for-diff-ℓ : ∀ {A B} {ℓ ℓ′}
    → (F : Frame A B)
    → (plug (blame A ℓ′) F) SafeFor ℓ
      -------------------------------------
    → ℓ ≢̂ ℓ′
  plug-blame-safe-for-diff-ℓ (F-·₁ _ _)           (⊢·        (⊢blame _ _ ℓ≢ℓ′) _   𝐶ₛ-·)    ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-·₂ _ _ _)         (⊢·    _   (⊢blame _ _ ℓ≢ℓ′)     𝐶ₛ-·)    ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-if _ _ _ _)       (⊢if       (⊢blame _ _ ℓ≢ℓ′) _ _ 𝐶ₛ-if)   ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-×₁ _ _ _)         (⊢cons _   (⊢blame _ _ ℓ≢ℓ′)     𝐶ₛ-cons) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-×₂ _ _)           (⊢cons     (⊢blame _ _ ℓ≢ℓ′) _   𝐶ₛ-cons) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ F-fst                (⊢fst      (⊢blame _ _ ℓ≢ℓ′)     𝐶ₛ-fst)  ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ F-snd                (⊢snd      (⊢blame _ _ ℓ≢ℓ′)     𝐶ₛ-snd)  ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-inl _)            (⊢inl  _   (⊢blame _ _ ℓ≢ℓ′)     𝐶ₛ-inl)  ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-inr _)            (⊢inr  _   (⊢blame _ _ ℓ≢ℓ′)     𝐶ₛ-inr)  ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-case _ _ _ _ _ _) (⊢case _ _ (⊢blame _ _ ℓ≢ℓ′) _ _ 𝐶ₛ-case) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-cast _)           (⊢cast _   (⊢blame _ _ ℓ≢ℓ′)     𝐶ₛ-cast) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-safe-for-diff-ℓ (F-wrap _ _)         (⊢wrap _ _ (⊢blame _ _ ℓ≢ℓ′)     𝐶ₛ-wrap) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′

  preserve-SafeFor : ∀ {M M′ : Term} {ℓ}
    → M SafeFor ℓ
    → M —→ M′
      --------------------
    → M′ SafeFor ℓ

  preserve-SafeFor-plug : ∀ {A B} {M M′ : Term} {ℓ}
    → (F : Frame A B)
    → (plug M F) SafeFor ℓ
    → M —→ M′
      -----------------------------
    → (plug M′ F) SafeFor ℓ

  preserve-SafeFor-plug (F-·₁ _ _) (⊢· safeforₗ safeforₘ 𝐶ₛ-·) R =
    ⊢· (preserve-SafeFor safeforₗ R) safeforₘ 𝐶ₛ-·
  preserve-SafeFor-plug (F-·₂ _ _ _) (⊢· safeforₗ safeforₘ 𝐶ₛ-·) R =
    ⊢· safeforₗ (preserve-SafeFor safeforₘ R) 𝐶ₛ-·
  preserve-SafeFor-plug (F-if _ _ _ _) (⊢if safeforₗ safeforₘ safeforₙ 𝐶ₛ-if) R =
    ⊢if (preserve-SafeFor safeforₗ R) safeforₘ safeforₙ 𝐶ₛ-if
  preserve-SafeFor-plug (F-×₁ _ _ _) (⊢cons safeforₘ safeforₙ 𝐶ₛ-cons) R =
    ⊢cons safeforₘ (preserve-SafeFor safeforₙ R) 𝐶ₛ-cons
  preserve-SafeFor-plug (F-×₂ _ _) (⊢cons safeforₘ safeforₙ 𝐶ₛ-cons) R =
    ⊢cons (preserve-SafeFor safeforₘ R) safeforₙ 𝐶ₛ-cons
  preserve-SafeFor-plug F-fst (⊢fst safeforₘ 𝐶ₛ-fst) R =
    ⊢fst (preserve-SafeFor safeforₘ R) 𝐶ₛ-fst
  preserve-SafeFor-plug F-snd (⊢snd safeforₘ 𝐶ₛ-snd) R =
    ⊢snd (preserve-SafeFor safeforₘ R) 𝐶ₛ-snd
  preserve-SafeFor-plug (F-inl B) (⊢inl .B safeforₘ 𝐶ₛ-inl) R =
    ⊢inl B (preserve-SafeFor safeforₘ R) 𝐶ₛ-inl
  preserve-SafeFor-plug (F-inr A) (⊢inr .A safeforₘ 𝐶ₛ-inr) R =
    ⊢inr A (preserve-SafeFor safeforₘ R) 𝐶ₛ-inr
  preserve-SafeFor-plug (F-case A B _ _ _ _) (⊢case .A .B safeforₗ safeforₘ safeforₙ 𝐶ₛ-case) R =
    ⊢case A B (preserve-SafeFor safeforₗ R) safeforₘ safeforₙ 𝐶ₛ-case
  preserve-SafeFor-plug (F-cast c) (⊢cast .c safeforₘ ⟨ safe , refl ⟩) R =
    ⊢cast c (preserve-SafeFor safeforₘ R) ⟨ safe , refl ⟩
  preserve-SafeFor-plug (F-wrap c i) (⊢wrap .c .i safeforₘ ⟨ safe , refl ⟩) R =
    ⊢wrap c i (preserve-SafeFor safeforₘ R) ⟨ safe , refl ⟩

  preserve-SafeFor safefor (ξ {F = F} _ rd) =
    preserve-SafeFor-plug F safefor rd
  preserve-SafeFor safefor (ξ-blame {F = F}) =
    ⊢blame _ _ (plug-blame-safe-for-diff-ℓ F safefor)
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

  {- If M SafeFor ℓ then M ⌿↠ blame ℓ . -}
  soundness-<: : ∀ {A} {M : Term} {ℓ}
    → M SafeFor ℓ
      --------------------
    → ¬ (M —↠ blame A ℓ)
  -- By induction on M —↠ blame ℓ .
  soundness-<: safefor-plug ( _ —→⟨ ξ ⊢M M→M′ ⟩ plugM′F↠blame ) =
    soundness-<: (preserve-SafeFor safefor-plug (ξ ⊢M M→M′)) plugM′F↠blame
  soundness-<: safefor ( _ —→⟨ ξ-blame {F = F} ⟩ blame↠blame ) =
    case blame↠blame of λ where
      (_ ∎) →
        contradiction (≡→≡̂ refl) (plug-blame-safe-for-diff-ℓ F safefor)
      (_ —→⟨ blame→ ⟩ _) →
        contradiction blame→ (blame⌿→ refl)
  -- Application (β)
  soundness-<: (⊢· (⊢ƛ _ safeforₙ 𝐶ₛ-ƛ) safeforₘ 𝐶ₛ-·)
               ( (ƛ _ ˙ N) · M —→⟨ β vₘ ⟩ N[M]↠blame ) =
    soundness-<: (substitution-SafeFor _ _ safeforₙ safeforₘ) N[M]↠blame
  -- δ
  soundness-<: (⊢· _ _ 𝐶ₛ-·)
               ( ($ f # _) · ($ k # _) —→⟨ δ ⟩ f·k↠blame ) =
    soundness-<: (⊢$ (f k) _ 𝐶ₛ-$) f·k↠blame
  -- If
  soundness-<: (⊢if _ safeforₘ _ 𝐶ₛ-if)
               ( if ($ true # _) then M else N endif  —→⟨ β-if-true ⟩  M↠blame ) =
    soundness-<: safeforₘ M↠blame
  soundness-<: (⊢if _ _ safeforₙ 𝐶ₛ-if)
               ( if ($ false # _) then M else N endif —→⟨ β-if-false ⟩ N↠blame ) =
    soundness-<: safeforₙ N↠blame
  -- Fst & snd
  soundness-<: (⊢fst (⊢cons safeforₘ safeforₙ 𝐶ₛ-cons) 𝐶ₛ-fst)
               ( fst ⟦ M , N ⟧ —→⟨ β-fst vₘ vₙ ⟩ M↠blame ) =
    soundness-<: safeforₘ M↠blame
  soundness-<: (⊢snd (⊢cons safeforₘ safeforₙ 𝐶ₛ-cons) 𝐶ₛ-snd)
               ( snd ⟦ M , N ⟧ —→⟨ β-snd vₘ vₙ ⟩ N↠blame ) =
    soundness-<: safeforₙ N↠blame
  -- Case
  soundness-<: (⊢case _ _ (⊢inl _ safeforₗ 𝐶ₛ-inl) safeforₘ _ 𝐶ₛ-case)
               ( case (inl L other _) of _ ⇒ _ ∣ _ ⇒ _ —→⟨ β-caseL v ⟩ M[L]↠blame ) =
    soundness-<: (substitution-SafeFor _ _ safeforₘ safeforₗ) M[L]↠blame
  soundness-<: (⊢case _ _ (⊢inr _ safeforₗ 𝐶ₛ-inr) _ safeforₙ 𝐶ₛ-case)
               ( case (inr L other _) of _ ⇒ _ ∣ _ ⇒ _ —→⟨ β-caseR v ⟩ N[L]↠blame ) =
    soundness-<: (substitution-SafeFor _ _ safeforₙ safeforₗ) N[L]↠blame
  -- Cast
  soundness-<: (⊢cast .c safeforₘ ⟨ safe , refl ⟩)
               ( M ⟨ c ⟩ —→⟨ cast v {a} ⟩ applyCastMc↠blame ) =
    soundness-<: (applyCast-pres-SafeFor a safe safeforₘ) applyCastMc↠blame
  -- Wrap
  soundness-<: (⊢cast .c safeforₘ ⟨ safe , refl ⟩)
               ( M ⟨ c ⟩ —→⟨ wrap v {i} ⟩ applyCastMc↠blame ) =
    soundness-<: (⊢wrap c i safeforₘ ⟨ safe , refl ⟩) applyCastMc↠blame
  -- Fun-cast
  soundness-<: (⊢· (⊢wrap .c .i safeforₘ ⟨ safe , refl ⟩) safeforₙ 𝐶ₛ-·)
               ( M ⟨ c ₍ i ₎⟩ · N —→⟨ fun-cast vₘ vₙ {x} ⟩ M·N↠blame) =
    soundness-<: (⊢cast _ (⊢· safeforₘ
                              (⊢cast _ safeforₙ ⟨ domBlameSafe safe x , refl ⟩) 𝐶ₛ-·)
                          ⟨ codBlameSafe safe x , refl ⟩) M·N↠blame
  -- Fst-cast & snd-cast
  soundness-<: (⊢fst (⊢wrap .c .i safeforₘ ⟨ safe , refl ⟩) 𝐶ₛ-fst)
               ( fst (M ⟨ c ₍ i ₎⟩) —→⟨ fst-cast _ {x} ⟩ fstM⟨fstc⟩↠blame ) =
    soundness-<: (⊢cast _ (⊢fst safeforₘ 𝐶ₛ-fst)
                   ⟨ fstBlameSafe safe x , refl ⟩) fstM⟨fstc⟩↠blame
  soundness-<: (⊢snd (⊢wrap .c .i safeforₘ ⟨ safe , refl ⟩) 𝐶ₛ-fst)
               ( snd (M ⟨ c ₍ i ₎⟩) —→⟨ snd-cast _ {x} ⟩ sndM⟨sndc⟩↠blame ) =
    soundness-<: (⊢cast _ (⊢snd safeforₘ 𝐶ₛ-snd)
                   ⟨ sndBlameSafe safe x , refl ⟩) sndM⟨sndc⟩↠blame
  -- Case-cast
  soundness-<: (⊢case _ _ (⊢wrap .c .i safeforₗ ⟨ safe , refl ⟩) safeforₘ safeforₙ 𝐶ₛ-case)
               ( case (L ⟨ c ₍ i ₎⟩) of _ ⇒ M ∣ _ ⇒ N —→⟨ case-cast v {x} ⟩ ↠blame ) =
    soundness-<: (⊢case _ _ safeforₗ
                   (substitution-SafeFor _ _
                     (rename-pres-SafeFor _ safeforₘ λ {x} ∋x → ⟨ _ , ⟨ ext-suc-∋x x ∋x , refl ⟩ ⟩ )
                     (⊢cast _ (⊢` refl) ⟨ inlBlameSafe safe x , refl ⟩))
                   (substitution-SafeFor _ _
                     (rename-pres-SafeFor _ safeforₙ λ {x} ∋x → ⟨ _ , ⟨ ext-suc-∋x x ∋x , refl ⟩ ⟩ )
                     (⊢cast _ (⊢` refl) ⟨ inrBlameSafe safe x , refl ⟩))
                   𝐶ₛ-case) ↠blame
  -- Blame
  soundness-<: (⊢blame _ _ ℓ≢) (blame _ ℓ ∎) = ℓ≢ ≡̂-refl
