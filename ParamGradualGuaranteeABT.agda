open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Data.List hiding ([_])
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product
  using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Types
open import Labels
open import CastStructureWithPrecisionABT

open import Utils


module ParamGradualGuaranteeABT (csp : CastStructWithPrecision) where

open CastStructWithPrecision csp

open import ParamCastCalculusABT precast
open import ParamCastAuxABT precast
open import ParamCastReductionABT cs
open import ParamCCPrecisionABT pcsp
{- We've already proven the simlulation lemmas. -}
open import PrecisionSimulationABT csp

{- Here is the statement of the gradual guarantee! -}
gradual-guarantee : ∀ {A A′} {M₁ M₁′ M₂′ : Term}
  → [] ⊢ M₁  ⦂ A
  → [] ⊢ M₁′ ⦂ A′
  → [] , [] ⊢ M₁ ⊑ M₁′
  → M₁′ —→ M₂′
    --------------------------------------------
  → ∃[ M₂ ] (M₁ —↠ M₂) × ([] , [] ⊢ M₂ ⊑ M₂′)

-- group all cases for the ξ rule in the plug lemma
gradual-guarantee-plug : ∀ {A A′} {F : Frame} {M₁ M₁′ M₂′ : Term}
  → [] ⊢ M₁ ⦂ A
  → [] ⊢ plug M₁′ F ⦂ A′
  → [] , [] ⊢ M₁ ⊑ plug M₁′ F
  → M₁′ —→ M₂′
    -------------------------------------------------
  → ∃[ M₂ ] (M₁ —↠ M₂) × [] , [] ⊢ M₂ ⊑ plug M₂′ F

gradual-guarantee-plug {F = F-·₁ M′} {L · M}
                       (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· ⊢M₁′ _ 𝐶⊢-·) (⊑-· L⊑M₁′ M⊑M′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ R* , L₂⊑ ⟩ ⟩ →
      ⟨ L₂ · M , ⟨ plug-cong (F-·₁ M) R* , ⊑-· L₂⊑ M⊑M′ ⟩ ⟩
gradual-guarantee-plug {F = F-·₂ V′ v′} {L · M}
                       (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· ⊢V′ ⊢M₁′ 𝐶⊢-·) (⊑-· L⊑V′ M⊑M₁′) R =
  case catchup ⊢L v′ L⊑V′ of λ where
    ⟨ V , ⟨ v , ⟨ L↠V , V⊑V′ ⟩ ⟩ ⟩ →
      case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
        ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
          ⟨ V · M₂ ,
            ⟨ ↠-trans (plug-cong (F-·₁ _) L↠V) (plug-cong (F-·₂ _ v) M↠M₂) ,
              ⊑-· V⊑V′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-if M′ N′} {if L then M else N endif}
                       (⊢if ⊢L ⊢M ⊢N 𝐶⊢-if) (⊢if ⊢M₁′ ⊢M′ ⊢N′ 𝐶⊢-if)
                       (⊑-if L⊑M₁′ M⊑M′ N⊑N′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ L↠L₂ , L₂⊑M₂′ ⟩ ⟩ →
      ⟨ if L₂ then M else N endif ,
        ⟨ plug-cong (F-if M N) L↠L₂ ,
          ⊑-if L₂⊑M₂′ M⊑M′ N⊑N′ ⟩ ⟩
gradual-guarantee-plug {F = F-×₁ V′ v′} {⟦ L , M ⟧}
                       (⊢cons ⊢L ⊢M 𝐶⊢-cons) (⊢cons ⊢V′ ⊢M₁′ 𝐶⊢-cons)
                       (⊑-cons L⊑V′ M⊑M₁′) R =
  case catchup ⊢L v′ L⊑V′ of λ where
    ⟨ V , ⟨ v , ⟨ L↠V , V⊑V′ ⟩ ⟩ ⟩ →
      case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
        ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
          ⟨ ⟦ V , M₂ ⟧ ,
            ⟨ ↠-trans (plug-cong (F-×₂ _) L↠V) (plug-cong (F-×₁ _ v) M↠M₂) ,
              ⊑-cons V⊑V′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-×₂ M′} {⟦ L , M ⟧}
                       (⊢cons ⊢L ⊢M 𝐶⊢-cons) (⊢cons ⊢M₁′ ⊢M′ 𝐶⊢-cons)
                       (⊑-cons L⊑M₁′ M⊑M′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ L↠L₂ , L₂⊑M₂′ ⟩ ⟩ →
      ⟨ ⟦ L₂ , M ⟧ , ⟨ plug-cong (F-×₂ _) L↠L₂ , ⊑-cons L₂⊑M₂′ M⊑M′ ⟩ ⟩
gradual-guarantee-plug {F = F-fst} {fst M}
                       (⊢fst ⊢M 𝐶⊢-fst) (⊢fst ⊢M₁′ 𝐶⊢-fst)
                       (⊑-fst M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ fst M₂ , ⟨ plug-cong F-fst M↠M₂ , ⊑-fst M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-snd} {snd M}
                       (⊢snd ⊢M 𝐶⊢-snd) (⊢snd ⊢M₁′ 𝐶⊢-snd)
                       (⊑-snd M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ snd M₂ , ⟨ plug-cong F-snd M↠M₂ , ⊑-snd M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-inl B′} {inl M other B}
                       (⊢inl B ⊢M 𝐶⊢-inl) (⊢inl B′ ⊢M₁′ 𝐶⊢-inl)
                       (⊑-inl B⊑B′ M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ inl M₂ other B , ⟨ plug-cong (F-inl B) M↠M₂ , ⊑-inl B⊑B′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-inr A′} {inr M other A}
                       (⊢inr A ⊢M 𝐶⊢-inr) (⊢inr A′ ⊢M₁′ 𝐶⊢-inr)
                       (⊑-inr A⊑A′ M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ inr M₂ other A , ⟨ plug-cong (F-inr A) M↠M₂ , ⊑-inr A⊑A′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-case A′ B′ M′ N′} {case L of A ⇒ M ∣ B ⇒ N}
                       (⊢case A B ⊢L ⊢M ⊢N 𝐶⊢-case) (⊢case A′ B′ ⊢M₁′ ⊢M′ ⊢N′ 𝐶⊢-case)
                       (⊑-case L⊑M₁′ A⊑A′ B⊑B′ M⊑M′ N⊑N′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ L↠L₂ , L₂⊑M₂′ ⟩ ⟩ →
      ⟨ case L₂ of A ⇒ M ∣ B ⇒ N ,
        ⟨ plug-cong (F-case A B M N) L↠L₂ ,
          ⊑-case L₂⊑M₂′ A⊑A′ B⊑B′ M⊑M′ N⊑N′ ⟩ ⟩
gradual-guarantee-plug {F = F-cast c′} {M ⟨ c ⟩}
                       (⊢cast c ⊢M 𝐶⊢-cast) (⊢cast c′ ⊢M₁′ 𝐶⊢-cast)
                       (⊑-cast A⊑A′ B⊑B′ M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ⟩ , ⟨ plug-cong (F-cast c) M↠M₂ , ⊑-cast A⊑A′ B⊑B′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-cast c′} {M}
                       _ (⊢cast c′ ⊢M₁′ 𝐶⊢-cast)
                       (⊑-castr A⊑A′ A⊑B′ ⊢M M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ M₂ , ⟨ M↠M₂ , ⊑-castr A⊑A′ A⊑B′ (preserve-mult ⊢M M↠M₂) M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-wrap c′ i′} {M ⟨ c ₍ i ₎⟩}
                       (⊢wrap c i ⊢M 𝐶⊢-wrap) (⊢wrap c′ i′ ⊢M₁′ 𝐶⊢-wrap)
                       (⊑-wrap lpii M⊑M₁′ imp) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ₍ i ₎⟩ , ⟨ plug-cong (F-wrap c i) M↠M₂ , ⊑-wrap lpii M₂⊑M₂′ imp ⟩ ⟩
gradual-guarantee-plug {F = F-wrap c′ i′} {M}
                       _ (⊢wrap c′ i′ ⊢M₁′ 𝐶⊢-wrap)
                       (⊑-wrapr lpti ⊢M M⊑M₁′ nd) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ M₂ , ⟨ M↠M₂ , ⊑-wrapr lpti (preserve-mult ⊢M M↠M₂) M₂⊑M₂′ nd ⟩ ⟩
gradual-guarantee-plug (⊢cast c ⊢M 𝐶⊢-cast) _ (⊑-castl A⊑A′ B⊑A′ ⊢M′ M⊑) R =
  {- be careful about which ⊢M′ to use, since CC doesn't
     satisfy uniqueness of typing -}
  case gradual-guarantee ⊢M ⊢M′ M⊑ (ξ R) of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ⟩ ,
        ⟨ plug-cong (F-cast c) R* ,
          ⊑-castl A⊑A′ B⊑A′ (preserve ⊢M′ (ξ R)) M₂⊑ ⟩ ⟩
gradual-guarantee-plug (⊢wrap c i ⊢M 𝐶⊢-cast) _ (⊑-wrapl lpit ⊢M′ M⊑) R =
  case gradual-guarantee ⊢M ⊢M′ M⊑ (ξ R) of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ₍ i ₎⟩ ,
        ⟨ plug-cong (F-wrap c i) R* ,
          ⊑-wrapl lpit (preserve ⊢M′ (ξ R)) M₂⊑ ⟩ ⟩

gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (ξ {F = F} R) =
  gradual-guarantee-plug {F = F} ⊢M₁ ⊢M₁′ M₁⊑ R
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ ξ-blame =
  ⟨ _ , ⟨ _ ∎ , ⊑-blame ⟩ ⟩
gradual-guarantee (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· (⊢ƛ _ ⊢N′ 𝐶⊢-ƛ) ⊢W′ 𝐶⊢-·) (⊑-· L⊑ M⊑) (β w′) =
  case catchup ⊢L V-ƛ L⊑ of λ where
    ⟨ V , ⟨ v , ⟨ L↠V , V⊑ ⟩ ⟩ ⟩ →
      case catchup ⊢M w′ M⊑ of λ where
        ⟨ W , ⟨ w , ⟨ M↠W , W⊑ ⟩ ⟩ ⟩ →
          let ⊢V = preserve-mult ⊢L L↠V
              ⊢W = preserve-mult ⊢M M↠W in
          case sim-β ⊢V ⊢W ⊢N′ ⊢W′ v w w′ V⊑ W⊑ of λ where
            ⟨ M₂ , ⟨ V·W↠M₂ , M₂⊑ ⟩ ⟩ →
              ⟨ M₂ ,
                ⟨  ↠-trans (plug-cong (F-·₁ _)   L↠V)
                            (↠-trans (plug-cong (F-·₂ _ v) M↠W) V·W↠M₂) ,
                   M₂⊑ ⟩ ⟩
gradual-guarantee (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· (⊢$ f ab 𝐶⊢-$) (⊢$ k a 𝐶⊢-$) 𝐶⊢-·) (⊑-· L⊑f M⊑k) δ =
  {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ β-if-true = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ β-if-false = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-fst x x₁) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-snd x x₁) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-caseL x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-caseR x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (cast v) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (wrap v) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (fun-cast x x₁) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (fst-cast x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (snd-cast x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (case-cast x) = {!!}
gradual-guarantee (⊢cast c ⊢M 𝐶⊢-cast) _ (⊑-castl A⊑A′ B⊑A′ ⊢M′ M⊑) R =
  case gradual-guarantee ⊢M ⊢M′ M⊑ R of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ⟩ ,
        ⟨ plug-cong (F-cast c) R* ,
          ⊑-castl A⊑A′ B⊑A′ (preserve ⊢M′ R) M₂⊑ ⟩ ⟩
gradual-guarantee (⊢wrap c i ⊢M 𝐶⊢-wrap) _ (⊑-wrapl lpit ⊢M′ M⊑) R =
  case gradual-guarantee ⊢M ⊢M′ M⊑ R of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ₍ i ₎⟩ ,
        ⟨ plug-cong (F-wrap c i) R* ,
          ⊑-wrapl lpit (preserve ⊢M′ R) M₂⊑ ⟩ ⟩
