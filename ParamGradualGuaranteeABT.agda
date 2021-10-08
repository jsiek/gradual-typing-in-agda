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
open import ParamCCPrecisionABT precast
open import PreservePrecisionABT precast using (cc-prec→⊑)
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
gradual-guarantee-plug : ∀ {A A′ X′} {F : Frame X′ A′} {M₁ M₁′ M₂′ : Term}
  → [] ⊢ M₁ ⦂ A
  → [] ⊢ plug M₁′ F ⦂ A′
  → [] ⊢ M₁′ ⦂ X′
  → [] , [] ⊢ M₁ ⊑ plug M₁′ F
  → M₁′ —→ M₂′
    -------------------------------------------------
  → ∃[ M₂ ] (M₁ —↠ M₂) × [] , [] ⊢ M₂ ⊑ plug M₂′ F

gradual-guarantee-plug {F = F-·₁ M′ ⊢M′} {L · M}
                       (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· ⊢M₁′ _ 𝐶⊢-·) _ (⊑-· L⊑M₁′ M⊑M′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ R* , L₂⊑ ⟩ ⟩ →
      ⟨ L₂ · M , ⟨ plug-cong (F-·₁ M ⊢M) ⊢L R* , ⊑-· L₂⊑ M⊑M′ ⟩ ⟩
gradual-guarantee-plug {F = F-·₂ V′ _ v′} {L · M}
                       (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· ⊢V′ ⊢M₁′ 𝐶⊢-·) _ (⊑-· L⊑V′ M⊑M₁′) R =
  case catchup ⊢L v′ L⊑V′ of λ where
    ⟨ V , ⟨ v , ⟨ L↠V , V⊑V′ ⟩ ⟩ ⟩ →
      case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
        ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
          let ⊢V = preserve-mult ⊢L L↠V in
          ⟨ V · M₂ ,
            ⟨ ↠-trans (plug-cong (F-·₁ _ ⊢M) ⊢L L↠V) (plug-cong (F-·₂ _ ⊢V v) ⊢M M↠M₂) ,
              ⊑-· V⊑V′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-if M′ N′ _ _} {if L then M else N endif}
                       (⊢if ⊢L ⊢M ⊢N 𝐶⊢-if) (⊢if ⊢M₁′ ⊢M′ ⊢N′ 𝐶⊢-if) _
                       (⊑-if L⊑M₁′ M⊑M′ N⊑N′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ L↠L₂ , L₂⊑M₂′ ⟩ ⟩ →
      ⟨ if L₂ then M else N endif ,
        ⟨ plug-cong (F-if M N ⊢M ⊢N) ⊢L L↠L₂ ,
          ⊑-if L₂⊑M₂′ M⊑M′ N⊑N′ ⟩ ⟩
gradual-guarantee-plug {F = F-×₁ V′ _ v′} {⟦ L , M ⟧}
                       (⊢cons ⊢L ⊢M 𝐶⊢-cons) (⊢cons ⊢V′ ⊢M₁′ 𝐶⊢-cons) _
                       (⊑-cons L⊑V′ M⊑M₁′) R =
  case catchup ⊢L v′ L⊑V′ of λ where
    ⟨ V , ⟨ v , ⟨ L↠V , V⊑V′ ⟩ ⟩ ⟩ →
      case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
        ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
          let ⊢V = preserve-mult ⊢L L↠V in
          ⟨ ⟦ V , M₂ ⟧ ,
            ⟨ ↠-trans (plug-cong (F-×₂ _ ⊢M) ⊢L L↠V) (plug-cong (F-×₁ _ ⊢V v) ⊢M M↠M₂) ,
              ⊑-cons V⊑V′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-×₂ M′ _} {⟦ L , M ⟧}
                       (⊢cons ⊢L ⊢M 𝐶⊢-cons) (⊢cons ⊢M₁′ ⊢M′ 𝐶⊢-cons) _
                       (⊑-cons L⊑M₁′ M⊑M′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ L↠L₂ , L₂⊑M₂′ ⟩ ⟩ →
      ⟨ ⟦ L₂ , M ⟧ , ⟨ plug-cong (F-×₂ _ ⊢M) ⊢L L↠L₂ , ⊑-cons L₂⊑M₂′ M⊑M′ ⟩ ⟩
gradual-guarantee-plug {F = F-fst} {fst M}
                       (⊢fst ⊢M 𝐶⊢-fst) (⊢fst ⊢M₁′ 𝐶⊢-fst) _
                       (⊑-fst M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ fst M₂ , ⟨ plug-cong F-fst ⊢M M↠M₂ , ⊑-fst M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-snd} {snd M}
                       (⊢snd ⊢M 𝐶⊢-snd) (⊢snd ⊢M₁′ 𝐶⊢-snd) _
                       (⊑-snd M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ snd M₂ , ⟨ plug-cong F-snd ⊢M M↠M₂ , ⊑-snd M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-inl B′} {inl M other B}
                       (⊢inl B ⊢M 𝐶⊢-inl) (⊢inl B′ ⊢M₁′ 𝐶⊢-inl) _
                       (⊑-inl B⊑B′ M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ inl M₂ other B , ⟨ plug-cong (F-inl B) ⊢M M↠M₂ , ⊑-inl B⊑B′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-inr A′} {inr M other A}
                       (⊢inr A ⊢M 𝐶⊢-inr) (⊢inr A′ ⊢M₁′ 𝐶⊢-inr) _
                       (⊑-inr A⊑A′ M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ inr M₂ other A , ⟨ plug-cong (F-inr A) ⊢M M↠M₂ , ⊑-inr A⊑A′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-case A′ B′ M′ N′ _ _} {case L of A ⇒ M ∣ B ⇒ N}
                       (⊢case A B ⊢L ⊢M ⊢N 𝐶⊢-case) (⊢case A′ B′ ⊢M₁′ ⊢M′ ⊢N′ 𝐶⊢-case) _
                       (⊑-case L⊑M₁′ A⊑A′ B⊑B′ M⊑M′ N⊑N′) R =
  case gradual-guarantee ⊢L ⊢M₁′ L⊑M₁′ R of λ where
    ⟨ L₂ , ⟨ L↠L₂ , L₂⊑M₂′ ⟩ ⟩ →
      ⟨ case L₂ of A ⇒ M ∣ B ⇒ N ,
        ⟨ plug-cong (F-case A B M N ⊢M ⊢N) ⊢L L↠L₂ ,
          ⊑-case L₂⊑M₂′ A⊑A′ B⊑B′ M⊑M′ N⊑N′ ⟩ ⟩
gradual-guarantee-plug {F = F-cast c′} {M ⟨ c ⟩}
                       (⊢cast c ⊢M 𝐶⊢-cast) (⊢cast c′ ⊢M₁′ 𝐶⊢-cast) _
                       (⊑-cast A⊑A′ B⊑B′ M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ⟩ , ⟨ plug-cong (F-cast c) ⊢M M↠M₂ , ⊑-cast A⊑A′ B⊑B′ M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-cast c′} {M}
                       _ (⊢cast c′ ⊢M₁′ 𝐶⊢-cast) _
                       (⊑-castr A⊑A′ A⊑B′ ⊢M M⊑M₁′) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ M₂ , ⟨ M↠M₂ , ⊑-castr A⊑A′ A⊑B′ (preserve-mult ⊢M M↠M₂) M₂⊑M₂′ ⟩ ⟩
gradual-guarantee-plug {F = F-wrap c′ i′} {M ⟨ c ₍ i ₎⟩}
                       (⊢wrap c i ⊢M 𝐶⊢-wrap) (⊢wrap c′ i′ ⊢M₁′ 𝐶⊢-wrap) _
                       (⊑-wrap A⊑A′ B⊑B′ M⊑M₁′ imp) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ₍ i ₎⟩ , ⟨ plug-cong (F-wrap c i) ⊢M M↠M₂ , ⊑-wrap A⊑A′ B⊑B′ M₂⊑M₂′ imp ⟩ ⟩
gradual-guarantee-plug {F = F-wrap c′ i′} {M}
                       _ (⊢wrap c′ i′ ⊢M₁′ 𝐶⊢-wrap) _
                       (⊑-wrapr A⊑A′ A⊑B′ ⊢M M⊑M₁′ nd) R =
  case gradual-guarantee ⊢M ⊢M₁′ M⊑M₁′ R of λ where
    ⟨ M₂ , ⟨ M↠M₂ , M₂⊑M₂′ ⟩ ⟩ →
      ⟨ M₂ , ⟨ M↠M₂ , ⊑-wrapr A⊑A′ A⊑B′ (preserve-mult ⊢M M↠M₂) M₂⊑M₂′ nd ⟩ ⟩
gradual-guarantee-plug (⊢cast c ⊢M 𝐶⊢-cast) ⊢plug ⊢M₁′ (⊑-castl A⊑A′ B⊑A′ ⊢M′ M⊑) R =
  case gradual-guarantee ⊢M ⊢M′ M⊑ (ξ ⊢M₁′ R) of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ⟩ ,
        ⟨ plug-cong (F-cast c ) ⊢M R* ,
          ⊑-castl A⊑A′ B⊑A′ (preserve ⊢M′ (ξ ⊢M₁′ R)) M₂⊑ ⟩ ⟩
gradual-guarantee-plug (⊢wrap c i ⊢M 𝐶⊢-cast) _ ⊢M₁′ (⊑-wrapl A⊑A′ B⊑A′ ⊢M′ M⊑) R =
  case gradual-guarantee ⊢M ⊢M′ M⊑ (ξ ⊢M₁′ R) of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ₍ i ₎⟩ ,
        ⟨ plug-cong (F-wrap c i) ⊢M R* ,
          ⊑-wrapl A⊑A′ B⊑A′ (preserve ⊢M′ (ξ ⊢M₁′ R)) M₂⊑ ⟩ ⟩

gradual-guarantee ⊢M₁ ⊢plug M₁⊑ (ξ {F = F} ⊢M₁′ R) =
  case uniqueness ⊢plug (plug-wt _ ⊢M₁′ F) of λ where
    refl → gradual-guarantee-plug {F = F} ⊢M₁ ⊢plug ⊢M₁′ M₁⊑ R
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ ξ-blame =
  ⟨ _ , ⟨ _ ∎ , ⊑-blame ⊢M₁ (cc-prec→⊑ (λ _ ()) ⊢M₁ (plug-wt _ (⊢blame _ _ 𝐶⊢-blame) _) M₁⊑) ⟩ ⟩
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
                ⟨  ↠-trans (plug-cong (F-·₁ _ ⊢M) ⊢L  L↠V)
                            (↠-trans (plug-cong (F-·₂ _ ⊢V v) ⊢M M↠W) V·W↠M₂) ,
                   M₂⊑ ⟩ ⟩
gradual-guarantee (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· (⊢$ f ab 𝐶⊢-$) (⊢$ k a 𝐶⊢-$) 𝐶⊢-·) (⊑-· L⊑f M⊑k) δ =
  case catchup ⊢L V-const L⊑f of λ where
    ⟨ V , ⟨ v , ⟨ L↠V , V⊑f ⟩ ⟩ ⟩ →
      case catchup ⊢M V-const M⊑k of λ where
        ⟨ W , ⟨ w , ⟨ M↠W , W⊑k ⟩ ⟩ ⟩ →
          let ⊢V = preserve-mult ⊢L L↠V
              ⊢W = preserve-mult ⊢M M↠W in
          case sim-δ ⊢V ⊢W v w V⊑f W⊑k of λ where
            ⟨ M₂ , ⟨ V·W↠M₂ , M₂⊑ ⟩ ⟩ →
              ⟨ M₂ ,
                ⟨  ↠-trans (plug-cong (F-·₁ _ ⊢M) ⊢L  L↠V)
                            (↠-trans (plug-cong (F-·₂ _ ⊢V v) ⊢M M↠W) V·W↠M₂) ,
                   M₂⊑ ⟩ ⟩
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ β-if-true = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ β-if-false = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-fst x x₁) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-snd x x₁) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-caseL x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (β-caseR x) = {!!}
gradual-guarantee ⊢M₁ (⊢cast c′ ⊢V′ 𝐶⊢-cast) (⊑-castr A⊑A′ A⊑B′ ⊢M₁† M₁⊑V′) (cast v′ {a′}) =
  case catchup ⊢M₁ v′ M₁⊑V′ of λ where
    ⟨ V , ⟨ v , ⟨ M₁↠V , V⊑V′ ⟩ ⟩ ⟩ →
      let ⊢V = preserve-mult ⊢M₁† M₁↠V in
      ⟨ V , ⟨ M₁↠V , cast-castr a′ ⊢V ⊢V′ v v′ A⊑A′ A⊑B′ V⊑V′ ⟩ ⟩
gradual-guarantee (⊢cast c ⊢M 𝐶⊢-cast) (⊢cast c′ ⊢V′ 𝐶⊢-cast) (⊑-cast A⊑A′ B⊑B′ M⊑V′) (cast v′ {a′}) =
  case catchup ⊢M v′ M⊑V′ of λ where
    ⟨ V , ⟨ v , ⟨ M↠V , V⊑V′ ⟩ ⟩ ⟩ →
      let ⊢V = preserve-mult ⊢M M↠V in
      case sim-cast a′ ⊢V ⊢V′ v v′ A⊑A′ B⊑B′ V⊑V′ of λ where
        ⟨ M₂ , ⟨ Vc↠M₂ , M₂⊑ ⟩ ⟩ →
          ⟨ M₂ , ⟨ ↠-trans (plug-cong (F-cast _) ⊢M M↠V) Vc↠M₂ , M₂⊑ ⟩ ⟩
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (wrap v) = {!!}
gradual-guarantee (⊢· ⊢L ⊢M 𝐶⊢-·) (⊢· (⊢wrap c′ i′ ⊢V′ 𝐶⊢-wrap) ⊢W′ 𝐶⊢-·)
                  (⊑-· L⊑V′c′ M⊑W′) (fun-cast v′ w′ {x′} {i′}) =
  case catchup ⊢L (V-wrap v′ i′) L⊑V′c′ of λ where
    ⟨ V , ⟨ v , ⟨ L↠V , V⊑V′c′ ⟩ ⟩ ⟩ →
      case catchup ⊢M w′ M⊑W′ of λ where
        ⟨ W , ⟨ w , ⟨ M↠W , W⊑W′ ⟩ ⟩ ⟩ →
          let ⊢V = preserve-mult ⊢L L↠V
              ⊢W = preserve-mult ⊢M M↠W in
          case sim-fun-cast ⊢V ⊢W ⊢V′ ⊢W′ v w v′ w′ i′ x′ V⊑V′c′ W⊑W′ of λ where
            ⟨ M₂ , ⟨ V·W↠M₂ , M₂⊑ ⟩ ⟩ →
              ⟨ M₂ ,
                ⟨ ↠-trans (plug-cong (F-·₁ _ ⊢M) ⊢L  L↠V)
                           (↠-trans (plug-cong (F-·₂ _ ⊢V v) ⊢M M↠W) V·W↠M₂) ,
                  M₂⊑ ⟩ ⟩
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (fst-cast x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (snd-cast x) = {!!}
gradual-guarantee ⊢M₁ ⊢M₁′ M₁⊑ (case-cast x) = {!!}
gradual-guarantee (⊢cast c ⊢M 𝐶⊢-cast) _ (⊑-castl A⊑A′ B⊑A′ ⊢M′ M⊑) R =
  case gradual-guarantee ⊢M ⊢M′ M⊑ R of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ⟩ ,
        ⟨ plug-cong (F-cast c) ⊢M R* ,
          ⊑-castl A⊑A′ B⊑A′ (preserve ⊢M′ R) M₂⊑ ⟩ ⟩
gradual-guarantee (⊢wrap c i ⊢M 𝐶⊢-wrap) _ (⊑-wrapl A⊑A′ B⊑A′ ⊢M′ M⊑) R =
  case gradual-guarantee ⊢M ⊢M′ M⊑ R of λ where
    ⟨ M₂ , ⟨ R* , M₂⊑ ⟩ ⟩ →
      ⟨ M₂ ⟨ c ₍ i ₎⟩ ,
        ⟨ plug-cong (F-wrap c i) ⊢M R* ,
          ⊑-wrapl A⊑A′ B⊑A′ (preserve ⊢M′ R) M₂⊑ ⟩ ⟩
