open import Data.Nat using (ℕ; zero; suc)
open import Data.List hiding ([_])
open import Data.Nat.Properties using (suc-injective)
open import Data.Bool
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
open import Syntax


module PrecisionSimulationABT (csp : CastStructWithPrecision) where

open CastStructWithPrecision csp

open import ParamCastCalculusABT precast
open import ParamCastAuxABT precast
open import ParamCastReductionABT cs
open import ParamCCPrecisionABT pcsp
open import PreservePrecisionABT pcsp

{- Catching up on the less precise side. -}
catchup : ∀ {A} {M V′ : Term}
  → [] ⊢ M ⦂ A
  → Value V′
  → [] , [] ⊢ M ⊑ V′
    ----------------------------------------------
  → ∃[ V ] Value V × (M —↠ V) × [] , [] ⊢ V ⊑ V′
catchup ⊢M v′ ⊑-$ =
  ⟨ _  , ⟨ V-const , ⟨ _ ∎ , ⊑-$ ⟩ ⟩ ⟩
catchup ⊢M v′ (⊑-ƛ A⊑ N⊑) =
  ⟨ _ , ⟨ V-ƛ , ⟨ _ ∎ , ⊑-ƛ A⊑ N⊑ ⟩ ⟩ ⟩
catchup (⊢cons ⊢M₁ ⊢M₂ 𝐶⊢-cons) (V-pair v′₁ v′₂) (⊑-cons M₁⊑ M₂⊑) =
  case ⟨ catchup ⊢M₁ v′₁ M₁⊑ , catchup ⊢M₂ v′₂ M₂⊑ ⟩ of λ where
    ⟨ ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ₘ , Vₘ⊑ ⟩ ⟩ ⟩ , ⟨ Vₙ , ⟨ vₙ , ⟨ rd⋆ₙ , Vₙ⊑ ⟩ ⟩ ⟩ ⟩ →
      ⟨ ⟦ Vₘ , Vₙ ⟧ , ⟨ V-pair vₘ vₙ ,
        ⟨ ↠-trans (plug-cong (F-×₂ _ ⊢M₂) ⊢M₁ rd⋆ₘ)
                   (plug-cong (F-×₁ _ (preserve-mult ⊢M₁ rd⋆ₘ) vₘ) ⊢M₂ rd⋆ₙ) ,
          ⊑-cons Vₘ⊑ Vₙ⊑ ⟩ ⟩ ⟩
catchup (⊢inl B ⊢M 𝐶⊢-inl) (V-inl v′) (⊑-inl B⊑ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ Vₘ , ⟨ vₘ , ⟨ rd⋆ , Vₘ⊑ ⟩ ⟩ ⟩ →
      ⟨ inl Vₘ other _ , ⟨ V-inl vₘ ,
        ⟨ plug-cong (F-inl _) ⊢M rd⋆ , ⊑-inl B⊑ Vₘ⊑ ⟩ ⟩ ⟩
catchup (⊢inr A ⊢M 𝐶⊢-inr) (V-inr v′) (⊑-inr A⊑ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ Vₘ , ⟨ vₘ , ⟨ rd* , Vₘ⊑ ⟩ ⟩ ⟩ →
      ⟨ inr Vₘ other _ , ⟨ V-inr vₘ ,
        ⟨ plug-cong (F-inr _) ⊢M rd* , ⊑-inr A⊑ Vₘ⊑ ⟩ ⟩ ⟩
catchup (⊢cast c ⊢M 𝐶⊢-cast) v′ (⊑-castl A⊑A′ B⊑A′ ⊢M′ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    -- M —↠ V
    ⟨ V , ⟨ v , ⟨ rd*₁ , V⊑ ⟩ ⟩ ⟩ →
      case ActiveOrInert c of λ where
        (inj₁ a) →
          case applyCast-catchup a (preserve-mult ⊢M rd*₁) ⊢M′ v v′ A⊑A′ B⊑A′ V⊑ of λ where
            ⟨ W , ⟨ w , ⟨ rd*₂ , W⊑ ⟩ ⟩ ⟩ →
              ⟨ W , ⟨ w ,
                ⟨ ↠-trans (plug-cong (F-cast c) ⊢M rd*₁) (_ —→⟨ cast v ⟩ rd*₂) ,
                  W⊑ ⟩ ⟩ ⟩
        (inj₂ i) →
          ⟨ V ⟨ c ₍ i ₎⟩ , ⟨ V-wrap v i ,
            ⟨ ↠-trans (plug-cong (F-cast c) ⊢M rd*₁) (_ —→⟨ wrap v ⟩ _ ∎) ,
              ⊑-wrapl (⊑→lpit i A⊑A′ B⊑A′) ⊢M′ V⊑ ⟩ ⟩ ⟩
-- just recur in all 3 wrap cases
catchup (⊢wrap c i ⊢M 𝐶⊢-wrap) (V-wrap v′ i′) (⊑-wrap lpii M⊑ imp) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W ⟨ c ₍ i ₎⟩ , ⟨ V-wrap w i ,
        ⟨ plug-cong (F-wrap _ _) ⊢M rd* , ⊑-wrap lpii W⊑ imp ⟩ ⟩ ⟩
catchup (⊢wrap c i ⊢M 𝐶⊢-wrap) v′ (⊑-wrapl {c = c} {i = i} lpit ⊢M′ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W ⟨ c ₍ i ₎⟩ , ⟨ V-wrap w i ,
        ⟨ plug-cong (F-wrap _ _) ⊢M rd* , ⊑-wrapl lpit ⊢M′ W⊑ ⟩ ⟩ ⟩
catchup ⊢M (V-wrap v′ i′) (⊑-wrapr lpti ⊢M₁ M⊑ nd) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W , ⟨ w , ⟨ rd* , ⊑-wrapr lpti (preserve-mult ⊢M₁ rd*) W⊑ nd ⟩ ⟩ ⟩


sim-β : ∀ {A A′ B B′} {V W N′ W′ : Term}
  → [] ⊢ V ⦂ A ⇒ B
  → [] ⊢ W ⦂ A
  → A′ ∷ [] ⊢ N′ ⦂ B′
  → [] ⊢ W′ ⦂ A′
  → Value V → Value W → Value W′
  → [] , [] ⊢ V ⊑ ƛ A′ ˙ N′
  → [] , [] ⊢ W ⊑ W′
    --------------------------------------------------
  → ∃[ M ] (V · W —↠ M) × ([] , [] ⊢ M ⊑ N′ [ W′ ])
sim-β {V = ƛ A ˙ N} {W} (⊢ƛ .A ⊢N 𝐶⊢-ƛ) ⊢W ⊢N′ ⊢W′ V-ƛ w w′ (⊑-ƛ A⊑ N⊑) W⊑ =
  ⟨ N [ W ] , ⟨ _ —→⟨ β w ⟩ _ ∎ , substitution-pres-⊑ ⊢N ⊢N′ ⊢W ⊢W′ N⊑ W⊑ ⟩ ⟩
sim-β (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢W _ ⊢W′ (V-wrap {V = V} v .i) w w′
      (⊑-wrapl lpit (⊢ƛ A′ ⊢N′ 𝐶⊢-ƛ) V⊑ƛN′) W⊑ =
  {-
       V ⟨ c ₍ i ₎⟩ · W
         —→ ( by fun-cast )
       (V · W ⟨ dom c ⟩) ⟨ cod c ⟩
         —↠ ( by catchup )
       (V · W₁) ⟨ cod c ⟩
         —↠ ( by sim-β )
       N ⟨ cod c ⟩
  -}
  case Inert-Cross⇒ c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩ →
      case lpit→⊑ lpit of λ where
        ⟨ fun⊑ A₁⊑A′ B₁⊑B′ , fun⊑ A⊑A′ B⊑B′ ⟩ →
          -- dom c : A ⇒ A₁ ⊑ A′
          let ⊢Wdomc = (⊢cast (dom c x) ⊢W 𝐶⊢-cast) in
          case catchup ⊢Wdomc w′ (⊑-castl A⊑A′ A₁⊑A′ ⊢W′ W⊑) of λ where
            ⟨ W₁ , ⟨ w₁ , ⟨ Wdomc↠W₁ , W₁⊑ ⟩ ⟩ ⟩ →
              case (sim-β ⊢V (preserve-mult ⊢Wdomc Wdomc↠W₁)
                          ⊢N′ ⊢W′ v w₁ w′ V⊑ƛN′ W₁⊑) of λ where
                ⟨ N , ⟨ V·W₁↠N , N⊑ ⟩ ⟩ →
                  let ⊢V·W₁    = ⊢· ⊢V (preserve-mult ⊢Wdomc Wdomc↠W₁) 𝐶⊢-·
                      ⊢V·Wdomc = ⊢· ⊢V ⊢Wdomc 𝐶⊢-· in
                  ⟨ N ⟨ cod c x ⟩ ,
                    ⟨ _ —→⟨ fun-cast v w {x} ⟩
                        ↠-trans (plug-cong (F-cast _) ⊢V·Wdomc (plug-cong (F-·₂ _ ⊢V v) ⊢Wdomc Wdomc↠W₁))
                                 (plug-cong (F-cast _) ⊢V·W₁ V·W₁↠N),
                      ⊑-castl B₁⊑B′ B⊑B′ (preserve-substitution _ _ ⊢N′ ⊢W′) N⊑ ⟩ ⟩

sim-δ : ∀ {A A′ B B′} {V W : Term} {f : rep A′ → rep B′} {k : rep A′}
          {ab : Prim (A′ ⇒ B′)} {a : Prim A′} {b : Prim B′}
  → [] ⊢ V ⦂ A ⇒ B
  → [] ⊢ W ⦂ A
  → Value V → Value W
  → [] , [] ⊢ V ⊑ $ f # ab
  → [] , [] ⊢ W ⊑ $ k # a
    ----------------------------------------------------
  → ∃[ M ] (V · W —↠ M) × ([] , [] ⊢ M ⊑ $ (f k) # b)
sim-δ {ab = P-Fun _} (⊢$ _ _ 𝐶⊢-$) (⊢wrap _ _ _ 𝐶⊢-wrap) -- impossible
      V-const (V-wrap w i) ⊑-$ (⊑-wrapl _ _ _) =
  contradiction i {- c : A ⇒ ` ι cannot be inert -} (baseNotInert _)
sim-δ {ab = P-Fun _} {a} {b} (⊢$ f ab 𝐶⊢-$) (⊢$ k a 𝐶⊢-$)
      V-const V-const ⊑-$ ⊑-$ =
  ⟨ $ (f k) # b , ⟨ _ —→⟨ δ ⟩ _ ∎ , ⊑-$ ⟩ ⟩
sim-δ {f = f} {k} {ab} {a} {b} (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢W
      (V-wrap v i) w (⊑-wrapl lpit (⊢$ f _ 𝐶⊢-$) V⊑f) W⊑k =
  case Inert-Cross⇒ c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩ →
      case lpit→⊑ lpit of λ where
        ⟨ fun⊑ A₁⊑A′ B₁⊑B′ , fun⊑ A⊑A′ B⊑B′ ⟩ →
          let ⊢Wdomc = (⊢cast (dom c x) ⊢W 𝐶⊢-cast) in
          case catchup ⊢Wdomc V-const (⊑-castl A⊑A′ A₁⊑A′ (⊢$ k a 𝐶⊢-$) W⊑k) of λ where
            ⟨ W₁ , ⟨ w₁ , ⟨ Wdomc↠W₁ , W₁⊑ ⟩ ⟩ ⟩ →
              case (sim-δ ⊢V (preserve-mult ⊢Wdomc Wdomc↠W₁) v w₁ V⊑f W₁⊑) of λ where
                ⟨ N , ⟨ V·W₁↠N , N⊑ ⟩ ⟩ →
                  let ⊢V·W₁    = ⊢· ⊢V (preserve-mult ⊢Wdomc Wdomc↠W₁) 𝐶⊢-·
                      ⊢V·Wdomc = ⊢· ⊢V ⊢Wdomc 𝐶⊢-· in
                  ⟨ N ⟨ cod c x ⟩ ,
                    ⟨ _ —→⟨ fun-cast v w {x} ⟩
                        ↠-trans (plug-cong (F-cast _) ⊢V·Wdomc (plug-cong (F-·₂ _ ⊢V v) ⊢Wdomc Wdomc↠W₁))
                                 (plug-cong (F-cast _) ⊢V·W₁ V·W₁↠N),
                      ⊑-castl B₁⊑B′ B⊑B′ (⊢$ (f k) b 𝐶⊢-$) N⊑ ⟩ ⟩

sim-fun-cast : ∀ {A A′ B B′ C′ D′} {V V′ W W′} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
  → [] ⊢ V ⦂ A ⇒ B
  → [] ⊢ W ⦂ A
  → [] ⊢ V′ ⦂ A′ ⇒ B′
  → [] ⊢ W′ ⦂ C′
  → Value V → Value W → Value V′ → Value W′
  → (i′ : Inert c′) → (x′ : Cross c′)
  → [] , [] ⊢ V ⊑ V′ ⟨ c′ ₍ i′ ₎⟩
  → [] , [] ⊢ W ⊑ W′
    --------------------------------------------------------------------------------
  → ∃[ M ] (V · W —↠ M) × ([] , [] ⊢ M ⊑ (V′ · (W′ ⟨ dom c′ x′ ⟩)) ⟨ cod c′ x′ ⟩)
sim-fun-cast ⊢V ⊢W ⊢V′ ⊢W′ v w v′ w′ i′ x′ (⊑-wrap lpii V⊑V′ imp) W⊑W′ =
  {!!}
sim-fun-cast ⊢V ⊢W ⊢V′ ⊢W′ v w v′ w′ i′ x′ (⊑-wrapl lpit ⊢V′c′ V⊑V′c′) W⊑W′ =
  {!!}
sim-fun-cast {V = V} {W = W} ⊢V ⊢W ⊢V′ ⊢W′ v w v′ w′ i′ x′ (⊑-wrapr lpti ⊢V₁ V⊑V′ nd) W⊑W′ =
  case lpti→⊑ lpti of λ where
    ⟨ unk⊑ , unk⊑ ⟩ → contradiction refl nd
    ⟨ fun⊑ A⊑A′ B⊑B′ , fun⊑ A⊑C′ B⊑D′ ⟩ →
      case uniqueness ⊢V ⊢V₁ of λ where
       refl → ⟨ V · W , ⟨ _ ∎ ,
                 ⊑-castr B⊑B′ B⊑D′ (⊢· ⊢V ⊢W 𝐶⊢-·) (⊑-· V⊑V′ (⊑-castr A⊑C′ A⊑A′ ⊢W W⊑W′)) ⟩ ⟩
