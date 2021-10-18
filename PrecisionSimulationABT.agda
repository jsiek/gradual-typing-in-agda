open import Data.Nat using (ℕ; zero; suc)
open import Data.List hiding ([_])
open import Data.Nat.Properties using (suc-injective)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; subst)
open Eq.≡-Reasoning renaming (_∎ to _qed)

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
open import ParamCCPrecisionABT precast
open import PreservePrecisionABT precast

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
              ⊑-wrapl A⊑A′ B⊑A′ ⊢M′ V⊑ ⟩ ⟩ ⟩
-- just recur in all 3 wrap cases
catchup (⊢wrap c i ⊢M 𝐶⊢-wrap) (V-wrap v′ i′) (⊑-wrap A⊑A′ B⊑B′ M⊑ imp) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W ⟨ c ₍ i ₎⟩ , ⟨ V-wrap w i ,
        ⟨ plug-cong (F-wrap _ _) ⊢M rd* , ⊑-wrap A⊑A′ B⊑B′ W⊑ imp ⟩ ⟩ ⟩
catchup (⊢wrap c i ⊢M 𝐶⊢-wrap) v′ (⊑-wrapl {c = c} {i = i} A⊑A′ B⊑A′ ⊢M′ M⊑) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W ⟨ c ₍ i ₎⟩ , ⟨ V-wrap w i ,
        ⟨ plug-cong (F-wrap _ _) ⊢M rd* , ⊑-wrapl A⊑A′ B⊑A′ ⊢M′ W⊑ ⟩ ⟩ ⟩
catchup ⊢M (V-wrap v′ i′) (⊑-wrapr A⊑A′ A⊑B′ ⊢M₁ M⊑ nd) =
  case catchup ⊢M v′ M⊑ of λ where
    ⟨ W , ⟨ w , ⟨ rd* , W⊑ ⟩ ⟩ ⟩ →
      ⟨ W , ⟨ w , ⟨ rd* , ⊑-wrapr A⊑A′ A⊑B′ (preserve-mult ⊢M₁ rd*) W⊑ nd ⟩ ⟩ ⟩


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
      (⊑-wrapl A⊑A′ B⊑A′ (⊢ƛ A′ ⊢N′ 𝐶⊢-ƛ) V⊑ƛN′) W⊑ =
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
      case ⟨ A⊑A′ , B⊑A′ ⟩ of λ where
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
      V-const (V-wrap w i) ⊑-$ (⊑-wrapl _ _ _ _) =
  contradiction i {- c : A ⇒ ` ι cannot be inert -} (baseNotInert _)
sim-δ {ab = P-Fun _} {a} {b} (⊢$ f ab 𝐶⊢-$) (⊢$ k a 𝐶⊢-$)
      V-const V-const ⊑-$ ⊑-$ =
  ⟨ $ (f k) # b , ⟨ _ —→⟨ δ ⟩ _ ∎ , ⊑-$ ⟩ ⟩
sim-δ {f = f} {k} {ab} {a} {b} (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢W
      (V-wrap v i) w (⊑-wrapl A⊑A′ B⊑A′ (⊢$ f _ 𝐶⊢-$) V⊑f) W⊑k =
  case Inert-Cross⇒ c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩ →
      case ⟨ A⊑A′ , B⊑A′ ⟩ of λ where
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

sim-fun-cast : ∀ {A A′ B B′ C′ D′} {V V′ W W′}
                 {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
  → [] ⊢ V ⦂ A ⇒ B
  → [] ⊢ W ⦂ A
  → [] ⊢ V′ ⦂ A′ ⇒ B′
  → [] ⊢ W′ ⦂ C′
  → Value V → Value W → Value V′ → Value W′
  → (i′ : Inert c′) → (x′ : Cross c′)
  → [] , [] ⊢ V ⊑ V′ ⟨ c′ ₍ i′ ₎⟩
  → [] , [] ⊢ W ⊑ W′
    --------------------------------------------------------------------------------
  → ∃[ M ] (V · W —↠ M) ×
            ([] , [] ⊢ M ⊑ (V′ · (W′ ⟨ dom c′ x′ ⟩)) ⟨ cod c′ x′ ⟩)
sim-fun-cast {W = W} ⊢V ⊢W ⊢V′ ⊢W′ v w v′ w′ i′ x′
             (⊑-wrap {M = V} A⊑A′ B⊑B′ V⊑V′ imp) W⊑W′ =
  case v of λ where
    (V-wrap {A} {⋆} {c = c} v i) → contradiction (imp refl) λ ()
    (V-wrap {A} {B₁ ⇒ B₂} {c = c} v i) →
      case Inert-Cross⇒ c i of λ where
        ⟨ x , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩ →
          case ⟨ A⊑A′ , B⊑B′ ⟩ of λ where
            ⟨ fun⊑ A₁⊑A′ A₂⊑B′ , fun⊑ B₁⊑C′ B₂⊑D′ ⟩ →
              ⟨ (V · W ⟨ dom c x ⟩) ⟨ cod c x ⟩ ,
                ⟨ _ —→⟨ fun-cast v w {x} ⟩ _ ∎ ,
                  ⊑-cast A₂⊑B′ B₂⊑D′ (⊑-· V⊑V′ (⊑-cast B₁⊑C′ A₁⊑A′ W⊑W′)) ⟩ ⟩
sim-fun-cast {W = W} (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢W ⊢V′ ⊢W′ (V-wrap v i) w v′ w′ i′ x′
             (⊑-wrapl {M = V} A⊑A′ B⊑A′ ⊢V′c′ V⊑V′c′) W⊑W′ =
  case uniqueness ⊢V′c′ (⊢wrap _ i′ ⊢V′ 𝐶⊢-wrap) of λ where
    refl →
      case Inert-Cross⇒ c i of λ where
        ⟨ x , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩ →
          case ⟨ A⊑A′ , B⊑A′ ⟩ of λ where
            ⟨ fun⊑ A₁⊑C′ A₂⊑D′ , fun⊑ B₁⊑C′ B₂⊑D′ ⟩ →
              let ⊢Wdomc = ⊢cast (dom c x) ⊢W 𝐶⊢-cast in
              case catchup ⊢Wdomc w′ (⊑-castl B₁⊑C′ A₁⊑C′ ⊢W′ W⊑W′) of λ where
                ⟨ W₁ , ⟨ w₁ , ⟨ Wdomc↠W₁ , W₁⊑ ⟩ ⟩ ⟩ →
                  let ⊢W₁ = preserve-mult ⊢Wdomc Wdomc↠W₁ in
                  case sim-fun-cast ⊢V ⊢W₁ ⊢V′ ⊢W′ v w₁ v′ w′ i′ x′ V⊑V′c′ W₁⊑ of λ where
                    ⟨ N , ⟨ V·W₁↠N , N⊑ ⟩ ⟩ →
                      let ⊢V·Wdomc = ⊢· ⊢V ⊢Wdomc 𝐶⊢-·
                          wt-rhs   = ⊢cast (cod _ x′)
                                       (⊢· ⊢V′ (⊢cast (dom _ x′) ⊢W′ 𝐶⊢-cast) 𝐶⊢-·) 𝐶⊢-cast in
                      ⟨ N ⟨ cod c x ⟩ ,
                        ⟨ _ —→⟨ fun-cast v w {x} ⟩
                          ↠-trans (plug-cong (F-cast _) ⊢V·Wdomc
                                     (plug-cong (F-·₂ _ ⊢V v) ⊢Wdomc Wdomc↠W₁))
                                   (plug-cong (F-cast _) (⊢· ⊢V ⊢W₁ 𝐶⊢-·) V·W₁↠N) ,
                          ⊑-castl A₂⊑D′ B₂⊑D′ wt-rhs N⊑ ⟩ ⟩
sim-fun-cast {V = V} {W = W} ⊢V ⊢W ⊢V′ ⊢W′ v w v′ w′ i′ x′
             (⊑-wrapr A⊑A′ A⊑B′ ⊢V₁ V⊑V′ nd) W⊑W′ =
  case ⟨ A⊑A′ , A⊑B′ ⟩ of λ where
    ⟨ unk⊑ , unk⊑ ⟩ → contradiction refl nd
    ⟨ fun⊑ A⊑A′ B⊑B′ , fun⊑ A⊑C′ B⊑D′ ⟩ →
      case uniqueness ⊢V ⊢V₁ of λ where
       refl → ⟨ V · W , ⟨ _ ∎ ,
                 ⊑-castr B⊑B′ B⊑D′ (⊢· ⊢V ⊢W 𝐶⊢-·)
                   (⊑-· V⊑V′ (⊑-castr A⊑C′ A⊑A′ ⊢W W⊑W′)) ⟩ ⟩

sim-β-fst : ∀ {A A′ B B′} {V V′ W′}
  → [] ⊢ V ⦂ A `× B
  → [] ⊢ V′ ⦂ A′
  → [] ⊢ W′ ⦂ B′
  → Value V → Value V′ → Value W′
  → [] , [] ⊢ V ⊑ ⟦ V′ , W′ ⟧
    -----------------------------------------
  → ∃[ M ] (fst V —↠ M) × [] , [] ⊢ M ⊑ V′
sim-β-fst {V = ⟦ V , W ⟧} ⊢V ⊢V′ ⊢W′ (V-pair v w) v′ w′ (⊑-cons V⊑V′ W⊑W′) =
  ⟨ _ , ⟨ _ —→⟨ β-fst v w ⟩ _ ∎ , V⊑V′ ⟩ ⟩
sim-β-fst {V = V ⟨ c ₍ i ₎⟩} (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ ⊢W′ (V-wrap v i) v′ w′
          (⊑-wrapl A⊑A′ B⊑A′ (⊢cons ⊢V′† ⊢W′† 𝐶⊢-cons) V⊑V′W′) =
  case ⟨ uniqueness ⊢V′ ⊢V′† , uniqueness ⊢W′ ⊢W′† ⟩ of λ where
    ⟨ refl , refl ⟩ →
      case Inert-Cross× c i of λ where
        ⟨ x , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩ →
          case sim-β-fst ⊢V ⊢V′ ⊢W′ v v′ w′ V⊑V′W′ of λ where
            ⟨ M , ⟨ fstV↠M , M⊑V′ ⟩ ⟩ →
              case ⟨ A⊑A′ , B⊑A′ ⟩ of λ where
                ⟨ pair⊑ A₁⊑A₁′ A₂⊑A₂′ , pair⊑ B₁⊑B₁′ B₂⊑B₂′ ⟩ →
                  let ⊢fstV = ⊢fst ⊢V 𝐶⊢-fst in
                    ⟨ M ⟨ fstC c x ⟩ ,
                      ⟨ _ —→⟨ fst-cast v {x} ⟩ plug-cong (F-cast (fstC c x)) ⊢fstV fstV↠M ,
                      ⊑-castl A₁⊑A₁′ B₁⊑B₁′ ⊢V′ M⊑V′ ⟩ ⟩

sim-β-snd : ∀ {A A′ B B′} {V V′ W′}
  → [] ⊢ V ⦂ A `× B
  → [] ⊢ V′ ⦂ A′
  → [] ⊢ W′ ⦂ B′
  → Value V → Value V′ → Value W′
  → [] , [] ⊢ V ⊑ ⟦ V′ , W′ ⟧
    -----------------------------------------
  → ∃[ M ] (snd V —↠ M) × [] , [] ⊢ M ⊑ W′
sim-β-snd {V = ⟦ V , W ⟧} ⊢V ⊢V′ ⊢W′ (V-pair v w) v′ w′ (⊑-cons V⊑V′ W⊑W′) =
  ⟨ _ , ⟨ _ —→⟨ β-snd v w ⟩ _ ∎ , W⊑W′ ⟩ ⟩
sim-β-snd {V = V ⟨ c ₍ i ₎⟩} (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ ⊢W′ (V-wrap v i) v′ w′
          (⊑-wrapl A⊑A′ B⊑A′ (⊢cons ⊢V′† ⊢W′† 𝐶⊢-cons) V⊑V′W′) =
  case ⟨ uniqueness ⊢V′ ⊢V′† , uniqueness ⊢W′ ⊢W′† ⟩ of λ where
    ⟨ refl , refl ⟩ →
      case Inert-Cross× c i of λ where
        ⟨ x , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩ →
          case sim-β-snd ⊢V ⊢V′ ⊢W′ v v′ w′ V⊑V′W′ of λ where
            ⟨ M , ⟨ sndV↠M , M⊑W′ ⟩ ⟩ →
              case ⟨ A⊑A′ , B⊑A′ ⟩ of λ where
                ⟨ pair⊑ A₁⊑A₁′ A₂⊑A₂′ , pair⊑ B₁⊑B₁′ B₂⊑B₂′ ⟩ →
                  let ⊢sndV = ⊢snd ⊢V 𝐶⊢-snd in
                    ⟨ M ⟨ sndC c x ⟩ ,
                      ⟨ _ —→⟨ snd-cast v {x} ⟩ plug-cong (F-cast (sndC c x)) ⊢sndV sndV↠M ,
                      ⊑-castl A₂⊑A₂′ B₂⊑B₂′ ⊢W′ M⊑W′ ⟩ ⟩

ext-⇑-subst-zero : ∀ M → rename (ext ⇑) M [ ` 0 ] ≡ M
ext-⇑-subst-zero M =
  ⟪ subst-zero (` 0) ⟫ (rename (ext ⇑) M)
    ≡⟨ cong (λ □ → ⟪ _ ⟫ □) (rename-subst (ext ⇑) M) ⟩
  ⟪ subst-zero (` 0) ⟫ (⟪ rename→subst (ext ⇑) ⟫ M)
    ≡⟨ sub-sub {M} {rename→subst (ext ⇑)} {subst-zero (` 0)} ⟩
  ⟪ rename→subst (ext ⇑) ⨟ subst-zero (` 0) ⟫ M
    ≡⟨ cong (λ □ → ⟪ □ ⨟ subst-zero (` 0) ⟫ M) (rename→subst-ext ⇑) ⟩
  ⟪ ext (rename→subst ⇑) ⨟ subst-zero (` 0) ⟫ M
    ≡⟨ cong (λ □ → ⟪ □ ⟫ M) subst-zero-exts-cons ⟩
  ⟪ ` 0 • rename→subst ⇑ ⟫ M
    ≡⟨ sub-0•↑1 M ⟩
  M qed

cast-zero-⊑ : ∀ {A B A′ X X′} {M M′} {c : Cast (B ⇒ A)}
  → A ∷ [] ⊢ M ⦂ X → A′ ∷ [] ⊢ M′ ⦂ X′
  → A ⊑ A′ → B ⊑ A′
  → A ∷ [] , A′ ∷ [] ⊢ M ⊑ M′
    --------------------------------------------------------
  → B ∷ [] , A′ ∷ [] ⊢ rename (ext ⇑) M [ ` 0 ⟨ c ⟩ ] ⊑ M′
cast-zero-⊑ {A} {B} {A′} {M = M} {M′} {c} ⊢M ⊢M′ A⊑A′ B⊑A′ M⊑M′ =
  subst (λ □ → _ , _ ⊢ _ ⊑ □) (ext-⇑-subst-zero M′) lp
  where
  lp : B ∷ [] , A′ ∷ [] ⊢ rename (ext ⇑) M [ ` 0 ⟨ c ⟩ ] ⊑ rename (ext ⇑) M′ [ ` 0 ]
  lp = let ⊢ext⇑  = ext-⇑-wt [] A  B
           ⊢ext⇑′ = ext-⇑-wt [] A′ A′ in
       substitution-pres-⊑ (preserve-rename _ ⊢M  (λ {x}  → ⊢ext⇑  {x}))
                           (preserve-rename _ ⊢M′ (λ {x}  → ⊢ext⇑′ {x}))
                           (⊢cast c (⊢` refl) 𝐶⊢-cast) (⊢` refl)
                           (rename-pres-⊑ (λ {x} → ⊢ext⇑  {x})
                                          (λ {x} → ⊢ext⇑′ {x})
                                          M⊑M′)
                           (⊑-castl B⊑A′ A⊑A′ (⊢` refl) ⊑-`)

⊑-cast-zero : ∀ {A A′ B′ X X′} {M M′} {c′ : Cast (B′ ⇒ A′)}
  → A ∷ [] ⊢ M ⦂ X → A′ ∷ [] ⊢ M′ ⦂ X′
  → A ⊑ A′ → A ⊑ B′
  → A ∷ [] , A′ ∷ [] ⊢ M ⊑ M′
    ---------------------------------------------------------
  → A ∷ [] , B′ ∷ [] ⊢ M ⊑ rename (ext ⇑) M′ [ ` 0 ⟨ c′ ⟩ ]
⊑-cast-zero {A} {A′} {B′} {M = M} {M′} {c′} ⊢M ⊢M′ A⊑A′ A⊑B′ M⊑M′ =
  subst (λ □ → _ , _ ⊢ □ ⊑ _) (ext-⇑-subst-zero M) lp
  where
  lp : A ∷ [] , B′ ∷ [] ⊢ rename (ext ⇑) M [ ` 0 ] ⊑ rename (ext ⇑) M′ [ ` 0 ⟨ c′ ⟩ ]
  lp = let ⊢ext⇑  = ext-⇑-wt [] A  A
           ⊢ext⇑′ = ext-⇑-wt [] A′ B′ in
       substitution-pres-⊑ (preserve-rename _ ⊢M  (λ {x}  → ⊢ext⇑  {x}))
                           (preserve-rename _ ⊢M′ (λ {x}  → ⊢ext⇑′ {x}))
                           (⊢` refl) (⊢cast c′ (⊢` refl) 𝐶⊢-cast)
                           (rename-pres-⊑ (λ {x} → ⊢ext⇑  {x})
                                          (λ {x} → ⊢ext⇑′ {x})
                                          M⊑M′)
                           (⊑-castr A⊑B′ A⊑A′ (⊢` refl) ⊑-`)

sim-case-cast : ∀ {A A₁′ A₂′ B B₁′ B₂′ C C′} {V V′ M M′ N N′}
                  {c′ : Cast ((A₁′ `⊎ B₁′) ⇒ (A₂′ `⊎ B₂′))}
  →       [] ⊢ V  ⦂ A   `⊎ B
  →       [] ⊢ V′ ⦂ A₁′ `⊎ B₁′
  → A   ∷ [] ⊢ M  ⦂ C
  → A₂′ ∷ [] ⊢ M′ ⦂ C′
  → B   ∷ [] ⊢ N  ⦂ C
  → B₂′ ∷ [] ⊢ N′ ⦂ C′
  → Value V → Value V′
  → (i′ : Inert c′) → (x′ : Cross c′)
  →     [] ,       [] ⊢ V ⊑ V′ ⟨ c′ ₍ i′ ₎⟩
  → A ∷ [] , A₂′ ∷ [] ⊢ M ⊑ M′
  → B ∷ [] , B₂′ ∷ [] ⊢ N ⊑ N′
    --------------------------------------------
  → ∃[ L ] (case V of A ⇒ M ∣ B ⇒ N —↠ L) ×
       [] , [] ⊢ L ⊑ case V′ of A₁′ ⇒ (rename (ext ⇑) M′ [ ` 0 ⟨ inlC c′ x′ ⟩ ])
                              ∣ B₁′ ⇒ (rename (ext ⇑) N′ [ ` 0 ⟨ inrC c′ x′ ⟩ ])
-- case on V ⊑ V′ ⟨ c′ ₍ i′ ₎⟩
sim-case-cast {A} {A₁′} {A₂′} {B} {B₁′} {B₂′} {C} {C′} {V = V ⟨ c ₍ i ₎⟩} {V′} {M} {M′} {N} {N′}
  (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ ⊢M ⊢M′ ⊢N ⊢N′ (V-wrap v i) v′ i′ x′ (⊑-wrap A⊑A′ B⊑B′ V⊑V′ imp) M⊑M′ N⊑N′ =
  case Inert-Cross⊎ c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ B₁ , refl ⟩ ⟩ ⟩ →
      case ⟨ A⊑A′ , B⊑B′ ⟩ of λ where
        ⟨ sum⊑ A₁⊑A₁′ B₁⊑B₁′ , sum⊑ A₂⊑A₂′ B₂⊑B₂′ ⟩ →
          let ⊢ext⇑  = ext-⇑-wt [] A   A₁  {- ext ⇑ ⦂ [ A₂ ] ⇒ [ A₂ ; A₁ ] -}
              ⊢ext⇑′ = ext-⇑-wt [] A₂′ A₁′ in
          ⟨ _ , ⟨ _ —→⟨ case-cast v {x} ⟩ _ ∎ ,
            ⊑-case V⊑V′ A₁⊑A₁′ B₁⊑B₁′
              (substitution-pres-⊑
                (preserve-rename M  ⊢M  (λ {x} → ⊢ext⇑  {x}))
                (preserve-rename M′ ⊢M′ (λ {x} → ⊢ext⇑′ {x}))
                (⊢cast (inlC _ x)  {- inlC c -}  (⊢` refl) 𝐶⊢-cast)
                (⊢cast (inlC _ x′) {- inlC c′ -} (⊢` refl) 𝐶⊢-cast)
                (rename-pres-⊑ (λ {x} → ⊢ext⇑ {x}) (λ {x} → ⊢ext⇑′ {x}) M⊑M′)
                (⊑-cast A₁⊑A₁′ A₂⊑A₂′ ⊑-`))
              (substitution-pres-⊑
                (preserve-rename N  ⊢N  (λ {x} → ext-⇑-wt [] B B₁ {x}))
                (preserve-rename N′ ⊢N′ (λ {x} → ext-⇑-wt [] B₂′ B₁′ {x}))
                (⊢cast (inrC _ x)  {- inrC c -}  (⊢` refl) 𝐶⊢-cast)
                (⊢cast (inrC _ x′) {- inrC c′ -} (⊢` refl) 𝐶⊢-cast)
                (rename-pres-⊑ (λ {x} → ext-⇑-wt [] B   B₁  {x})
                               (λ {x} → ext-⇑-wt [] B₂′ B₁′ {x}) N⊑N′)
                (⊑-cast B₁⊑B₁′ B₂⊑B₂′ ⊑-`))⟩ ⟩
sim-case-cast {A} {A₁′} {A₂′} {B} {B₁′} {B₂′} {C} {C′} {V = V ⟨ c ₍ i ₎⟩} {V′} {M} {M′} {N} {N′}
  (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ ⊢M ⊢M′ ⊢N ⊢N′ (V-wrap v i) v′ i′ x′ (⊑-wrapl A⊑A′ B⊑A′ (⊢wrap c′ i′ ⊢V′† 𝐶⊢-wrap) V⊑V′) M⊑M′ N⊑N′ =
  case Inert-Cross⊎ c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ B₁ , refl ⟩ ⟩ ⟩ →
      case ⟨ A⊑A′ , B⊑A′ ⟩ of λ where
        ⟨ sum⊑ A₁⊑A₂′ B₁⊑B₂′ , sum⊑ A₂⊑A₂′ B₂⊑B₂′ ⟩ →
              let ⊢left  = preserve-substitution _ _
                             (preserve-rename _ ⊢M (λ {x} → ext-⇑-wt [] A A₁ {x}))
                             (⊢cast (inlC c x) (⊢` refl) 𝐶⊢-cast)
                  ⊢right = preserve-substitution _ _
                             (preserve-rename _ ⊢N (λ {x} → ext-⇑-wt [] B B₁ {x}))
                             (⊢cast (inrC c x) (⊢` refl) 𝐶⊢-cast) in
          case sim-case-cast ⊢V ⊢V′† ⊢left ⊢M′ ⊢right ⊢N′ v v′ i′ x′ V⊑V′
                             (cast-zero-⊑ ⊢M ⊢M′ A₂⊑A₂′ A₁⊑A₂′ M⊑M′)
                             (cast-zero-⊑ ⊢N ⊢N′ B₂⊑B₂′ B₁⊑B₂′ N⊑N′) of λ where
            ⟨ L , ⟨ case↠L , L⊑case ⟩ ⟩ →
              ⟨ L , ⟨ _ —→⟨ case-cast v {x} ⟩ case↠L , L⊑case ⟩ ⟩
sim-case-cast {A} {A₁′} {A₂′} {B} {B₁′} {B₂′} {C} {C′} {V = V} {V′} {M} {M′} {N} {N′}
  ⊢V ⊢V′ ⊢M ⊢M′ ⊢N ⊢N′ v v′ i′ x′ (⊑-wrapr A⊑A′ A⊑B′ ⊢V† V⊑V′ nd) M⊑M′ N⊑N′ =
  case ⟨ ⊑⊎-nd A⊑A′ nd , ⊑⊎-nd A⊑B′ nd ⟩ of λ where
    ⟨ ⟨ A , ⟨ B , refl ⟩ ⟩ , ⟨ A , ⟨ B , refl ⟩ ⟩ ⟩ →
      case ⟨ uniqueness ⊢V ⊢V† , ⟨ A⊑A′ , A⊑B′ ⟩ ⟩ of λ where
        ⟨ refl , ⟨ sum⊑ A⊑A₁′ B⊑B₁′ , sum⊑ A⊑A₂′ B⊑B₂′ ⟩ ⟩ →
          ⟨ _ , ⟨ _ ∎ ,
            ⊑-case V⊑V′ A⊑A₁′ B⊑B₁′
                   (⊑-cast-zero ⊢M ⊢M′ A⊑A₂′ A⊑A₁′ M⊑M′)
                   (⊑-cast-zero ⊢N ⊢N′ B⊑B₂′ B⊑B₁′ N⊑N′) ⟩ ⟩

sim-β-caseL : ∀ {A A′ B B′ C C′} {V V′ M M′ N N′}
  →      [] ⊢ V  ⦂ A `⊎ B
  →      [] ⊢ V′ ⦂ A′
  → A  ∷ [] ⊢ M  ⦂ C
  → A′ ∷ [] ⊢ M′ ⦂ C′
  → B  ∷ [] ⊢ N  ⦂ C
  → B′ ∷ [] ⊢ N′ ⦂ C′
  → Value V → Value V′
  →     [] ,      [] ⊢ V ⊑ inl V′ other B′
  → A ∷ [] , A′ ∷ [] ⊢ M ⊑ M′
  → B ∷ [] , B′ ∷ [] ⊢ N ⊑ N′
    --------------------------------------------------------
  → ∃[ L ] (case V of A ⇒ M ∣ B ⇒ N —↠ L) × [] , [] ⊢ L ⊑ M′ [ V′ ]
sim-β-caseL (⊢inl B ⊢V 𝐶⊢-inl) ⊢V′ ⊢M ⊢M′ ⊢N ⊢N′ (V-inl {B} v) v′ (⊑-inl B⊑B′ V⊑V′) M⊑M′ N⊑N′ =
  ⟨ _ , ⟨ _ —→⟨ β-caseL v ⟩ _ ∎ , substitution-pres-⊑ ⊢M ⊢M′ ⊢V ⊢V′ M⊑M′ V⊑V′ ⟩ ⟩
sim-β-caseL {A} {A′} {B} {B′} (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ ⊢M ⊢M′ ⊢N ⊢N′ (V-wrap v i) v′
            (⊑-wrapl A₁⊎B₁⊑A′⊎B′ A⊎B⊑A′⊎B′ (⊢inl B′ ⊢V′† 𝐶⊢-inl) V⊑inlV′) M⊑M′ N⊑N′ =
  case Inert-Cross⊎ c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ B₁ , refl ⟩ ⟩ ⟩ →
      case ⟨ uniqueness ⊢V′ ⊢V′† , ⟨ A₁⊎B₁⊑A′⊎B′ , A⊎B⊑A′⊎B′ ⟩ ⟩ of λ where
        ⟨ refl , ⟨ sum⊑ A₁⊑A′ B₁⊑B′ , sum⊑ A⊑A′ B⊑B′ ⟩ ⟩ →
          let ⊢left  = preserve-substitution _ _
                         (preserve-rename _ ⊢M (λ {x} → ext-⇑-wt [] A A₁ {x}))
                         (⊢cast (inlC c x) (⊢` refl) 𝐶⊢-cast)
              ⊢right = preserve-substitution _ _
                         (preserve-rename _ ⊢N (λ {x} → ext-⇑-wt [] B B₁ {x}))
                         (⊢cast (inrC c x) (⊢` refl) 𝐶⊢-cast) in
          case sim-β-caseL ⊢V ⊢V′ ⊢left ⊢M′ ⊢right ⊢N′ v v′ V⊑inlV′
                           (cast-zero-⊑ ⊢M ⊢M′ A⊑A′ A₁⊑A′ M⊑M′)
                           (cast-zero-⊑ ⊢N ⊢N′ B⊑B′ B₁⊑B′ N⊑N′) of λ where
            ⟨ L , ⟨ case↠L , L⊑M′[V′] ⟩ ⟩ →
              ⟨ L , ⟨ _ —→⟨ case-cast v {x} ⟩ case↠L , L⊑M′[V′] ⟩ ⟩

sim-β-caseR : ∀ {A A′ B B′ C C′} {V V′ M M′ N N′}
  →      [] ⊢ V  ⦂ A `⊎ B
  →      [] ⊢ V′ ⦂ B′
  → A  ∷ [] ⊢ M  ⦂ C
  → A′ ∷ [] ⊢ M′ ⦂ C′
  → B  ∷ [] ⊢ N  ⦂ C
  → B′ ∷ [] ⊢ N′ ⦂ C′
  → Value V → Value V′
  →     [] ,      [] ⊢ V ⊑ inr V′ other A′
  → A ∷ [] , A′ ∷ [] ⊢ M ⊑ M′
  → B ∷ [] , B′ ∷ [] ⊢ N ⊑ N′
    --------------------------------------------------------
  → ∃[ L ] (case V of A ⇒ M ∣ B ⇒ N —↠ L) × [] , [] ⊢ L ⊑ N′ [ V′ ]
sim-β-caseR (⊢inr A ⊢V 𝐶⊢-inr) ⊢V′ ⊢M ⊢M′ ⊢N ⊢N′ (V-inr {A} v) v′ (⊑-inr A⊑A′ V⊑V′) M⊑M′ N⊑N′ =
  ⟨ _ , ⟨ _ —→⟨ β-caseR v ⟩ _ ∎ , substitution-pres-⊑ ⊢N ⊢N′ ⊢V ⊢V′ N⊑N′ V⊑V′ ⟩ ⟩
sim-β-caseR {A} {A′} {B} {B′} (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ ⊢M ⊢M′ ⊢N ⊢N′ (V-wrap v i) v′
            (⊑-wrapl A₁⊎B₁⊑A′⊎B′ A⊎B⊑A′⊎B′ (⊢inr A′ ⊢V′† 𝐶⊢-inr) V⊑inrV′) M⊑M′ N⊑N′ =
  case Inert-Cross⊎ c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ B₁ , refl ⟩ ⟩ ⟩ →
      case ⟨ uniqueness ⊢V′ ⊢V′† , ⟨ A₁⊎B₁⊑A′⊎B′ , A⊎B⊑A′⊎B′ ⟩ ⟩ of λ where
        ⟨ refl , ⟨ sum⊑ A₁⊑A′ B₁⊑B′ , sum⊑ A⊑A′ B⊑B′ ⟩ ⟩ →
          let ⊢left  = preserve-substitution _ _
                         (preserve-rename _ ⊢M (λ {x} → ext-⇑-wt [] A A₁ {x}))
                         (⊢cast (inlC c x) (⊢` refl) 𝐶⊢-cast)
              ⊢right = preserve-substitution _ _
                         (preserve-rename _ ⊢N (λ {x} → ext-⇑-wt [] B B₁ {x}))
                         (⊢cast (inrC c x) (⊢` refl) 𝐶⊢-cast) in
          case sim-β-caseR ⊢V ⊢V′ ⊢left ⊢M′ ⊢right ⊢N′ v v′ V⊑inrV′
                           (cast-zero-⊑ ⊢M ⊢M′ A⊑A′ A₁⊑A′ M⊑M′)
                           (cast-zero-⊑ ⊢N ⊢N′ B⊑B′ B₁⊑B′ N⊑N′) of λ where
            ⟨ L , ⟨ case↠L , L⊑N′[V′] ⟩ ⟩ →
              ⟨ L , ⟨ _ —→⟨ case-cast v {x} ⟩ case↠L , L⊑N′[V′] ⟩ ⟩

sim-fst-cast : ∀ {A A₁′ A₂′ B B₁′ B₂′} {V V′} {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
  → [] ⊢ V  ⦂ A   `× B
  → [] ⊢ V′ ⦂ A₁′ `× B₁′
  → Value V → Value V′
  → (i′ : Inert c′) → (x′ : Cross c′)
  → [] , [] ⊢ V ⊑ V′ ⟨ c′ ₍ i′ ₎⟩
    ------------------------------------------------------------
  → ∃[ M ] (fst V —↠ M) × [] , [] ⊢ M ⊑ fst V′ ⟨ fstC c′ x′ ⟩
sim-fst-cast (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ (V-wrap v i) v′ i′ x′ (⊑-wrap A₁×B₁⊑A₁′×B₁′ A×B⊑A₂′×B₂′ V⊑V′ imp) =
  case Inert-Cross× c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ B₁ , refl ⟩ ⟩ ⟩ →
      case ⟨ A₁×B₁⊑A₁′×B₁′ , A×B⊑A₂′×B₂′ ⟩ of λ where
        ⟨ pair⊑ A₁⊑A₁′ B₁⊑B₁′ , pair⊑ A⊑A₂′ B⊑B₂′ ⟩ →
          ⟨ _ , ⟨ _ —→⟨ fst-cast v {x} ⟩ _ ∎ ,
                  ⊑-cast A₁⊑A₁′ A⊑A₂′ (⊑-fst V⊑V′) ⟩ ⟩
sim-fst-cast (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ (V-wrap v i) v′ i′ x′
             (⊑-wrapl A₁×B₁⊑A₂′×B₂′ A×B⊑A₂′×B₂′ (⊢wrap c′ i′ ⊢V′† 𝐶⊢-wrap) V⊑V′c′) =
  case Inert-Cross× c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ B₁ , refl ⟩ ⟩ ⟩ →
      case ⟨ A₁×B₁⊑A₂′×B₂′ , A×B⊑A₂′×B₂′ ⟩ of λ where
        ⟨ pair⊑ A₁⊑A₂′ B₁⊑B₂′ , pair⊑ A⊑A₂′ B⊑B₂′ ⟩ →
          case sim-fst-cast ⊢V ⊢V′† v v′ i′ x′ V⊑V′c′ of λ where
            ⟨ M , ⟨ fst↠M , M⊑fst-cast ⟩ ⟩ →
              ⟨ M ⟨ fstC c x ⟩ ,
                ⟨ _ —→⟨ fst-cast v {x} ⟩ plug-cong (F-cast (fstC c x)) (⊢fst ⊢V 𝐶⊢-fst) fst↠M ,
                  ⊑-castl A₁⊑A₂′ A⊑A₂′ (⊢cast (fstC c′ x′) (⊢fst ⊢V′† 𝐶⊢-fst) 𝐶⊢-cast) M⊑fst-cast ⟩ ⟩
sim-fst-cast ⊢V ⊢V′ v v′ i′ x′ (⊑-wrapr A×B⊑A₁′×B₁′ A×B⊑A₂′×B₂′ ⊢V† V⊑V′ nd) =
  case ⟨ uniqueness ⊢V ⊢V† , ⟨ A×B⊑A₁′×B₁′ , A×B⊑A₂′×B₂′ ⟩ ⟩ of λ where
    ⟨ refl , ⟨ pair⊑ A⊑A₁′ B⊑B₁′ , pair⊑ A⊑A₂′ B⊑B₂′ ⟩ ⟩ →
      ⟨ _ , ⟨ _ ∎ , (⊑-castr A⊑A₁′ A⊑A₂′ (⊢fst ⊢V† 𝐶⊢-fst) (⊑-fst V⊑V′)) ⟩ ⟩

sim-snd-cast : ∀ {A A₁′ A₂′ B B₁′ B₂′} {V V′} {c′ : Cast ((A₁′ `× B₁′) ⇒ (A₂′ `× B₂′))}
  → [] ⊢ V  ⦂ A   `× B
  → [] ⊢ V′ ⦂ A₁′ `× B₁′
  → Value V → Value V′
  → (i′ : Inert c′) → (x′ : Cross c′)
  → [] , [] ⊢ V ⊑ V′ ⟨ c′ ₍ i′ ₎⟩
    ------------------------------------------------------------
  → ∃[ M ] (snd V —↠ M) × [] , [] ⊢ M ⊑ snd V′ ⟨ sndC c′ x′ ⟩
sim-snd-cast (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ (V-wrap v i) v′ i′ x′ (⊑-wrap A₁×B₁⊑A₁′×B₁′ A×B⊑A₂′×B₂′ V⊑V′ imp) =
  case Inert-Cross× c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ B₁ , refl ⟩ ⟩ ⟩ →
      case ⟨ A₁×B₁⊑A₁′×B₁′ , A×B⊑A₂′×B₂′ ⟩ of λ where
        ⟨ pair⊑ A₁⊑A₁′ B₁⊑B₁′ , pair⊑ A⊑A₂′ B⊑B₂′ ⟩ →
          ⟨ _ , ⟨ _ —→⟨ snd-cast v {x} ⟩ _ ∎ ,
                  ⊑-cast B₁⊑B₁′ B⊑B₂′ (⊑-snd V⊑V′) ⟩ ⟩
sim-snd-cast (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ (V-wrap v i) v′ i′ x′
             (⊑-wrapl A₁×B₁⊑A₂′×B₂′ A×B⊑A₂′×B₂′ (⊢wrap c′ i′ ⊢V′† 𝐶⊢-wrap) V⊑V′c′) =
  case Inert-Cross× c i of λ where
    ⟨ x , ⟨ A₁ , ⟨ B₁ , refl ⟩ ⟩ ⟩ →
      case ⟨ A₁×B₁⊑A₂′×B₂′ , A×B⊑A₂′×B₂′ ⟩ of λ where
        ⟨ pair⊑ A₁⊑A₂′ B₁⊑B₂′ , pair⊑ A⊑A₂′ B⊑B₂′ ⟩ →
          case sim-snd-cast ⊢V ⊢V′† v v′ i′ x′ V⊑V′c′ of λ where
            ⟨ M , ⟨ snd↠M , M⊑snd-cast ⟩ ⟩ →
              ⟨ M ⟨ sndC c x ⟩ ,
                ⟨ _ —→⟨ snd-cast v {x} ⟩ plug-cong (F-cast (sndC c x)) (⊢snd ⊢V 𝐶⊢-snd) snd↠M ,
                  ⊑-castl B₁⊑B₂′ B⊑B₂′ (⊢cast (sndC c′ x′) (⊢snd ⊢V′† 𝐶⊢-snd) 𝐶⊢-cast) M⊑snd-cast ⟩ ⟩
sim-snd-cast ⊢V ⊢V′ v v′ i′ x′ (⊑-wrapr A×B⊑A₁′×B₁′ A×B⊑A₂′×B₂′ ⊢V† V⊑V′ nd) =
  case ⟨ uniqueness ⊢V ⊢V† , ⟨ A×B⊑A₁′×B₁′ , A×B⊑A₂′×B₂′ ⟩ ⟩ of λ where
    ⟨ refl , ⟨ pair⊑ A⊑A₁′ B⊑B₁′ , pair⊑ A⊑A₂′ B⊑B₂′ ⟩ ⟩ →
      ⟨ _ , ⟨ _ ∎ , (⊑-castr B⊑B₁′ B⊑B₂′ (⊢snd ⊢V† 𝐶⊢-snd) (⊑-snd V⊑V′)) ⟩ ⟩

-- wrap-castr* : ∀ {A′ B′} {V V′} {c′ : Cast (A′ ⇒ B′)}
--   → (i′ : Inert c′)
--   → [] ⊢ V ⦂ ⋆ → [] ⊢ V′ ⦂ A′
--   → Value V → Value V′
--   → [] , [] ⊢ V ⊑ V′
--     ------------------------------
--   → [] , [] ⊢ V ⊑ V′ ⟨ c′ ₍ i′ ₎⟩
-- wrap-castr* i′ ⊢V ⊢V′ v v′ V⊑V′ with canonical⋆ ⊢V v
-- wrap-castr* {A′} {B′} {V = V ⟨ c ₍ i ₎⟩} {V′} {c′} i′ (⊢wrap c i ⊢V 𝐶⊢-wrap) ⊢V′ (V-wrap v i) v′ V⊑V′
--   | ⟨ A , ⟨ V , ⟨ c , ⟨ i , refl ⟩ ⟩ ⟩ ⟩ =
--   case V⊑V′ of λ where
--     (⊑-wrap _ _ _ imp) →
--       case ⊢V′ of λ where
--         (⊢wrap _ _ _ 𝐶⊢-wrap) →
--           -- case analysis on A′ and B′
--           let A′≡⋆ = imp refl in
--           case ⟨ A′≡⋆ , eq-unk B′ ⟩ of λ where
--             ⟨ refl , yes refl ⟩ → contradiction i′ (idNotInert A-Unk c′)
--             ⟨ refl , no  B′≢⋆ ⟩ → contradiction i′ (projNotInert B′≢⋆ c′)
--     (⊑-wrapr _ _ (⊢wrap _ _ _ 𝐶⊢-wrap) _ nd) →
--       contradiction refl nd
--     (⊑-wrapl A⊑A′ unk⊑ ⊢V′† V⊑V′) →
--       case uniqueness ⊢V′ ⊢V′† of λ where
--         refl →
--           ⊑-wrapl {!!} {- A ⊑ B′ -} unk⊑ (⊢wrap c′ i′ ⊢V′ 𝐶⊢-wrap)
--             (⊑-wrapr A⊑A′ {!!} ⊢V V⊑V′ {!!} {- A ≢ ⋆ -})

-- wrap-castr : ∀ {A A′ B′} {V V′} {c′ : Cast (A′ ⇒ B′)}
--   → (i′ : Inert c′)
--   → [] ⊢ V ⦂ A → [] ⊢ V′ ⦂ A′
--   → Value V → (v′ : Value V′)
--   → A ⊑ A′ → A ⊑ B′
--   → [] , [] ⊢ V ⊑ V′
--     -----------------------------------------------------
--   → [] , [] ⊢ V ⊑ V′ ⟨ c′ ₍ i′ ₎⟩
