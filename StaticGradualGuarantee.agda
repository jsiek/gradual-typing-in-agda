open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Types
open import Variables
open import Labels
open import GTLC
open import GTLCPrecision


module StaticGradualGuarantee where

  ctx-prec-var : ∀ {Γ Γ′ A′} {x : ℕ}
    → Γ ⊑* Γ′
    → Γ′ ∋ x ⦂ A′
    → ∃[ A ] (Γ ∋ x ⦂ A) × (A ⊑ A′)
  ctx-prec-var (⊑*-, lp lp*) Z = ⟨ _ , ⟨ Z , lp ⟩ ⟩
  ctx-prec-var (⊑*-, lp lp*) (S ∋x) =
    let ⟨ A , ⟨ ∋n , lpA ⟩ ⟩ = ctx-prec-var lp* ∋x in ⟨ A , ⟨ S ∋n , lpA ⟩ ⟩

  static-gradual-guarantee : ∀ {Γ Γ′ A′} {M M′ : Term}
    → Γ′ ⊢G M′ ⦂ A′
    → Γ ⊑* Γ′
    → M ⊑ᴳ M′
      -------------------------------
    → ∃[ A ] (Γ ⊢G M ⦂ A) × (A ⊑ A′)
  static-gradual-guarantee (⊢var ∋x) lp* ⊑ᴳ-var =
    let ⟨ A , ⟨ ∋n , lpA ⟩ ⟩ = ctx-prec-var lp* ∋x in
      ⟨ A , ⟨ ⊢var ∋n , lpA ⟩ ⟩
  static-gradual-guarantee (⊢lam ⊢N′) lp* (⊑ᴳ-ƛ lp lpN) =
    let ⟨ B , ⟨ ⊢N , lpB ⟩ ⟩ = static-gradual-guarantee ⊢N′ (⊑*-, lp lp*) lpN in
      ⟨ _ , ⟨ ⊢lam ⊢N , fun⊑ lp lpB ⟩ ⟩
  static-gradual-guarantee (⊢app ⊢L′ ⊢M′ m c~) lp* (⊑ᴳ-· lpL lpM)
    with static-gradual-guarantee ⊢L′ lp* lpL
  ... | ⟨ AB , ⟨ ⊢L , lpAB ⟩ ⟩
    with static-gradual-guarantee ⊢M′ lp* lpM
  ...   | ⟨ B , ⟨ ⊢M , lpB ⟩ ⟩ with lpAB
  ...     | unk⊑ = ⟨ _ , ⟨ ⊢app ⊢L ⊢M match⇒⋆ unk~L , unk⊑ ⟩ ⟩
  ...     | fun⊑ lp1 lp2 with m
  ...       | match⇒⇒ =
      ⟨ _ , ⟨ ⊢app ⊢L ⊢M match⇒⇒ (lp-consis c~ lp1 lpB) , lp2 ⟩ ⟩
  static-gradual-guarantee ⊢lit lp* ⊑ᴳ-prim = ⟨ _ , ⟨ ⊢lit , Refl⊑ ⟩ ⟩
  static-gradual-guarantee (⊢if ⊢L′ ⊢M′ ⊢N′ c~ d~) lp* (⊑ᴳ-if lpL lpM lpN)
    with static-gradual-guarantee ⊢L′ lp* lpL | static-gradual-guarantee ⊢M′ lp* lpM | static-gradual-guarantee ⊢N′ lp* lpN
  ... | ⟨ B , ⟨ ⊢L , lpB ⟩ ⟩ | ⟨ A , ⟨ ⊢M , lpA ⟩ ⟩ | ⟨ A' , ⟨ ⊢N , lpA' ⟩ ⟩ =
    ⟨ _ , ⟨ ⊢if ⊢L ⊢M ⊢N (lp-consis c~ lpB Refl⊑) (lp-consis d~ lpA lpA') , ⨆-pres-prec _ _ lpA lpA' ⟩ ⟩
  static-gradual-guarantee (⊢cons ⊢M′ ⊢N′) lp* (⊑ᴳ-cons lpM lpN)
    with static-gradual-guarantee ⊢M′ lp* lpM | static-gradual-guarantee ⊢N′ lp* lpN
  ... | ⟨ A , ⟨ ⊢M , lpA ⟩ ⟩ | ⟨ B , ⟨ ⊢N , lpB ⟩ ⟩ =
    ⟨ _ , ⟨ ⊢cons ⊢M ⊢N , pair⊑ lpA lpB ⟩ ⟩
  static-gradual-guarantee (⊢fst ⊢M′ m) lp* (⊑ᴳ-fst lpM)
    with static-gradual-guarantee ⊢M′ lp* lpM
  ... | ⟨ A , ⟨ ⊢M , lpA ⟩ ⟩ with m | lpA
  ...   | match×⋆ | unk⊑ = ⟨ _ , ⟨ ⊢fst ⊢M match×⋆ , unk⊑ ⟩ ⟩
  ...   | match×× | unk⊑ = ⟨ _ , ⟨ ⊢fst ⊢M match×⋆ , unk⊑ ⟩ ⟩
  ...   | match×× | pair⊑ lp1 lp2 = ⟨ _ , ⟨ ⊢fst ⊢M match×× , lp1 ⟩ ⟩
  static-gradual-guarantee (⊢snd ⊢M′ m) lp* (⊑ᴳ-snd lpM)
    with static-gradual-guarantee ⊢M′ lp* lpM
  ... | ⟨ A , ⟨ ⊢M , lpA ⟩ ⟩ with m | lpA
  ...   | match×⋆ | unk⊑ = ⟨ _ , ⟨ ⊢snd ⊢M match×⋆ , unk⊑ ⟩ ⟩
  ...   | match×× | unk⊑ = ⟨ _ , ⟨ ⊢snd ⊢M match×⋆ , unk⊑ ⟩ ⟩
  ...   | match×× | pair⊑ lp1 lp2 = ⟨ _ , ⟨ ⊢snd ⊢M match×× , lp2 ⟩ ⟩
  static-gradual-guarantee (⊢inl ⊢M′) lp* (⊑ᴳ-inl lp lpM)
    with static-gradual-guarantee ⊢M′ lp* lpM
  ... | ⟨ A , ⟨ ⊢M , lpA ⟩ ⟩ = ⟨ _ , ⟨ ⊢inl ⊢M , sum⊑ lpA lp ⟩ ⟩
  static-gradual-guarantee (⊢inr ⊢M′) lp* (⊑ᴳ-inr lp lpM)
    with static-gradual-guarantee ⊢M′ lp* lpM
  ... | ⟨ B , ⟨ ⊢M , lpB ⟩ ⟩ = ⟨ _ , ⟨ ⊢inr ⊢M , sum⊑ lp lpB ⟩ ⟩
  static-gradual-guarantee (⊢case ⊢L′ ⊢M′ ⊢N′ c~ d~) lp* (⊑ᴳ-case lpL lp1 lp2 lpM lpN)
    with static-gradual-guarantee ⊢L′ lp* lpL | static-gradual-guarantee ⊢M′ (⊑*-, lp1 lp*) lpM | static-gradual-guarantee ⊢N′ (⊑*-, lp2 lp*) lpN
  ... | ⟨ A , ⟨ ⊢L , lpA ⟩ ⟩ | ⟨ B , ⟨ ⊢M , lpB ⟩ ⟩ | ⟨ C , ⟨ ⊢N , lpC ⟩ ⟩ =
    ⟨ _ , ⟨ ⊢case ⊢L ⊢M ⊢N (lp-consis c~ lpA (sum⊑ lp1 lp2)) (lp-consis d~ lpB lpC) , ⨆-pres-prec _ _ lpB lpC ⟩ ⟩
