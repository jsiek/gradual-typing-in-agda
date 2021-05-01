open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Types
open import Variables
open import Labels
open import GTLC

open import PreCastStructureWithPrecision

module CompilePresPrec
  (pcsp : PreCastStructWithPrecision)
  where

open PreCastStructWithPrecision pcsp
open import ParamCastCalculus Cast Inert

open import GTLCPrecision
open import ParamCCPrecision pcsp

module CompilePresPrecProof
  (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
  where


  open import GTLC2CC Cast Inert cast

  {-
    Compilation from GTLC to CC preserves precision.
      - We assume Γ ⊢ M ↝ f ⦂ A and Γ′ ⊢ M′ ↝ f′ ⦂ A′ .
  -}
  compile-pres-prec : ∀ {Γ Γ′ A A′} {M M′}
    → (⊢M : Γ ⊢G M ⦂ A) → (⊢M′ : Γ′ ⊢G M′ ⦂ A′)
    → Γ ⊑* Γ′
    → M ⊑ᴳ M′
      -------------------------------
    → (A ⊑ A′) × (Γ , Γ′ ⊢ compile {Γ} {A} M ⊢M ⊑ᶜ compile {Γ′} {A′} M′ ⊢M′)
  compile-pres-prec ⊢lit ⊢lit lpc ⊑ᴳ-prim = ⟨ Refl⊑ , ⊑ᶜ-prim ⟩
  compile-pres-prec (⊢var {x = 0} Z) (⊢var Z) (⊑*-, lp _) (⊑ᴳ-var {.0}) = ⟨ lp , ⊑ᶜ-var refl ⟩
  compile-pres-prec (⊢var {x = suc x} (S ∋x)) (⊢var (S ∋x′)) (⊑*-, lp lpc) (⊑ᴳ-var {.(suc x)})
    with compile-pres-prec (⊢var ∋x) (⊢var ∋x′) lpc ⊑ᴳ-var
  ... | ⟨ IH₁ , ⊑ᶜ-var IH₂ ⟩ = ⟨ IH₁ , (⊑ᶜ-var (cong suc IH₂)) ⟩
  compile-pres-prec (⊢lam ⊢M) (⊢lam ⊢M′) lpc (⊑ᴳ-ƛ lpA lpM) =
    let ⟨ lpB , lpN ⟩ = compile-pres-prec ⊢M ⊢M′ (⊑*-, lpA lpc) lpM in
      ⟨ fun⊑ lpA lpB , ⊑ᶜ-ƛ lpA lpN ⟩
  compile-pres-prec (⊢app ⊢L ⊢M m _) (⊢app ⊢L′ ⊢M′ m′ _) lpc (⊑ᴳ-· lpL lpM) =
    let ⟨ lpA , lpL′ ⟩ = compile-pres-prec ⊢L ⊢L′ lpc lpL in
    let ⟨ lpB , lpM′ ⟩ = compile-pres-prec ⊢M ⊢M′ lpc lpM in
    let ⟨ lpA₁ , lpA₂ ⟩ = ▹⇒-pres-prec m m′ lpA in
      ⟨ lpA₂ , ⊑ᶜ-· (⊑ᶜ-cast lpA (fun⊑ lpA₁ lpA₂) lpL′) (⊑ᶜ-cast lpB lpA₁ lpM′) ⟩
  compile-pres-prec (⊢if ⊢L ⊢M ⊢N _ aa) (⊢if ⊢L′ ⊢M′ ⊢N′ _ aa′) lpc (⊑ᴳ-if lpL lpM lpN) =
    let ⟨ lpB , lpL′ ⟩ = compile-pres-prec ⊢L ⊢L′ lpc lpL in
    let ⟨ lpA₁ , lpM′ ⟩ = compile-pres-prec ⊢M ⊢M′ lpc lpM in
    let ⟨ lpA₂ , lpN′ ⟩ = compile-pres-prec ⊢N ⊢N′ lpc lpN in
    let lp⨆aa = ⨆-pres-prec aa aa′ lpA₁ lpA₂ in
      ⟨ lp⨆aa , ⊑ᶜ-if (⊑ᶜ-cast lpB base⊑ lpL′) (⊑ᶜ-cast lpA₁ lp⨆aa lpM′) (⊑ᶜ-cast lpA₂ lp⨆aa lpN′) ⟩
  compile-pres-prec (⊢cons ⊢M ⊢N) (⊢cons ⊢M′ ⊢N′) lpc (⊑ᴳ-cons lpM lpN) =
    let ⟨ lpA , lpM′ ⟩ = compile-pres-prec ⊢M ⊢M′ lpc lpM in
    let ⟨ lpB , lpN′ ⟩ = compile-pres-prec ⊢N ⊢N′ lpc lpN in
      ⟨ pair⊑ lpA lpB , ⊑ᶜ-cons lpM′ lpN′ ⟩
  compile-pres-prec (⊢fst ⊢M m) (⊢fst ⊢M′ m′) lpc (⊑ᴳ-fst lpM) =
    let ⟨ lp , lpM′ ⟩ = compile-pres-prec ⊢M ⊢M′ lpc lpM in
    let ⟨ lp₁ , lp₂ ⟩ = ▹×-pres-prec m m′ lp in
      ⟨ lp₁ , ⊑ᶜ-fst (⊑ᶜ-cast lp (pair⊑ lp₁ lp₂) lpM′) ⟩
  compile-pres-prec (⊢snd ⊢M m) (⊢snd ⊢M′ m′) lpc (⊑ᴳ-snd lpM) =
    let ⟨ lp , lpM′ ⟩ = compile-pres-prec ⊢M ⊢M′ lpc lpM in
    let ⟨ lp₁ , lp₂ ⟩ = ▹×-pres-prec m m′ lp in
      ⟨ lp₂ , ⊑ᶜ-snd (⊑ᶜ-cast lp (pair⊑ lp₁ lp₂) lpM′) ⟩
  compile-pres-prec (⊢inl ⊢M) (⊢inl ⊢M′) lpc (⊑ᴳ-inl lpB lpM) =
    let ⟨ lpA , lpM′ ⟩ = compile-pres-prec ⊢M ⊢M′ lpc lpM in
      ⟨ sum⊑ lpA lpB , ⊑ᶜ-inl lpB lpM′ ⟩
  compile-pres-prec (⊢inr ⊢M) (⊢inr ⊢M′) lpc (⊑ᴳ-inr lpA lpM) =
    let ⟨ lpB , lpM′ ⟩ = compile-pres-prec ⊢M ⊢M′ lpc lpM in
      ⟨ sum⊑ lpA lpB , ⊑ᶜ-inr lpA lpM′ ⟩
  compile-pres-prec (⊢case ⊢L ⊢M ⊢N abc bc) (⊢case ⊢L′ ⊢M′ ⊢N′ abc′ bc′) lpc (⊑ᴳ-case lpL lp1 lp2 lpM lpN) =
    let ⟨ lpA , lpL′ ⟩ = compile-pres-prec ⊢L ⊢L′ lpc lpL in
    let ⟨ lpB , lpM′ ⟩ = compile-pres-prec ⊢M ⊢M′ (⊑*-, lp1 lpc) lpM in
    let ⟨ lpC , lpN′ ⟩ = compile-pres-prec ⊢N ⊢N′ (⊑*-, lp2 lpc) lpN in
    let lp⨆bc = ⨆-pres-prec bc bc′ lpB lpC in
      ⟨ lp⨆bc , ⊑ᶜ-case (⊑ᶜ-cast lpA (sum⊑ lp1 lp2) lpL′) lp1 lp2
                         (⊑ᶜ-cast lpB lp⨆bc lpM′) (⊑ᶜ-cast lpC lp⨆bc lpN′) ⟩

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
