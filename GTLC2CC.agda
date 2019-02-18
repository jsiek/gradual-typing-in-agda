open import Types
open import Variables
open import Labels
open import Data.Nat using (ℕ; zero; suc)

module GTLC2CC
  (Cast : Type → Set)
  (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
  where

  open import GTLC
  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Maybe

  {- to do: change to dom/cod a la AGT -}
  match⇒ : (A : Type) → Maybe (Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ~ (A₁ ⇒ A₂))
  match⇒ ⋆ = just (⟨ ⋆ , (⟨ ⋆ , unk~L ⟩) ⟩)
  match⇒ Nat = nothing
  match⇒ 𝔹 = nothing
  match⇒ (A ⇒ A₁) = just (⟨ A , (⟨ A₁ , Refl~ ⟩) ⟩)
  match⇒ (A `× A₁) = nothing
  match⇒ (A `⊎ A₁) = nothing

  match× : (A : Type) → Maybe (Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ~ (A₁ `× A₂))
  match× ⋆ = just (⟨ ⋆ , (⟨ ⋆ , unk~L ⟩) ⟩)
  match× Nat = nothing
  match× 𝔹 = nothing
  match× (A ⇒ A₁) = nothing
  match× (A `× A₁) = just (⟨ A , (⟨ A₁ , Refl~ ⟩) ⟩)
  match× (A `⊎ A₁) = nothing

  match⊎ : (A : Type) → Maybe (Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ~ (A₁ `⊎ A₂))
  match⊎ ⋆ = just (⟨ ⋆ , (⟨ ⋆ , unk~L ⟩) ⟩)
  match⊎ Nat = nothing
  match⊎ 𝔹 = nothing
  match⊎ (A ⇒ A₁) = nothing
  match⊎ (A `× A₁) = nothing
  match⊎ (A `⊎ A₁) = just (⟨ A , (⟨ A₁ , Refl~ ⟩) ⟩)

  match𝔹 : (A : Type) → Maybe (A ~ 𝔹)
  match𝔹 ⋆ = just (consis unk⊑ bool⊑)
  match𝔹 Nat = nothing
  match𝔹 𝔹 = just (consis bool⊑ bool⊑)
  match𝔹 (A ⇒ A₁) = nothing
  match𝔹 (A `× A₁) = nothing
  match𝔹 (A `⊎ A₁) = nothing

  compile : {Γ : Context} → (M : Term) → Maybe (Σ[ A ∈ Type ] Γ ⊢ A)
  compile {Γ} (`_ x) with lookup Γ x
  ... | nothing = nothing
  ... | just (⟨ A , k ⟩) = just (⟨ A , ` k ⟩)
  compile {Γ} (ƛ A , M) with compile {Γ , A} M
  ... | nothing = nothing
  ... | just (⟨ B , M' ⟩) = just (⟨ (A ⇒ B) , (ƛ A , M') ⟩)
  compile {Γ} (M · N at ℓ) with compile {Γ} M | compile {Γ} N
  ... | nothing | _ = nothing
  ... | just _ | nothing = nothing
  ... | just (⟨ A , M' ⟩) | just (⟨ B , N' ⟩) with match⇒ A
  ...    | nothing = nothing
  ...    | just (⟨ A₁ , (⟨ A₂ , c ⟩) ⟩) with B `~ A₁ 
  ...       | inj₁ d = 
              let M'' = (M' ⟨ (cast A (A₁ ⇒ A₂) (pos ℓ) {c}) ⟩) in
              let N'' = (N' ⟨ (cast B A₁ (pos ℓ) {d}) ⟩) in
              just (⟨ A₂ , M'' · N'' ⟩)
  ...       | inj₂ d = nothing
  compile {Γ} ($_ {A} x) with prim A
  ... | inj₁ p = just (⟨ A , ($ x){p} ⟩)
  ... | inj₂ p = nothing  
  compile {Γ} (if L M N ℓ) with compile {Γ} L | compile {Γ} M | compile {Γ} N
  ... | nothing | _ | _ = nothing
  ... | just _ | nothing | _ = nothing
  ... | just _ | just _ | nothing = nothing
  ... | just (⟨ A , L' ⟩) | just (⟨ B , M' ⟩) | just (⟨ C , N' ⟩) with match𝔹 A
  ...    | nothing = nothing
  ...    | just c with B `~ C
  ...        | inj₂ _ = nothing
  ...        | inj₁ d with (B `⊔ C) {d}
  ...           | ⟨ D , LUB ⟩ =
                  let L'' = (L' ⟨ (cast A 𝔹 (pos ℓ) {c}) ⟩) in
                  let M'' = (M' ⟨ (cast B D (pos ℓ) {consis {D} (proj₁ (proj₁ LUB)) (proj₂ LUB (proj₁ LUB))}) ⟩) in
                  let N'' = (N' ⟨ (cast C D (pos ℓ) {consis {D} (proj₂ (proj₁ LUB)) (proj₂ LUB (proj₁ LUB))}) ⟩) in
                  just (⟨ D , if L'' M'' N'' ⟩)

  compile {Γ} (cons M N) with compile {Γ} M | compile {Γ} N
  ... | nothing | _       = nothing
  ... | just _  | nothing = nothing
  ... | just (⟨ A , M' ⟩) | just (⟨ B , N' ⟩) = just (⟨ (A `× B) , (cons M' N') ⟩)
  compile {Γ} (fst M ℓ) with compile {Γ} M
  ... | nothing = nothing
  ... | just (⟨ A , M' ⟩) with match× A
  ...     | nothing = nothing
  ...     | just (⟨ A₁ , (⟨ A₂ , c ⟩) ⟩) =
            let M'' = (M' ⟨ cast A (A₁ `× A₂) (pos ℓ) {c} ⟩) in
            just (⟨ A₁ , fst M'' ⟩)
  compile {Γ} (snd M ℓ) with compile {Γ} M
  ... | nothing = nothing
  ... | just (⟨ A , M' ⟩) with match× A
  ...     | nothing = nothing
  ...     | just (⟨ A₁ , (⟨ A₂ , c ⟩) ⟩) =
            let M'' = (M' ⟨ cast A (A₁ `× A₂) (pos ℓ) {c} ⟩) in
            just (⟨ A₂ , snd M'' ⟩)
  compile {Γ} (inl B M) with compile {Γ} M
  ... | nothing = nothing
  ... | just (⟨ A , M' ⟩) = just (⟨ A `⊎ B , inl M' ⟩)
  compile {Γ} (inr A M) with compile {Γ} M
  ... | nothing = nothing
  ... | just (⟨ B , M' ⟩) = just (⟨ A `⊎ B , inr M' ⟩)
  compile {Γ} (case L M N ℓ) with compile {Γ} L | compile {Γ} M | compile {Γ} N
  ... | nothing | _ | _ = nothing
  ... | just _ | nothing | _ = nothing
  ... | just _ | just _ | nothing = nothing
  ... | just (⟨ A , L' ⟩) | just (⟨ B , M₁ ⟩) | just (⟨ C , N₁ ⟩) with match⊎ A
  ...     | nothing = nothing
  ...     | just (⟨ A₁ , (⟨ A₂ , a ⟩) ⟩) with match⇒ B | match⇒ C
  ...        | nothing | _ = nothing
  ...        | just _ | nothing = nothing
  ...        | just (⟨ B₁ , (⟨ B₂ , b ⟩) ⟩) | just (⟨ C₁ , (⟨ C₂ , c ⟩) ⟩) with B₁ `~ A₁ | C₁ `~ A₂
  ...           | inj₂ _ | _ = nothing
  ...           | inj₁ _ | inj₂ _ = nothing
  ...           | inj₁ ba | inj₁ ca with B₂ `~ C₂
  ...              | inj₂ _ = nothing
  ...              | inj₁ bc with (B₂ `⊔ C₂) {bc}
  ...                | ⟨ D , LUB ⟩ =
                       let L'' = (L' ⟨ cast A (A₁ `⊎ A₂) (pos ℓ) {a} ⟩) in
                       let M₂ = (M₁ ⟨ cast B (B₁ ⇒ B₂) (pos ℓ) {b} ⟩) in
                       let N₂ = (N₁ ⟨ cast C (C₁ ⇒ C₂) (pos ℓ) {c} ⟩) in
                       let f1 = fun~ ba (consis (proj₁ (proj₁ LUB)) (proj₂ LUB (proj₁ LUB))) in
                       let M₃ = (M₂ ⟨ cast (B₁ ⇒ B₂) (A₁ ⇒ D) (pos ℓ) {f1} ⟩) in
                       let f2 =  fun~ ca (consis (proj₂ (proj₁ LUB)) (proj₂ LUB (proj₁ LUB))) in
                       let N₃ = (N₂ ⟨ cast (C₁ ⇒ C₂) (A₂ ⇒ D) (pos ℓ) {f2} ⟩) in
                       just (⟨ D , case L'' M₃ N₃ ⟩)

