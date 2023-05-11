{-# OPTIONS --rewriting #-}
module LogRel.CastBindDir2 where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import LogRel.Cast
open import LogRel.CastDeterministic
open import StepIndexedLogic
open import LogRel.CastSafe
open import LogRel.CastLogRelDir2

{- formulation of ℰ-bind with explicit step-indexing, a la Max New -}

𝒱→ℰ-down-one-≺ : ∀{c}{d}{F}{F′}{i}{M}{N}{M′}
   → M —→ N
   → (∀ j V V′ → j ≤ suc i → M —↠ V → Value V → M′ —↠ V′ → Value V′
       → # (𝒱⟦ d ⟧ ≺ V V′) j
       → # (ℰ⟦ c ⟧ ≺ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
   → (∀ j V V′ → j ≤ i → N —↠ V → Value V → M′ —↠ V′ → Value V′
       →  # (𝒱⟦ d ⟧ ≺ V V′) j
       → # (ℰ⟦ c ⟧ ≺ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
𝒱→ℰ-down-one-≺ {c}{d}{F}{F′}{i}{M}{N}{M′} M→N 𝒱→ℰsi
   j V V′ j≤i M→V v M′→V′ v′ 𝒱j =
   𝒱→ℰsi j V V′ (≤-trans j≤i (n≤1+n i)) (M —→⟨ M→N ⟩ M→V) v M′→V′ v′ 𝒱j

𝒱→ℰ-down-one-≻ : ∀{c}{d}{F}{F′}{i}{M}{M′}{N′}
   → M′ —→ N′
   → (∀ j V V′ → j ≤ suc i → M —↠ V → Value V → M′ —↠ V′ → Value V′
       → # (𝒱⟦ d ⟧ ≻ V V′) j
       → # (ℰ⟦ c ⟧ ≻ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
   → (∀ j V V′ → j ≤ i → M —↠ V → Value V → N′ —↠ V′ → Value V′
       →  # (𝒱⟦ d ⟧ ≻ V V′) j
       → # (ℰ⟦ c ⟧ ≻ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
𝒱→ℰ-down-one-≻ {c}{d}{F}{F′}{i}{M}{N}{M′} M′→N′ 𝒱→ℰsi
   j V V′ j≤i M→V v M′→V′ v′ 𝒱j =
   𝒱→ℰsi j V V′ (≤-trans j≤i (n≤1+n i)) M→V v (N —→⟨ M′→N′ ⟩ M′→V′) v′ 𝒱j

ℰ-bind-step : ∀{c}{d}{F}{F′}{M}{M′}{i}{dir}
   → #(ℰ⟦ d ⟧ dir M M′) i
   → (∀ j V V′ → j ≤ i → M —↠ V → Value V → M′ —↠ V′ → Value V′
         → #(𝒱⟦ d ⟧ dir V V′) j
         → #(ℰ⟦ c ⟧ dir (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
   → #(ℰ⟦ c ⟧ dir (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)) i
ℰ-bind-step {c}{d} {F} {F′} {M} {M′} {zero} {dir} ℰMM′sz 𝒱→ℰj =
    tz (ℰ⟦ c ⟧ dir (F ⦉ M ⦊) (F′ ⦉ M′ ⦊))
ℰ-bind-step {c}{d}{F}{F′}{M}{M′}{suc i}{≺} ℰMM′si 𝒱→ℰj
    with ⇔-to (ℰ-suc{d}{≺}) ℰMM′si
... | inj₁ (N , M→N , ▷ℰNM′) =
     let IH = ℰ-bind-step{c}{d}{F}{F′}{N}{M′}{i}{≺} ▷ℰNM′
                   (𝒱→ℰ-down-one-≺{c}{d}{F}{F′}{i}{M}{N}{M′} M→N 𝒱→ℰj) in
      ⇔-fro (ℰ-suc{c}{≺}) (inj₁ ((F ⦉ N ⦊) , ξ′ F refl refl M→N , IH))
... | inj₂ (inj₂ (m , inj₁ M′→blame)) = inj₂ (inj₁ (ξ-blame₃ F′ M′→blame refl))
ℰ-bind-step {c}{d}{F}{F′}{M}{M′}{suc i}{≺} ℰMM′si 𝒱→ℰj 
    | inj₂ (inj₂ (m , inj₂ (V′ , M′→V′ , v′ , 𝒱MV′))) =
      let ℰFMF′V′ = 𝒱→ℰj (suc i) M V′ ≤-refl (M END) m M′→V′ v′ 𝒱MV′ in
      anti-reduction-≺-R ℰFMF′V′ (ξ′* F′ M′→V′)
ℰ-bind-step {c}{d}{F}{F′}{M}{M′}{suc i}{≺} ℰMM′si 𝒱→ℰj 
    | inj₂ (inj₁ M′→blame) = inj₂ (inj₁ (ξ-blame₃ F′ M′→blame refl))
ℰ-bind-step {c}{d}{F}{F′}{M}{M′}{suc i}{≻} ℰMM′si 𝒱→ℰj 
    with ⇔-to (ℰ-suc{d}{≻}) ℰMM′si
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      let ℰFMFN′ : # (ℰ⟦ c ⟧ ≻ (F ⦉ M ⦊) (F′ ⦉ N′ ⦊)) i
          ℰFMFN′ = ℰ-bind-step{c}{d}{F}{F′}{M}{N′}{i}{≻} ▷ℰMN′ 
                     (𝒱→ℰ-down-one-≻{c}{d}{F}{F′} M′→N′ 𝒱→ℰj)  in
      inj₁ ((F′ ⦉ N′ ⦊) , (ξ′ F′ refl refl M′→N′) , ℰFMFN′)
... | inj₂ (inj₁ isBlame)
    with F′
... | □ = inj₂ (inj₁ isBlame)
... | ` F″ = inj₁ (blame , ξ-blame F″ , ℰ-blame-step{c}{≻})
ℰ-bind-step {c}{d}{F}{F′}{M}{M′}{suc i}{≻} ℰMM′si 𝒱→ℰj 
    | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱VM′)) =
    let xx = 𝒱→ℰj (suc i) V M′ ≤-refl M→V v (M′ END) m′ 𝒱VM′ in
    anti-reduction-≻-L xx (ξ′* F M→V)
