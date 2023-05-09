{-# OPTIONS --rewriting #-}
module LogRel.CastBindDir where

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
open import LogRel.CastLogRelDir

{- formulation of ℰ-bind with explicit step-indexing, a la Max New -}


𝒱→ℰ-down-one-≺ : ∀{c}{F}{F′}{i}{M}{N}{M′}
   → M —→ N
   → (∀ j V V′ → j ≤ suc i → M —↠ V → M′ —↠ V′ → # (𝒱⟦ c ⟧ ≺ V V′) j
       → # (ℰ⟦ c ⟧ ≺ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
   → (∀ j V V′ → j ≤ i → N —↠ V → M′ —↠ V′ →  # (𝒱⟦ c ⟧ ≺ V V′) j
       → # (ℰ⟦ c ⟧ ≺ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
𝒱→ℰ-down-one-≺ {c}{F}{F′}{i}{M}{N}{M′} M→N 𝒱→ℰsi j V V′ j≤i M→V M′→V′ 𝒱j =
   𝒱→ℰsi j V V′ (≤-trans j≤i (n≤1+n i)) (M —→⟨ M→N ⟩ M→V) M′→V′ 𝒱j

𝒱→ℰ-down-one-≻ : ∀{c}{F}{F′}{i}{M}{M′}{N′}
   → M′ —→ N′
   → (∀ j V V′ → j ≤ suc i → M —↠ V → M′ —↠ V′ → # (𝒱⟦ c ⟧ ≻ V V′) j
       → # (ℰ⟦ c ⟧ ≻ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
   → (∀ j V V′ → j ≤ i → M —↠ V → N′ —↠ V′ →  # (𝒱⟦ c ⟧ ≻ V V′) j
       → # (ℰ⟦ c ⟧ ≻ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
𝒱→ℰ-down-one-≻ {c}{F}{F′}{i}{M}{N}{M′} M′→N′ 𝒱→ℰsi j V V′ j≤i M→V M′→V′ 𝒱j =
   𝒱→ℰsi j V V′ (≤-trans j≤i (n≤1+n i)) M→V (N —→⟨ M′→N′ ⟩ M′→V′) 𝒱j

ξ-blame₃ : ∀ {M}{M′ : Term}
   → (F : PEFrame)
   → M —↠ blame
   → M′ ≡ F ⦉ M ⦊
     -----------
   → M′ —↠ blame
ξ-blame₃ (` F) M→b refl = (ξ* F M→b) ++ unit (ξ-blame F)
ξ-blame₃ □ M→b refl = M→b

ξ′* : ∀{M N} → (F : PEFrame) → M —↠ N → F ⦉ M ⦊ —↠ F ⦉ N ⦊
ξ′* {M} {N} (` F) M→N = ξ* F M→N
ξ′* {M} {N} □ M→N = M→N

ξ-preservation : ∀{Γ}{F}{M}{N}{A}
  → Γ ⊢ F ⦉ M ⦊ ⦂ A
  → M —→ N
  → Γ ⊢ F ⦉ N ⦊ ⦂ A
ξ-preservation {Γ} {` (□· M₁)} {M} {N} {A} (⊢· ⊢L ⊢M) M→N =
   ⊢· (preservation ⊢L M→N) ⊢M
ξ-preservation {Γ} {` (v ·□)} {M} {N} {A} (⊢· ⊢L ⊢M) M→N =
   ⊢· ⊢L (preservation ⊢M M→N)
ξ-preservation {Γ} {` □⟨ G !⟩} {M} {N} {.★} (⊢⟨!⟩ ⊢M) M→N =
   ⊢⟨!⟩ (preservation ⊢M M→N)
ξ-preservation {Γ} {` □⟨ H ?⟩} {M} {N} {.(gnd⇒ty H)} (⊢⟨?⟩ ⊢M .H) M→N =
   ⊢⟨?⟩ (preservation ⊢M M→N) H
ξ-preservation {Γ} {□} {M} {N} {A} ⊢FM M→N =
   preservation ⊢FM M→N

ℰ-bind-step : ∀{c}{F}{F′}{M}{M′}{i}{dir}{A}
   → [] ⊢ F ⦉ M ⦊ ⦂ A
   → (∀ j V V′ → j ≤ i → M —↠ V → M′ —↠ V′ → #(𝒱⟦ c ⟧ dir V V′) j
         → #(ℰ⟦ c ⟧ dir (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)) j)
   → #(ℰ⟦ c ⟧ dir M M′) i
   → #(ℰ⟦ c ⟧ dir (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)) i
ℰ-bind-step {c} {F} {F′} {M} {M′} {zero} {dir} ⊢FM 𝒱→ℰj ℰMM′sz =
    tz (ℰ⟦ c ⟧ dir (F ⦉ M ⦊) (F′ ⦉ M′ ⦊))
    
ℰ-bind-step {c}{F}{F′}{M}{M′}{suc i}{≺} ⊢FM 𝒱→ℰj ℰMM′si
    with ⇔-to (ℰ-suc{c}{≺}) ℰMM′si
... | inj₁ (N , M→N , ▷ℰNM′) =
     let IH = ℰ-bind-step{c}{F}{F′}{N}{M′}{i}{≺} (ξ-preservation{F = F} ⊢FM M→N)
                   (𝒱→ℰ-down-one-≺{c}{F}{F′}{i}{M}{N}{M′} M→N 𝒱→ℰj) ▷ℰNM′ in
      ⇔-fro (ℰ-suc{c}{≺}) (inj₁ ((F ⦉ N ⦊) , ξ′ F refl refl M→N , IH))
... | inj₂ (inj₂ (m , inj₁ M′→blame)) = inj₂ (inj₁ (ξ-blame₃ F′ M′→blame refl))
ℰ-bind-step {c}{F}{F′}{M}{M′}{suc i}{≺} ⊢FM 𝒱→ℰj ℰMM′si
    | inj₂ (inj₂ (m , inj₂ (V′ , M′→V′ , v′ , 𝒱MV′))) =
      let ℰFMF′V′ = 𝒱→ℰj (suc i) M V′ ≤-refl (M END) M′→V′ 𝒱MV′ in
      anti-reduction-≺-R ℰFMF′V′ (ξ′* F′ M′→V′)
ℰ-bind-step {c}{F}{F′}{M}{M′}{suc i}{≺} ⊢FM 𝒱→ℰj ℰMM′si
    | inj₂ (inj₁ M′→blame) = inj₂ (inj₁ (ξ-blame₃ F′ M′→blame refl))

ℰ-bind-step {c}{F}{F′}{M}{M′}{suc i}{≻} ⊢FM 𝒱→ℰj ℰMM′si
    with ⇔-to (ℰ-suc{c}{≻}) ℰMM′si
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      let ℰFMFN′ : # (ℰ⟦ c ⟧ ≻ (F ⦉ M ⦊) (F′ ⦉ N′ ⦊)) i
          ℰFMFN′ = ℰ-bind-step{c}{F}{F′}{M}{N′}{i}{≻} ⊢FM
             (𝒱→ℰ-down-one-≻{F = F}{F′} M′→N′ 𝒱→ℰj) ▷ℰMN′ in
      inj₁ ((F′ ⦉ N′ ⦊) , (ξ′ F′ refl refl M′→N′) , ℰFMFN′)
... | inj₂ (inj₁ isBlame) = inj₁ (blame , {!ξ′-blame F′!} , {!!})
... | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱VM′)) = {!!}
