open import Types
open import Variables
open import Labels
open import Data.Nat using (ℕ; zero; suc)

module GTLC2CCOrig
  (Cast : Type → Set)
  (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
  where

  open import GTLC
  open import ParamCastCalculusOrig Cast
  
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
     using (_≡_; refl; trans; sym; cong; cong-app)


  compile-var : ∀{Γ A}{x} → Γ ∋ x ⦂ A → Γ ∋ A
  compile-var Z = Z
  compile-var (S ∋x) = let IH = compile-var ∋x in S IH

  compile : ∀ {Γ A} (M : Term) → (d : Γ ⊢G M ⦂ A) → (Γ ⊢ A)
  compile (` x) (⊢var ∋x) = ` (compile-var ∋x)
  compile (ƛ A ˙ N) (⊢lam d) = ƛ (compile N d)
  compile (L · M at ℓ) (⊢app {A = A}{A₁}{A₂}{B} d₁ d₂ mA A1~B) =
     let L' = (compile L d₁) ⟨ cast A (A₁ ⇒ A₂) ℓ {consis (▹⇒⊑ mA) Refl⊑} ⟩ in
     let M' = (compile M d₂) ⟨ cast B A₁ ℓ {Sym~ A1~B} ⟩ in
     L' · M'
  compile ($ k # p) ⊢lit = $_ k {p}
  compile (if L then M else N at ℓ) (⊢if {A = A}{A'}{B} d₁ d₂ d₃ B~Bool A~A') =
     let L' = (compile L d₁) ⟨ cast B (` 𝔹) ℓ {B~Bool} ⟩ in
     let M' = (compile M d₂) ⟨ cast A (⨆ A~A') ℓ {~⨆ A~A'} ⟩ in
     let N' = (compile N d₃) ⟨ cast A' (⨆ A~A') ℓ {⨆~ A~A'} ⟩ in
     if L' M' N'
  compile (⟦ M , N ⟧) (⊢cons d₁ d₂) = cons (compile M d₁) (compile N d₂)
  compile (fst M at ℓ) (⊢fst {A = A}{A₁}{A₂} d mA) =
      let c = cast A (A₁ `× A₂) ℓ {consis (▹×⊑ mA) Refl⊑}  in
      let M' = (compile M d) ⟨ c ⟩ in
      fst M'
  compile (snd M at ℓ) (⊢snd {A = A}{A₁}{A₂} d mA) =
      let c = cast A (A₁ `× A₂) ℓ {consis (▹×⊑ mA) Refl⊑}  in
      let M' = (compile M d) ⟨ c ⟩ in
      snd M'
  compile (inl M other B) (⊢inl d) = inl (compile M d)
  compile (inr M other A) (⊢inr d) = inr (compile M d)
  compile (case L of B₁ ⇒ M ∣ C₁ ⇒ N at ℓ)
          (⊢case {A = A}{B₁}{B₂}{C₁}{C₂} d₁ d₂ d₃ A~B1C1 B2~C2) =
      let L' = (compile L d₁) ⟨ cast A (B₁ `⊎ C₁) ℓ {A~B1C1} ⟩ in
      let M' = (compile M d₂) ⟨ cast B₂ (⨆ B2~C2) ℓ {~⨆ B2~C2} ⟩ in
      let N' = (compile N d₃) ⟨ cast C₂ (⨆ B2~C2) ℓ {⨆~ B2~C2} ⟩ in
      case L' (ƛ M') (ƛ N')
