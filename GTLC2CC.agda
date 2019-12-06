open import Types
open import Variables
open import Labels
open import Data.Nat using (ℕ; zero; suc)

module GTLC2CC
  (Cast : Type → Set)
  (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
  where

  open import GTLC
  open import ParamCastCalculus Cast
  
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
     using (_≡_; refl; trans; sym; cong; cong-app)

  compile : ∀ {Γ A} → (Γ ⊢G A) → (Γ ⊢ A)
  compile (` x) = ` x
  compile (ƛ A ˙ M) = ƛ (compile M)
  compile (_·_at_ {Γ}{A}{A₁}{A₂}{B} L M ℓ {m}{cn}) =
     let L' = (compile L) ⟨ cast A (A₁ ⇒ A₂) ℓ {consis (▹⇒⊑ m) Refl⊑} ⟩ in
     let M' = (compile M) ⟨ cast B A₁ ℓ {Sym~ cn} ⟩ in
     L' · M'
  compile ($_ k {p}) = ($ k) {p}
  compile (if {Γ}{A}{A'}{B} L M N ℓ {bb}{c}) =
     let L' = (compile L) ⟨ cast B (` 𝔹) ℓ {bb} ⟩ in
     let M' = (compile M) ⟨ cast A (⨆ c) ℓ {~⨆ c} ⟩ in
     let N' = (compile N) ⟨ cast A' (⨆ c) ℓ {⨆~ c} ⟩ in
     if L' M' N'
  compile (cons L M) =
     let L' = compile L in
     let M' = compile M in
     cons L' M'
  compile (fst {Γ}{A}{A₁}{A₂} M ℓ {m}) =
     let M' = (compile M) ⟨ cast A (A₁ `× A₂) ℓ {consis (▹×⊑ m) Refl⊑} ⟩ in
     fst M'
  compile (snd {Γ}{A}{A₁}{A₂} M ℓ {m}) =
     let M' = (compile M) ⟨ cast A (A₁ `× A₂) ℓ {consis (▹×⊑ m) Refl⊑} ⟩ in
     snd M'
  compile (inl B M) = inl (compile M)
  compile (inr A M) = inr (compile M)
  compile (case {Γ}{A}{A₁}{A₂}{B}{B₁}{B₂}{C}{C₁}{C₂} L M N ℓ
            {ma}{mb}{mc}{ab}{ac}{bc}) =
        let L' = (compile L) ⟨ cast A (A₁ `⊎ A₂) ℓ {consis (▹⊎⊑ ma) Refl⊑} ⟩
                  ⟨ cast (A₁ `⊎ A₂) (B₁ `⊎ C₁) ℓ {sum~ ab ac} ⟩ in
        let M' = (compile M) ⟨ cast B (B₁ ⇒ B₂) ℓ {consis (▹⇒⊑ mb) Refl⊑} ⟩
                  ⟨ cast (B₁ ⇒ B₂) (B₁ ⇒ ⨆ bc) ℓ {c1} ⟩ in
        let N' = (compile N) ⟨ cast C (C₁ ⇒ C₂) ℓ {consis (▹⇒⊑ mc) Refl⊑} ⟩
                  ⟨ cast (C₁ ⇒ C₂) (C₁ ⇒ ⨆ bc) ℓ {c2} ⟩ in
        case L' M' N'
        where
        c1 : (B₁ ⇒ B₂) ~ (B₁ ⇒ ⨆ bc)
        c1 = fun~ Refl~ (~⨆ bc)
        c2 : (C₁ ⇒ C₂) ~ (C₁ ⇒ ⨆ bc)
        c2 = fun~ Refl~ (⨆~ bc)


{-
  open import GTLC-materialize

  compile-mat : ∀ {Γ M A} → (Γ ⊢m M ⦂ A) → Σ[ A' ∈ Type ] Γ ⊢ A' × A' ⊑ A
  compile-mat d
      with mat-impl-trad d
  ... | ⟨ A' , ⟨ d' , lt ⟩ ⟩ =
        ⟨ A' , ⟨ (compile d') , lt ⟩ ⟩

-}
