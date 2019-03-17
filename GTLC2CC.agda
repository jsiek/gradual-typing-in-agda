open import Types
open import Variables
open import Labels
open import Data.Nat using (ℕ; zero; suc)

module GTLC2CC
  (Cast : Type → Set)
  (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
  where

  open import GTLC
  open import GTLC-materialize
  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc
  
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
     using (_≡_; refl; trans; sym; cong; cong-app)

  compile : ∀ {Γ M A} → (Γ ⊢ M ⦂ A) → (Γ ⊢ A)
  compile (⊢` {k = k} lk) = ` k
  compile (⊢ƛ d) = ƛ (compile d)
  compile (⊢app{Γ}{L}{M}{A}{A₁}{A₂}{B}{ℓ} d₁ m d₂ c) =
     let d₁' = (compile d₁) ⟨ cast A (A₁ ⇒ A₂) ℓ {consis (▹⇒⊑ m) Refl⊑} ⟩ in
     let d₂' = (compile d₂) ⟨ cast B A₁ ℓ {Sym~ c} ⟩ in
     d₁' · d₂'
  compile (⊢const{k = k}{p = p}) = ($ k) {p}
  compile (⊢if{Γ}{L}{M}{N}{ℓ}{A}{A'}{B} d d₁ d₂ bb c)
      with (A `⊔ A') {c}
  ... | ⟨ A⊔A' , ⟨ ub , _ ⟩ ⟩ =
     let d' = (compile d) ⟨ cast B (` 𝔹) ℓ {bb} ⟩ in
     let d₁' = (compile d₁) ⟨ cast A A⊔A' ℓ {consis (proj₁ ub) Refl⊑} ⟩ in
     let d₂' = (compile d₂) ⟨ cast A' A⊔A' ℓ {consis (proj₂ ub) Refl⊑} ⟩ in
     if d' d₁' d₂'
  compile (⊢cons d₁ d₂) =
     let d₁' = compile d₁ in
     let d₂' = compile d₂ in
     cons d₁' d₂'
  compile (⊢fst{Γ}{A}{A₁}{A₂}{M}{ℓ} d m) =
     let d' = (compile d) ⟨ cast A (A₁ `× A₂) ℓ {consis (▹×⊑ m) Refl⊑} ⟩ in
     fst d'
  compile (⊢snd{Γ}{A}{A₁}{A₂}{M}{ℓ} d m) =
     let d' = (compile d) ⟨ cast A (A₁ `× A₂) ℓ {consis (▹×⊑ m) Refl⊑} ⟩ in
     snd d'
  compile (⊢inl d) = inl (compile d)
  compile (⊢inr d) = inr (compile d)
  compile (⊢case{Γ}{A}{A₁}{A₂}{B}{B₁}{B₂}{C}{C₁}{C₂}{L}{M}{N}{ℓ}
            da ma db mb dc mc ab ac bc)
      with (B₂ `⊔ C₂) {bc}
  ... | ⟨ B₂⊔C₂ , ⟨ ub , lb ⟩ ⟩ =
        let da' = (compile da) ⟨ cast A (A₁ `⊎ A₂) ℓ {consis (▹⊎⊑ ma) Refl⊑} ⟩
                  ⟨ cast (A₁ `⊎ A₂) (B₁ `⊎ C₁) ℓ {sum~ ab ac} ⟩ in
        let db' = (compile db) ⟨ cast B (B₁ ⇒ B₂) ℓ {consis (▹⇒⊑ mb) Refl⊑} ⟩
                  ⟨ cast (B₁ ⇒ B₂) (B₁ ⇒ B₂⊔C₂) ℓ {c1} ⟩ in
        let dc' = (compile dc) ⟨ cast C (C₁ ⇒ C₂) ℓ {consis (▹⇒⊑ mc) Refl⊑} ⟩
                  ⟨ cast (C₁ ⇒ C₂) (C₁ ⇒ B₂⊔C₂) ℓ {c2} ⟩ in
        case da' db' dc'
        where
        c1 : (B₁ ⇒ B₂) ~ (B₁ ⇒ B₂⊔C₂)
        c1 = fun~ Refl~ (consis (proj₁ ub) (lb ub))
        c2 : (C₁ ⇒ C₂) ~ (C₁ ⇒ B₂⊔C₂)
        c2 = fun~ Refl~ (consis (proj₂ ub) (lb ub))


  compile-mat : ∀ {Γ M A} → (Γ ⊢m M ⦂ A) → Σ[ A' ∈ Type ] Γ ⊢ A' × A' ⊑ A
  compile-mat d
      with mat-impl-trad d
  ... | ⟨ A' , ⟨ d' , lt ⟩ ⟩ =
        ⟨ A' , ⟨ (compile d') , lt ⟩ ⟩
