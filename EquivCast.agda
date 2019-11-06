open import Types
open import CastStructure

open import Data.Nat
open import Data.Product
   using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)

module EquivCast
  (CastCalc₁ : CastStruct)
  (CastCalc₂ : CastStruct)
  where

  module CC₁ = CastCalc CastCalc₁
  module CC₂ = CastCalc CastCalc₂
  open CastStruct CastCalc₁ using () renaming (Cast to Cast₁)
  open CastStruct CastCalc₂ using () renaming (Cast to Cast₂)
  open CC₁ using (`_; _·_; $_) renaming (
       _⊢_ to _⊢₁_; ƛ_ to ƛ₁_; _⟨_⟩ to _⟨_⟩₁;
       if to if₁; cons to cons₁; fst to fst₁; snd to snd₁;
       inl to inl₁; inr to inr₁; case to case₁; blame to blame₁; _[_] to _[_]₁;
       _—→_ to _—→₁_)
  open CC₂ using ()
     renaming (
       _⊢_ to _⊢₂_; `_ to ``_; ƛ_ to ƛ₂_; _·_ to _●_; $_ to #_;
       if to if₂; cons to cons₂; fst to fst₂; snd to snd₂; _[_] to _[_]₂;
       inl to inl₂; inr to inr₂; case to case₂; _⟨_⟩ to _⟨_⟩₂;
       blame to blame₂;
       _—→_ to _—→₂_)

  module Equiv 
    (EqCast : ∀{A B} → Cast₁ (A ⇒ B) → Cast₂ (A ⇒ B) → Set)
    (inert-equiv : ∀{A B : Type}{c₁ : Cast₁ (A ⇒ B)}{c₂ : Cast₂ (A ⇒ B)}
            → CastStruct.Inert CastCalc₁ c₁ → EqCast c₁ c₂ → CastStruct.Inert CastCalc₂ c₂)
    (active-equiv : ∀{A B : Type}{c₁ : Cast₁ (A ⇒ B)}{c₂ : Cast₂ (A ⇒ B)}
            → CastStruct.Active CastCalc₁ c₁ → EqCast c₁ c₂ → CastStruct.Active CastCalc₂ c₂)
    (dom-equiv : ∀{A B C D : Type}{c₁ : Cast₁ ((A ⇒ B) ⇒ (C ⇒ D))}{i₁ : CastStruct.Inert CastCalc₁ c₁}
                              {c₂ : Cast₂ ((A ⇒ B) ⇒ (C ⇒ D))}{i₂ : CastStruct.Inert CastCalc₂ c₂}
            → EqCast c₁ c₂ 
            → EqCast (CastStruct.dom CastCalc₁ c₁ i₁) (CastStruct.dom CastCalc₂ c₂ i₂))
    (cod-equiv : ∀{A B C D : Type}{c₁ : Cast₁ ((A ⇒ B) ⇒ (C ⇒ D))}{i₁ : CastStruct.Inert CastCalc₁ c₁}
                              {c₂ : Cast₂ ((A ⇒ B) ⇒ (C ⇒ D))}{i₂ : CastStruct.Inert CastCalc₂ c₂}
            → EqCast c₁ c₂ 
            → EqCast (CastStruct.cod CastCalc₁ c₁ i₁) (CastStruct.cod CastCalc₂ c₂ i₂))
    where

    data _≈_ : ∀{Γ A} → Γ ⊢₁ A → Γ ⊢₂ A → Set where
      ≈-var : ∀ {Γ}{A}{x : Γ ∋ A} → (` x) ≈ (`` x)
      ≈-lam : ∀ {Γ}{A B}{M₁ : Γ , A ⊢₁ B}{M₂ : Γ , A ⊢₂ B}
            → M₁ ≈ M₂ → (ƛ₁ M₁) ≈ (ƛ₂ M₂)
      ≈-app : ∀ {Γ}{A B}{L₁ : Γ ⊢₁ A ⇒ B}{L₂ : Γ ⊢₂ A ⇒ B}
                {M₁ : Γ ⊢₁ A}{M₂ : Γ ⊢₂ A}
            → L₁ ≈ L₂ → M₁ ≈ M₂ → (L₁ · M₁) ≈ (L₂ ● M₂)
      ≈-lit : ∀ {Γ}{A}{k : rep A}{f : Prim A}
            → ($_ {Γ}{A} k {f}) ≈ (#_ {Γ}{A} k {f})
      ≈-if : ∀ {Γ}{A}
                {N₁ : Γ ⊢₁ ` 𝔹}{N₂ : Γ ⊢₂ ` 𝔹}
                {L₁ : Γ ⊢₁ A}{L₂ : Γ ⊢₂ A}
                {M₁ : Γ ⊢₁ A}{M₂ : Γ ⊢₂ A}
            → N₁ ≈ N₂ → L₁ ≈ L₂ → M₁ ≈ M₂
            → (if₁ N₁ L₁ M₁) ≈ (if₂ N₂ L₂ M₂)
      ≈-cons : ∀ {Γ}{A B}{L₁ : Γ ⊢₁ A}{L₂ : Γ ⊢₂ A}
                {M₁ : Γ ⊢₁ B}{M₂ : Γ ⊢₂ B}
            → L₁ ≈ L₂ → M₁ ≈ M₂ → (cons₁ L₁ M₁) ≈ (cons₂ L₂ M₂)
      ≈-fst : ∀ {Γ}{A B}{M₁ : Γ ⊢₁ A `× B}{M₂ : Γ ⊢₂ A `× B}
            → M₁ ≈ M₂ → (fst₁ M₁) ≈ (fst₂ M₂)
      ≈-snd : ∀ {Γ}{A B}{M₁ : Γ ⊢₁ A `× B}{M₂ : Γ ⊢₂ A `× B}
            → M₁ ≈ M₂ → (snd₁ M₁) ≈ (snd₂ M₂)
      ≈-inl : ∀ {Γ}{A B}{M₁ : Γ ⊢₁ A}{M₂ : Γ ⊢₂ A}
            → M₁ ≈ M₂ → (inl₁ {B = B} M₁) ≈ (inl₂ M₂)
      ≈-inr : ∀ {Γ}{A B}{M₁ : Γ ⊢₁ B}{M₂ : Γ ⊢₂ B}
            → M₁ ≈ M₂ → (inr₁ {A = A} M₁) ≈ (inr₂ M₂)
      ≈-case : ∀ {Γ}{A B C}
                {N₁ : Γ ⊢₁ A `⊎ B}{N₂ : Γ ⊢₂ A `⊎ B}
                {L₁ : Γ ⊢₁ A ⇒ C}{L₂ : Γ ⊢₂ A ⇒ C}
                {M₁ : Γ ⊢₁ B ⇒ C}{M₂ : Γ ⊢₂ B ⇒ C}
            → N₁ ≈ N₂ → L₁ ≈ L₂ → M₁ ≈ M₂
            → (case₁ N₁ L₁ M₁) ≈ (case₂ N₂ L₂ M₂)
      ≈-cast : ∀ {Γ}{A B}{M₁ : Γ ⊢₁ A}{M₂ : Γ ⊢₂ A}
                 {c₁ : Cast₁ (A ⇒ B)}{c₂ : Cast₂ (A ⇒ B)}
            → M₁ ≈ M₂ → EqCast c₁ c₂
            → (_⟨_⟩₁ M₁ c₁) ≈ (_⟨_⟩₂ M₂ c₂)
      ≈-blame : ∀ {Γ}{A}{ℓ} → (blame₁{Γ}{A} ℓ) ≈ (blame₂{Γ}{A} ℓ)


    value-equiv : ∀{A : Type}{M₁ : ∅ ⊢₁ A}{M₂ : ∅ ⊢₂ A}
      → M₁ ≈ M₂ → CC₁.Value M₁
      → CC₂.Value M₂
    value-equiv (≈-lam M₁≈M₂) CC₁.V-ƛ = CC₂.V-ƛ
    value-equiv ≈-lit CC₁.V-const = CC₂.V-const
    value-equiv (≈-cons M₁≈M₂ M₁≈M₃) (CC₁.V-pair VM₁ VM₂) =
       CC₂.V-pair (value-equiv M₁≈M₂ VM₁) (value-equiv M₁≈M₃ VM₂)
    value-equiv (≈-inl M₁≈M₂) (CC₁.V-inl VM₁) = CC₂.V-inl (value-equiv M₁≈M₂ VM₁)
    value-equiv (≈-inr M₁≈M₂) (CC₁.V-inr VM₁) = CC₂.V-inr (value-equiv M₁≈M₂ VM₁)
    value-equiv (≈-cast M₁≈M₂ ec) (CC₁.V-cast {i = i} VM₁) =
       CC₂.V-cast {i = inert-equiv i ec} (value-equiv M₁≈M₂ VM₁)

    plug-equiv-inv : ∀{A B : Type}{M₁ : ∅ ⊢₁ A}{F₁ : CC₁.Frame {∅} A B}{N₂ : ∅ ⊢₂ B}
       → CC₁.plug M₁ F₁ ≈ N₂
       → Σ[ F₂ ∈ CC₂.Frame {∅} A B ] Σ[ M₂ ∈ ∅ ⊢₂ A ]
          (N₂ ≡ CC₂.plug M₂ F₂) × (M₁ ≈ M₂)
    plug-equiv-inv {F₁ = CC₁.F-·₁ L₁} (≈-app {∅}{A}{B}{M₁}{M₂}{L₁}{L₂} F₁[M₁]≈N₂ F₁[M₁]≈N₃) =
       ⟨ (CC₂.F-·₁ L₂) , ⟨ M₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-·₂ M {v}} (≈-app {∅}{A}{B}{M₁}{M₂}{L₁}{L₂} F₁[M₁]≈N₂ F₁[M₁]≈N₃) =
       ⟨ CC₂.F-·₂ M₂ {value-equiv F₁[M₁]≈N₂ v} , ⟨ L₂ , ⟨ refl , F₁[M₁]≈N₃ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-if x x₁} (≈-if{N₂ = N₂}{L₂ = L₂}{M₂ = M₂} F₁[M₁]≈N₂ F₁[M₁]≈N₃ F₁[M₁]≈N₄) =
       ⟨ CC₂.F-if L₂ M₂ , ⟨ N₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-×₁ x} (≈-cons{L₂ = L₂}{M₂ = M₂} F₁[M₁]≈N₂ F₁[M₁]≈N₃) =
       ⟨ (CC₂.F-×₁ L₂) , ⟨ M₂ , ⟨ refl , F₁[M₁]≈N₃ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-×₂ x} (≈-cons{L₂ = L₂}{M₂ = M₂} F₁[M₁]≈N₂ F₁[M₁]≈N₃) =
       ⟨ (CC₂.F-×₂ M₂) , ⟨ L₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-fst} (≈-fst{M₂ = M₂} F₁[M₁]≈N₂) =
       ⟨ CC₂.F-fst , ⟨ M₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-snd} (≈-snd{M₂ = M₂} F₁[M₁]≈N₂) =
       ⟨ CC₂.F-snd , ⟨ M₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-inl} (≈-inl{M₂ = M₂} F₁[M₁]≈N₂) =
       ⟨ CC₂.F-inl , ⟨ M₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-inr} (≈-inr{M₂ = M₂} F₁[M₁]≈N₂) =
       ⟨ CC₂.F-inr , ⟨ M₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-case x x₁} (≈-case{N₂ = N₂}{L₂ = L₂}{M₂ = M₂} F₁[M₁]≈N₂ F₁[M₁]≈N₃ F₁[M₁]≈N₄) =
       ⟨ CC₂.F-case L₂ M₂ , ⟨ N₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩
    plug-equiv-inv {F₁ = CC₁.F-cast x} (≈-cast{M₂ = M₂}{c₂ = c₂} F₁[M₁]≈N₂ x₁) =
       ⟨ (CC₂.F-cast c₂) , ⟨ M₂ , ⟨ refl , F₁[M₁]≈N₂ ⟩ ⟩ ⟩

    plug-equiv : ∀{A A₁ : Type}{F : CC₁.Frame A A₁}{F₂ : CC₂.Frame A A₁}{M M′ : ∅ ⊢₁ A}{M₂ N₂ : ∅ ⊢₂ A}
       → CC₁.plug M F ≈ CC₂.plug M₂ F₂
       → M′ ≈ N₂
       → CC₁.plug M′ F ≈ CC₂.plug N₂ F₂
    plug-equiv{A}{A₁}{F}{F₂} MF≈M₂F M′≈N₂ = {!!}

    subst-equiv : ∀{A B}{Γ}{M₁ : Γ , A ⊢₁ B}{M₂ : Γ , A ⊢₂ B}{N₁ : Γ ⊢₁ A}{N₂ : Γ ⊢₂ A}
       → M₁ ≈ M₂
       → N₁ ≈ N₂
       → (M₁ [ N₁ ]₁) ≈ (M₂ [ N₂ ]₂)
    subst-equiv M₁≈M₂ N₁≈N₂ = {!!}

    module AppCastEquiv
      (applyCast-equiv : ∀{A B : Type}{M₁ : ∅ ⊢₁ A}{M₂ : ∅ ⊢₂ A}{vM₁ : CC₁.Value M₁}{vM₂ : CC₂.Value M₂}
                          {c₁ : Cast₁ (A ⇒ B)}{a₁ : CastStruct.Active CastCalc₁ c₁}
                          {c₂ : Cast₂ (A ⇒ B)}{a₂ : CastStruct.Active CastCalc₂ c₂}
              → M₁ ≈ M₂
              → EqCast c₁ c₂
              → CastStruct.applyCast CastCalc₁ M₁ vM₁ c₁ {a₁} ≈ CastStruct.applyCast CastCalc₂ M₂ vM₂ c₂ {a₂})
      (fstCast-equiv : ∀{A B C : Type}{M₁ : ∅ ⊢₁ A}{M₂ : ∅ ⊢₂ A}
                        {c₁ : Cast₁ (A ⇒ (B `× C))}{i₁ : CastStruct.Inert CastCalc₁ c₁}
                        {c₂ : Cast₂ (A ⇒ (B `× C))}{i₂ : CastStruct.Inert CastCalc₂ c₂}
              → M₁ ≈ M₂
              → EqCast c₁ c₂
              → CastStruct.fstCast CastCalc₁ M₁ c₁ {i₁} ≈ CastStruct.fstCast CastCalc₂ M₂ c₂ {i₂})
      (sndCast-equiv : ∀{A B C : Type}{M₁ : ∅ ⊢₁ A}{M₂ : ∅ ⊢₂ A}
                        {c₁ : Cast₁ (A ⇒ (B `× C))}{i₁ : CastStruct.Inert CastCalc₁ c₁}
                        {c₂ : Cast₂ (A ⇒ (B `× C))}{i₂ : CastStruct.Inert CastCalc₂ c₂}
              → M₁ ≈ M₂
              → EqCast c₁ c₂
              → CastStruct.sndCast CastCalc₁ M₁ c₁ {i₁} ≈ CastStruct.sndCast CastCalc₂ M₂ c₂ {i₂})
      where
      
      simulate : ∀{A}{M₁ N₁ : ∅ ⊢₁ A}{M₂ : ∅ ⊢₂ A}
               → M₁ ≈ M₂
               → M₁ —→₁ N₁
               → Σ[ N₂ ∈ (∅ ⊢₂ A) ] ((M₂ —→₂ N₂) × (N₁ ≈ N₂))
      simulate M₁≈M₂ (CC₁.ξ M—→₁M′)
          with plug-equiv-inv M₁≈M₂
      ... | ⟨ F₂ , ⟨ M₂ , ⟨ eq , eqv ⟩ ⟩ ⟩ rewrite eq
          with simulate eqv M—→₁M′
      ... | ⟨ N₂ , ⟨ M₂—→₂N₂ , N₁≈N₂ ⟩ ⟩ =
          ⟨ CC₂.plug N₂ F₂ , ⟨ CC₂.ξ M₂—→₂N₂ , plug-equiv M₁≈M₂ N₁≈N₂ ⟩ ⟩
      simulate M₁≈M₂ (CC₁.ξ-blame {ℓ = ℓ})
          with plug-equiv-inv M₁≈M₂
      ... | ⟨ F₂ , ⟨ M₂ , ⟨ eq , ≈-blame ⟩ ⟩ ⟩ rewrite eq =
            ⟨ blame₂ ℓ , ⟨ CC₂.ξ-blame , ≈-blame ⟩ ⟩
      simulate {M₁ = (ƛ₁ N) · W} {M₂ = ((ƛ₂ L) ● V)} (≈-app (≈-lam b₁≈b₂) M₁≈M₃) (_—→₁_.β vW) =
         let vV = value-equiv M₁≈M₃ vW in
         ⟨ L [ V ]₂ , ⟨ _—→₂_.β vV , subst-equiv b₁≈b₂ M₁≈M₃ ⟩ ⟩
      simulate (≈-app (≈-lit{k = k}) (≈-lit{k = k₁})) _—→₁_.δ = ⟨ # k k₁ , ⟨ _—→₂_.δ , ≈-lit ⟩ ⟩
      simulate (≈-if{L₂ = L₂} (≈-lit{k = true}) M₁≈M₃ M₁≈M₄) CC₁.β-if-true = ⟨ L₂ , ⟨ CC₂.β-if-true , M₁≈M₃ ⟩ ⟩
      simulate (≈-if{M₂ = M₂} (≈-lit{k = false}) M₁≈M₃ M₁≈M₄) CC₁.β-if-false = ⟨ M₂ , ⟨ CC₂.β-if-false , M₁≈M₄ ⟩ ⟩
      simulate (≈-fst (≈-cons{L₂ = L₂} L₁≈L₂ M₁≈M₂)) (CC₁.β-fst vN₁ vW) =
         ⟨ L₂ , ⟨ CC₂.β-fst (value-equiv L₁≈L₂ vN₁) (value-equiv M₁≈M₂ vW) , L₁≈L₂ ⟩ ⟩
      simulate (≈-snd (≈-cons{M₂ = M₂} L₁≈L₂ M₁≈M₂)) (CC₁.β-snd vV vN₁) =
         ⟨ M₂ , ⟨ CC₂.β-snd (value-equiv L₁≈L₂ vV) (value-equiv M₁≈M₂ vN₁)  , M₁≈M₂ ⟩ ⟩    
      simulate (≈-case{L₂ = L₂} (≈-inl{M₂ = N₂} N₁≈N₂) L₁≈L₂ M₁≈M₂) (CC₁.β-caseL vN₁) =
          ⟨ (L₂ ● N₂) , ⟨ (CC₂.β-caseL (value-equiv N₁≈N₂ vN₁)) , (≈-app L₁≈L₂ N₁≈N₂ ) ⟩ ⟩
      simulate (≈-case{M₂ = M₂} (≈-inr{M₂ = N₂} N₁≈N₂) L₁≈L₂ M₁≈M₂) (CC₁.β-caseR vN₁) =
          ⟨ (M₂ ● N₂) , ⟨ (CC₂.β-caseR (value-equiv N₁≈N₂ vN₁)) , (≈-app M₁≈M₂ N₁≈N₂) ⟩ ⟩
      simulate (≈-cast{M₂ = M₂}{c₂ = c₂} M₁≈M₂ c₁≈c₂) (CC₁.cast vV {a}) =
          let vM₂ = value-equiv M₁≈M₂ vV in
          let a₂ = active-equiv a c₁≈c₂ in
          ⟨ CastStruct.applyCast CastCalc₂ M₂ vM₂ c₂ {a₂} , ⟨ (CC₂.cast vM₂ {a₂}) , applyCast-equiv M₁≈M₂ c₁≈c₂ ⟩ ⟩
      simulate (≈-app{M₂ = M₂} (≈-cast{M₂ = V₂}{c₂ = c₂} V₁≈V₂ c₁≈c₂) M₁≈M₂) (CC₁.fun-cast v x {i}) =
          let i₂ = inert-equiv i c₁≈c₂ in
          let R = (V₂ ● (M₂ ⟨ CastStruct.dom CastCalc₂ c₂ i₂ ⟩₂)) ⟨ CastStruct.cod CastCalc₂ c₂ i₂ ⟩₂ in
          ⟨ R , ⟨ (CC₂.fun-cast (value-equiv V₁≈V₂ v) (value-equiv M₁≈M₂ x ) {i₂}) ,
                  ≈-cast (≈-app V₁≈V₂ (≈-cast M₁≈M₂ (dom-equiv c₁≈c₂))) (cod-equiv c₁≈c₂) ⟩ ⟩
      simulate (≈-fst (≈-cast {M₂ = M₂}{c₂ = c₂} M₁≈M₂ c₁≈c₂)) (CC₁.fst-cast {c = c₁} vM₁ {i = i₁}) =
          ⟨ (CastStruct.fstCast CastCalc₂ M₂ c₂ {inert-equiv i₁ c₁≈c₂}) ,
          ⟨ (CC₂.fst-cast {c = c₂} (value-equiv M₁≈M₂ vM₁)) ,
            fstCast-equiv M₁≈M₂ c₁≈c₂ ⟩ ⟩
      simulate (≈-snd (≈-cast {M₂ = M₂}{c₂ = c₂} M₁≈M₂ c₁≈c₂)) (CC₁.snd-cast {c = c₁} vM₁ {i = i₁}) =
          ⟨ (CastStruct.sndCast CastCalc₂ M₂ c₂ {inert-equiv i₁ c₁≈c₂}) ,
          ⟨ (CC₂.snd-cast {c = c₂} (value-equiv M₁≈M₂ vM₁)) ,
            sndCast-equiv M₁≈M₂ c₁≈c₂ ⟩ ⟩
      simulate (≈-case{L₂ = L₂}{M₂ = M₂} (≈-cast {M₂ = N₂}{c₂ = c₂} N₁≈N₂ c₁≈c₂) L₁≈L₂ M₁≈M₂) (CC₁.case-cast vN₁ {i₁}) =
          ⟨ CastStruct.caseCast CastCalc₂ N₂ c₂ {inert-equiv i₁ c₁≈c₂} L₂ M₂ ,
          ⟨ (CC₂.case-cast (value-equiv N₁≈N₂ vN₁) {inert-equiv i₁ c₁≈c₂}) ,
            {!!} ⟩ ⟩
