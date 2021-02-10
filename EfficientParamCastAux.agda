open import Types
open import PreCastStructure
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)

{-

  This module provides an alternative reduction relation for the
  Parameterized Cast Calculus that ensures space efficiency.  It
  accomplishes this by merging adjacent casts using a compose
  operation that must be provided by the client of the module.

-}

module EfficientParamCastAux (pcs : PreCastStruct) where

  open PreCastStruct pcs

  import ParamCastCalculus
  open ParamCastCalculus Cast

  {-

   The notion of Value changes to only allow a single cast in a value.
   So a value is a simple value (no cast) with an optional cast around it.

  -}

  data Value : ∀ {Γ A} → Γ ⊢ A → Set
  
  data SimpleValue : ∀ {Γ A} → Γ ⊢ A → Set where

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        -----------------
      → SimpleValue (ƛ N)

    V-const : ∀ {Γ} {A : Type} {k : rep A} {f : Prim A}
        ------------------------------
      → SimpleValue {Γ} {A} (($ k){f})

    V-pair : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        ----------------------
      → SimpleValue (cons V W)

    V-inl : ∀ {Γ A B} {V : Γ ⊢ A}
      → Value V
        --------------------------------
      → SimpleValue {Γ} {A `⊎ B} (inl V)

    V-inr : ∀ {Γ A B} {V : Γ ⊢ B}
      → Value V
        --------------------------------
      → SimpleValue {Γ} {A `⊎ B} (inr V)


  data Value where
    S-val : ∀ {Γ A}{V : Γ ⊢ A}
      → SimpleValue V
        -------------
      → Value V

    V-cast : ∀ {Γ : Context} {A B : Type} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        {i : Inert c}
      → SimpleValue V
        ---------------
      → Value (V ⟨ c ⟩)

  simple⋆ : ∀ {Γ A} → (M : Γ ⊢ A) → (SimpleValue M) → A ≢ ⋆
  simple⋆ .(ƛ _) V-ƛ = λ ()
  simple⋆ ((ParamCastCalculus.$ k) {P-Base}) V-const = λ ()
  simple⋆ ((ParamCastCalculus.$ k) {P-Fun f}) V-const = λ ()
  simple⋆ .(cons _ _) (V-pair x x₁) = λ ()
  simple⋆ .(inl _) (V-inl x) = λ ()
  simple⋆ .(inr _) (V-inr x) = λ ()

  canonical⋆ : ∀ {Γ} → (M : Γ ⊢ ⋆) → (Value M)
             → Σ[ A ∈ Type ] Σ[ M' ∈ (Γ ⊢ A) ] Σ[ c ∈ (Cast (A ⇒ ⋆)) ]
                 Inert c × (M ≡ (M' ⟨ c ⟩)) × A ≢ ⋆
  canonical⋆ .($ _) (S-val (V-const {f = ()}))
  canonical⋆ (M ⟨ _ ⟩) (V-cast{A = A}{B = B}{V = V}{c = c}{i = i} v) =
    ⟨ A , ⟨ V , ⟨ c , ⟨ i , ⟨ refl , simple⋆ M v ⟩ ⟩ ⟩ ⟩ ⟩

  simple-base : ∀ {Γ ι} → (M : Γ ⊢ ` ι) → SimpleValue M 
     → Σ[ k ∈ rep-base ι ] Σ[ f ∈ Prim (` ι) ] M ≡ ($ k){f}
  simple-base (($ k){f}) V-const = ⟨ k , ⟨ f , refl ⟩ ⟩

  rename-value : ∀ {Γ Δ A} (M : Γ ⊢ A) (ρ : ∀{B} → Γ ∋ B → Δ ∋ B)
        → Value M → Value (rename ρ M)
  rename-simple : ∀ {Γ Δ A} (M : Γ ⊢ A) (ρ : ∀{B} → Γ ∋ B → Δ ∋ B)
        → SimpleValue M → SimpleValue (rename ρ M)
  rename-simple (ƛ N) ρ V-ƛ = V-ƛ
  rename-simple ($_ r {p}) ρ V-const = V-const
  rename-simple (cons M N) ρ (V-pair x x₁) =
     (V-pair (rename-value M ρ x) (rename-value N ρ x₁))
  rename-simple (inl M) ρ (V-inl x) = (V-inl (rename-value M ρ x))
  rename-simple (inr M) ρ (V-inr x) = (V-inr (rename-value M ρ x))
  
  rename-value M ρ (S-val sM) = S-val (rename-simple M ρ sM)
  rename-value (V ⟨ c ⟩) ρ (V-cast {i = i} sV) =
     V-cast {i = i} (rename-simple V ρ sV)

  subst-value : ∀ {Γ Δ A} (M : Γ ⊢ A) (σ : ∀{B} → Γ ∋ B → Δ ⊢ B)
        → Value M → Value (subst σ M)
        
  subst-simple : ∀ {Γ Δ A} (M : Γ ⊢ A) (σ : ∀{B} → Γ ∋ B → Δ ⊢ B)
        → SimpleValue M → SimpleValue (subst σ M)
  subst-simple (ƛ N) σ V-ƛ = V-ƛ
  subst-simple ($_ r {p}) σ V-const = V-const
  subst-simple (cons M N) σ (V-pair x x₁) =
     V-pair (subst-value M σ x) (subst-value N σ x₁)
  subst-simple (inl M) σ (V-inl x) = V-inl (subst-value M σ x)
  subst-simple (inr M) σ (V-inr x) = V-inr (subst-value M σ x)
  
  subst-value M σ (S-val x) = S-val (subst-simple M σ x)
  subst-value (M ⟨ c ⟩) σ (V-cast {i = i} x) =
     V-cast {i = i} (subst-simple M σ x)
