
module GTLC where

open import Types
open import Variables
open import Data.Nat
open import Data.Maybe
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong-app)

data Term : Set where
  `_ :  ℕ → Term
  ƛ_,_ : Type → Term → Term
  _·_at_  :  Term → Term → ℕ → Term
  $_ :  ∀ {A} → rep A → Term
  if : Term → Term → Term → ℕ → Term
  cons : Term → Term → Term
  fst : Term → ℕ → Term
  snd : Term → ℕ → Term
  inl : Type → Term → Term
  inr : Type → Term → Term
  case : Term → Term → Term → ℕ → Term

infix  4  _⊢_⦂_

lookup : (Γ : Context) → ℕ → Maybe (Σ[ A ∈ Type ] Γ ∋ A)
lookup ∅ n = nothing
lookup (Γ , A) zero = just ⟨ A , Z ⟩
lookup (Γ , A) (suc n) with lookup Γ n
... | nothing = nothing
... | just ⟨ B , k ⟩ = just ⟨ B , S k ⟩

data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢mat : ∀ {Γ M A B }
    → Γ ⊢ M ⦂ A  →  A ⊑ B
      -------------------
    → Γ ⊢ M ⦂ B

  ⊢` : ∀ {Γ A k x}
    → lookup Γ x ≡ just ⟨ A , k ⟩
      ---------------------------
    → Γ ⊢ ` x ⦂ A

  ⊢ƛ : ∀ {Γ N A B}
    → Γ , A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ A , N ⦂ A ⇒ B

  _·_ : ∀ {Γ L M A B ℓ}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M at ℓ ⦂ B

  ⊢const : ∀ {Γ A} {k : rep A} {p : Prim A}
      -----------
    → Γ ⊢ $ k ⦂ A

  ⊢if : ∀ {Γ L M N A ℓ}
    → Γ ⊢ L ⦂ 𝔹
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ if L M N ℓ ⦂ A

  ⊢cons : ∀ {Γ A B M N}
    → Γ ⊢ M ⦂ A  →  Γ ⊢ N ⦂ B
      -----------------------
    → Γ ⊢ cons M N ⦂ A `× B
    
  ⊢fst : ∀ {Γ A B M ℓ}
    → Γ ⊢ M ⦂ A `× B
      -----------------------
    → Γ ⊢ fst M ℓ ⦂ A

  ⊢snd : ∀ {Γ A B M ℓ}
    → Γ ⊢ M ⦂ A `× B
      -----------------------
    → Γ ⊢ snd M ℓ ⦂ B

  ⊢inl : ∀ {Γ A B M}
    → Γ ⊢ M ⦂ A
      -----------------------
    → Γ ⊢ inl B M ⦂ A `⊎ B

  ⊢inr : ∀ {Γ A B M}
    → Γ ⊢ M ⦂ B
      -----------------------
    → Γ ⊢ inr A M ⦂ A `⊎ B

  ⊢case : ∀{Γ A B C L M N ℓ}
    → Γ ⊢ L ⦂ A `⊎ B
    → Γ ⊢ M ⦂ A ⇒ C  →  Γ ⊢ N ⦂ B ⇒ C
      -------------------------------
    → Γ ⊢ case L M N ℓ ⦂ C
  
