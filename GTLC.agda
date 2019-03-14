
module GTLC where

open import Types
open import Variables
open import Labels
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)

data Term : Set where
  `_ :  ℕ → Term
  ƛ_,_ : Type → Term → Term
  _·_at_  :  Term → Term → Label → Term
  $_ :  ∀ {A} → rep A → Term
  if : Term → Term → Term → Label → Term
  cons : Term → Term → Term
  fst : Term → Label → Term
  snd : Term → Label → Term
  inl : Type → Term → Term
  inr : Type → Term → Term
  case : Term → Term → Term → Label → Term

lookup : (Γ : Context) → ℕ → Maybe (Σ[ A ∈ Type ] Γ ∋ A)
lookup ∅ n = nothing
lookup (Γ , A) zero = just ⟨ A , Z ⟩
lookup (Γ , A) (suc n) with lookup Γ n
... | nothing = nothing
... | just ⟨ B , k ⟩ = just ⟨ B , S k ⟩


data _▹_⇒_ : Type → Type → Type → Set where
  match⇒⇒ : ∀{A B} → (A ⇒ B) ▹ A ⇒ B
  match⇒⋆ : ⋆ ▹ ⋆ ⇒ ⋆

▹⇒⊑ : ∀{C A B} → C ▹ A ⇒ B → C ⊑ A ⇒ B
▹⇒⊑ match⇒⇒ = fun⊑ Refl⊑ Refl⊑
▹⇒⊑ match⇒⋆ = unk⊑

data _▹_×_ : Type → Type → Type → Set where
  match×× : ∀{A B} → (A `× B) ▹ A × B
  match×⋆ : ⋆ ▹ ⋆ × ⋆

▹×⊑ : ∀{C A B} → C ▹ A × B → C ⊑ A `× B
▹×⊑ match×× = pair⊑ Refl⊑ Refl⊑
▹×⊑ match×⋆ = unk⊑

data _▹_⊎_ : Type → Type → Type → Set where
  match⊎⊎ : ∀{A B} → (A `⊎ B) ▹ A ⊎ B
  match⊎⋆ : ⋆ ▹ ⋆ ⊎ ⋆

▹⊎⊑ : ∀{C A B} → C ▹ A ⊎ B → C ⊑ A `⊎ B
▹⊎⊑ match⊎⊎ = sum⊑ Refl⊑ Refl⊑
▹⊎⊑ match⊎⋆ = unk⊑

{-

The following is the traditional version of the type system
for the GTLC.

-}

infix  4  _⊢_⦂_
data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢` : ∀ {Γ A k x}
    → lookup Γ x ≡ just ⟨ A , k ⟩
      ---------------------------
    → Γ ⊢ ` x ⦂ A

  ⊢ƛ : ∀ {Γ N A B}
    → Γ , A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ A , N ⦂ A ⇒ B

  ⊢app : ∀ {Γ L M A A₁ A₂ B ℓ}
    → Γ ⊢ L ⦂ A  →  A ▹ A₁ ⇒ A₂
    → Γ ⊢ M ⦂ B  →  A₁ ~ B
      -------------------------
    → Γ ⊢ L · M at ℓ ⦂ A₂

  ⊢const : ∀ {Γ A} {k : rep A} {p : Prim A}
      -----------
    → Γ ⊢ $ k ⦂ A

  ⊢if : ∀ {Γ L M N ℓ}{A A' B : Type}
    → Γ ⊢ L ⦂ B  →   Γ ⊢ M ⦂ A  →  Γ ⊢ N ⦂ A'  →  B ~ 𝔹  →  (c : A ~ A')
      --------------------------------------
    → Γ ⊢ if L M N ℓ ⦂ (A ⊔ A') {c}

  ⊢cons : ∀ {Γ A B M N}
    → Γ ⊢ M ⦂ A  →  Γ ⊢ N ⦂ B
      -----------------------
    → Γ ⊢ cons M N ⦂ A `× B
    
  ⊢fst : ∀ {Γ A A₁ A₂ M ℓ}
    → Γ ⊢ M ⦂ A  →  A ▹ A₁ × A₂
      -------------------------
    → Γ ⊢ fst M ℓ ⦂ A₁

  ⊢snd : ∀ {Γ A A₁ A₂ M ℓ}
    → Γ ⊢ M ⦂ A  →  A ▹ A₁ × A₂
      -------------------------
    → Γ ⊢ snd M ℓ ⦂ A₂

  ⊢inl : ∀ {Γ A B M}
    → Γ ⊢ M ⦂ A
      -----------------------
    → Γ ⊢ inl B M ⦂ A `⊎ B

  ⊢inr : ∀ {Γ A B M}
    → Γ ⊢ M ⦂ B
      -----------------------
    → Γ ⊢ inr A M ⦂ A `⊎ B

  ⊢case : ∀{Γ A A₁ A₂ B B₁ B₂ C C₁ C₂ L M N ℓ}
    → Γ ⊢ L ⦂ A  →  A ▹ A₁ ⊎ A₂
    → Γ ⊢ M ⦂ B  →  B ▹ B₁ ⇒ B₂
    → Γ ⊢ N ⦂ C  →  C ▹ C₁ ⇒ C₂
    → A₁ ~ B₁ → A₂ ~ C₁ → (bc : B₂ ~ C₂)
      ----------------------------------
    → Γ ⊢ case L M N ℓ ⦂ (B₂ ⊔ C₂) {bc}

