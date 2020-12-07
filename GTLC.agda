
module GTLC where

open import Types public
open import Variables public
open import Labels public
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe
open import Data.Unit
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)


{-

The following is the traditional version of the type system
for the GTLC.

-}

infix  4  _⊢G_
data _⊢G_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
      ---------------------------
    → Γ ⊢G A

  ƛ_˙_ : ∀ {Γ B}
    → (A : Type)
    → Γ , A ⊢G B
      -------------------
    → Γ ⊢G A ⇒ B

  _·_at_ : ∀ {Γ A A₁ A₂ B}
    → Γ ⊢G A
    → Γ ⊢G B
    → Label
    → {m : A ▹ A₁ ⇒ A₂}
    → {cn : A₁ ~ B}
      -------------------------
    → Γ ⊢G A₂

  $_ : ∀ {Γ A}
    → rep A
    → {p : Prim A}
      ------------------
    → Γ ⊢G A

  if : ∀ {Γ}{A A' B : Type}
    → Γ ⊢G B
    → Γ ⊢G A
    → Γ ⊢G A'
    → Label
    → {bb : B ~ ` 𝔹}
    → {aa : A ~ A'}
      --------------------------------------
    → Γ ⊢G ⨆ aa

  cons : ∀ {Γ A B}
    → Γ ⊢G A  →  Γ ⊢G B
      -----------------------
    → Γ ⊢G A `× B
    
  fst : ∀ {Γ A A₁ A₂}
    → Γ ⊢G A
    → Label
    → { m : A ▹ A₁ × A₂ }
      -------------------------
    → Γ ⊢G A₁

  snd : ∀ {Γ A A₁ A₂}
    → Γ ⊢G A
    → Label
    → { m : A ▹ A₁ × A₂ }
      -------------------------
    → Γ ⊢G A₂

  inl : ∀ {Γ A}
    → (B : Type)
    → Γ ⊢G A
      -----------------------
    → Γ ⊢G A `⊎ B

  inr : ∀ {Γ B}
    → (A : Type)
    → Γ ⊢G B
      -----------------------
    → Γ ⊢G A `⊎ B

  case : ∀{Γ A A₁ A₂ B₁ B₂ C₁ C₂}
    → Γ ⊢G A
    → Γ , B₁ ⊢G B₂
    → Γ , C₁ ⊢G C₂
    → Label
    → {ma : A ▹ A₁ ⊎ A₂ }
    → {ab : A₁ ~ B₁}
    → {ac : A₂ ~ C₁}
    → {bc : B₂ ~ C₂}
      ----------------------------------
    → Γ ⊢G ⨆ bc

{- Examples -}



