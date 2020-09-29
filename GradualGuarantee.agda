open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂; inspect; [_])
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)

-- We're using simple cast - at least for now.
open import SimpleCast using (Cast; Active; Cross; applyCast; pcs; cs; dom; cod; fstC; sndC; inlC; inrC)
open import Types
open import Variables
open import Labels

open import GTLC
import ParamCastCalculus
open ParamCastCalculus Cast
import ParamCastAux
open ParamCastAux pcs using (Value; Frame; plug; canonical⋆)
import ParamCastReduction
open ParamCastReduction cs

open Value

infix 6 _,_⊢_⊑ᴳ_

-- Term precision for GTLC.
data _,_⊢_⊑ᴳ_ : ∀ (Γ Γ′ : Context) → {A A′ : Type} → Γ ⊢G A → Γ′ ⊢G A′ → Set where

  ⊑ᴳ-prim : ∀ {Γ Γ′ A} {k : rep A} {i : Prim A}
      ------------------------------
    → Γ , Γ′ ⊢ $_ {Γ} k {i} ⊑ᴳ $_ {Γ′} k {i}

  ⊑ᴳ-var : ∀ {Γ Γ′ A A′} {x : Γ ∋ A} {x′ : Γ′ ∋ A′}
    → ∋→ℕ x ≡ ∋→ℕ x′
      -----------------
    → Γ , Γ′ ⊢ ` x ⊑ᴳ ` x′

  ⊑ᴳ-ƛ : ∀ {Γ Γ′ A A′ B B′} {N : Γ , A ⊢G B} {N′ : Γ′ , A′ ⊢G B′}
    → A ⊑ A′
    → (Γ , A) , (Γ′ , A′) ⊢ N ⊑ᴳ N′
      ------------------------------
    → Γ , Γ′ ⊢ ƛ A ˙ N ⊑ᴳ ƛ A′ ˙ N′

  ⊑ᴳ-· : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′ B B′} {L : Γ ⊢G A} {L′ : Γ′ ⊢G A′} {M : Γ ⊢G B} {M′ : Γ′ ⊢G B′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ L ⊑ᴳ L′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → {m : A ▹ A₁ ⇒ A₂} {cn : A₁ ~ B} {m′ : A′ ▹ A₁′ ⇒ A₂′} {cn′ : A₁′ ~ B′}
      --------------------------------------------------------------
    → Γ , Γ′ ⊢ (L · M at ℓ) {m} {cn} ⊑ᴳ (L′ · M′ at ℓ′) {m′} {cn′}

  ⊑ᴳ-if : ∀ {Γ Γ′ A₁ A₁′ A₂ A₂′ B B′} {L : Γ ⊢G B} {L′ : Γ′ ⊢G B′} {M : Γ ⊢G A₁} {M′ : Γ′ ⊢G A₁′} {N : Γ ⊢G A₂} {N′ : Γ′ ⊢G A₂′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ L ⊑ᴳ L′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → Γ , Γ′ ⊢ N ⊑ᴳ N′
    → {bb : B ~ ` 𝔹} {bb′ : B′ ~ ` 𝔹} {aa : A₁ ~ A₂} {aa′ : A₁′ ~ A₂′}
      ------------------------------------------------------------------
    → Γ , Γ′ ⊢ if L M N ℓ {bb} {aa} ⊑ᴳ if L′ M′ N′ ℓ′ {bb′} {aa′}

  ⊑ᴳ-cons : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢G A} {M′ : Γ′ ⊢G A′} {N : Γ ⊢G B} {N′ : Γ′ ⊢G B′}
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → Γ , Γ′ ⊢ N ⊑ᴳ N′
      --------------------------------
    → Γ , Γ′ ⊢ cons M N ⊑ᴳ cons M′ N′

  ⊑ᴳ-fst : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′} {M : Γ ⊢G A} {M′ : Γ′ ⊢G A′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → {m : A ▹ A₁ × A₂} {m′ : A′ ▹ A₁′ × A₂′}
      ------------------------------------------
    → Γ , Γ′ ⊢ fst M ℓ {m} ⊑ᴳ fst M′ ℓ′ {m′}

  ⊑ᴳ-snd : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′} {M : Γ ⊢G A} {M′ : Γ′ ⊢G A′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → {m : A ▹ A₁ × A₂} {m′ : A′ ▹ A₁′ × A₂′}
      ------------------------------------------
    → Γ , Γ′ ⊢ snd M ℓ {m} ⊑ᴳ snd M′ ℓ′ {m′}

  ⊑ᴳ-inl : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢G A} {M′ : Γ′ ⊢G A′}
    → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
      ------------------------------
    → Γ , Γ′ ⊢ inl B M ⊑ᴳ inl B′ M′

  ⊑ᴳ-inr : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢G B} {M′ : Γ′ ⊢G B′}
    → A ⊑ A′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
      ------------------------------
    → Γ , Γ′ ⊢ inr A M ⊑ᴳ inl A′ M′

  ⊑ᴳ-case : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′ B B′ B₁ B₁′ B₂ B₂′ C C′ C₁ C₁′ C₂ C₂′}
              {L : Γ ⊢G A} {L′ : Γ′ ⊢G A′} {M : Γ ⊢G B} {M′ : Γ′ ⊢G B′} {N : Γ ⊢G C} {N′ : Γ′ ⊢G C′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ L ⊑ᴳ L′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → Γ , Γ′ ⊢ N ⊑ᴳ N′
    → {ma : A ▹ A₁ ⊎ A₂} {ma′ : A′ ▹ A₁′ ⊎ A₂′} {mb : B ▹ B₁ ⇒ B₂} {mb′ : B′ ▹ B₁′ ⇒ B₂′} {mc : C ▹ C₁ ⇒ C₂} {mc′ : C′ ▹ C₁′ ⇒ C₂′}
    → {ab : A₁ ~ B₁} {ab′ : A₁′ ~ B₁′} {ac : A₂ ~ C₁} {ac′ : A₂′ ~ C₁′} {bc : B₂ ~ C₂} {bc′ : B₂′ ~ C₂′}
    → Γ , Γ′ ⊢ case L M N ℓ {ma} {mb} {mc} {ab} {ac} {bc} ⊑ᴳ case L′ M′ N′ ℓ′ {ma′} {mb′} {mc′} {ab′} {ac′} {bc′}


-- Similar to the example in Fig. 5, Refined Criteria.
_ : ∅ , ∅ ⊢ ((ƛ ⋆ ˙ (` Z)) · ($_ 42 {P-Base}) at pos 0) {match⇒⇒} {unk~L} ⊑ᴳ ((ƛ (` Nat) ˙ (` Z)) · ($_ 42 {P-Base}) at pos 0) {match⇒⇒} {base~}
_ = ⊑ᴳ-· (⊑ᴳ-ƛ unk⊑ (⊑ᴳ-var refl)) ⊑ᴳ-prim
