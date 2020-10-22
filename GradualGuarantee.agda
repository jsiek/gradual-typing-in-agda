open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂; inspect; [_])
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.Empty using (⊥; ⊥-elim)

-- We're using simple cast with inert cross cast - at least for now.
open import GroundInertX using (Cast; cast; Inert; Active; Cross; applyCast; pcs; cs; dom; cod; fstC; sndC; inlC; inrC; compile)
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
open Frame

infix 6 _,_⊢_⊑ᴳ_
infix 6 _,_⊢_⊑ᶜ_

-- Term precision for GTLC - M₁ ⊑ᴳ M₂ means that M₂ is *more precise* than M₁ .
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
    → Γ , Γ′ ⊢ inr A M ⊑ᴳ inr A′ M′

  ⊑ᴳ-case : ∀ {Γ Γ′ A A′ A₁ A₁′ A₂ A₂′ B B′ B₁ B₁′ B₂ B₂′ C C′ C₁ C₁′ C₂ C₂′}
              {L : Γ ⊢G A} {L′ : Γ′ ⊢G A′} {M : Γ ⊢G B} {M′ : Γ′ ⊢G B′} {N : Γ ⊢G C} {N′ : Γ′ ⊢G C′} {ℓ ℓ′}
    → Γ , Γ′ ⊢ L ⊑ᴳ L′
    → Γ , Γ′ ⊢ M ⊑ᴳ M′
    → Γ , Γ′ ⊢ N ⊑ᴳ N′
    → {ma : A ▹ A₁ ⊎ A₂} {ma′ : A′ ▹ A₁′ ⊎ A₂′} {mb : B ▹ B₁ ⇒ B₂} {mb′ : B′ ▹ B₁′ ⇒ B₂′} {mc : C ▹ C₁ ⇒ C₂} {mc′ : C′ ▹ C₁′ ⇒ C₂′}
    → {ab : A₁ ~ B₁} {ab′ : A₁′ ~ B₁′} {ac : A₂ ~ C₁} {ac′ : A₂′ ~ C₁′} {bc : B₂ ~ C₂} {bc′ : B₂′ ~ C₂′}
      ------------------------------------------------------------------------------------------------------------
    → Γ , Γ′ ⊢ case L M N ℓ {ma} {mb} {mc} {ab} {ac} {bc} ⊑ᴳ case L′ M′ N′ ℓ′ {ma′} {mb′} {mc′} {ab′} {ac′} {bc′}


-- Term precision of CC.
data _,_⊢_⊑ᶜ_ : ∀ (Γ Γ′ : Context) → {A A′ : Type} → Γ ⊢ A → Γ′ ⊢ A′ → Set where

  ⊑ᶜ-prim : ∀ {Γ Γ′ A} {k : rep A} {i : Prim A}
      ------------------------------
    → Γ , Γ′ ⊢ $_ {Γ} k {i} ⊑ᶜ $_ {Γ′} k {i}

  ⊑ᴳ-var : ∀ {Γ Γ′ A A′} {x : Γ ∋ A} {x′ : Γ′ ∋ A′}
    → ∋→ℕ x ≡ ∋→ℕ x′
      -----------------
    → Γ , Γ′ ⊢ ` x ⊑ᶜ ` x′

  ⊑ᶜ-ƛ : ∀ {Γ Γ′ A A′ B B′} {N : Γ , A ⊢ B} {N′ : Γ′ , A′ ⊢ B′}
    → A ⊑ A′
    → (Γ , A) , (Γ′ , A′) ⊢ N ⊑ᶜ N′
      ------------------------------
    → Γ , Γ′ ⊢ ƛ N ⊑ᶜ ƛ N′

  ⊑ᶜ-· : ∀ {Γ Γ′ A A′ B B′} {L : Γ ⊢ A ⇒ B} {L′ : Γ′ ⊢ A′ ⇒ B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      --------------------------
    → Γ , Γ′ ⊢ L · M ⊑ᶜ L′ · M′

  ⊑ᶜ-if : ∀ {Γ Γ′ A A′} {L : Γ ⊢ ` 𝔹} {L′ : Γ′ ⊢ ` 𝔹} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {N : Γ ⊢ A} {N′ : Γ′ ⊢ A′}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → Γ , Γ′ ⊢ N ⊑ᶜ N′
      ---------------------------------
    → Γ , Γ′ ⊢ if L M N ⊑ᶜ if L′ M′ N′

  ⊑ᶜ-cons : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {N : Γ ⊢ B} {N′ : Γ′ ⊢ B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → Γ , Γ′ ⊢ N ⊑ᶜ N′
      --------------------------------
    → Γ , Γ′ ⊢ cons M N ⊑ᶜ cons M′ N′

  ⊑ᶜ-fst : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A `× B} {M′ : Γ′ ⊢ A′ `× B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -------------------------
    → Γ , Γ′ ⊢ fst M ⊑ᶜ fst M′

  ⊑ᶜ-snd : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A `× B} {M′ : Γ′ ⊢ A′ `× B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -------------------------
    → Γ , Γ′ ⊢ snd M ⊑ᶜ snd M′

  ⊑ᶜ-inl : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inl {B = B} M ⊑ᶜ inl {B = B′} M′

  ⊑ᶜ-inr : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ B} {M′ : Γ′ ⊢ B′}
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------------------
    → Γ , Γ′ ⊢ inr {A = A} M ⊑ᶜ inr {A = A′} M′

  ⊑ᶜ-case : ∀ {Γ Γ′ A A′ B B′ C C′} {L : Γ ⊢ A `⊎ B} {L′ : Γ′ ⊢ A′ `⊎ B′} {M : Γ ⊢ A ⇒ C} {M′ : Γ′ ⊢ A′ ⇒ C′} {N : Γ ⊢ B ⇒ C} {N′ : Γ′ ⊢ B′ ⇒ C′}
    → Γ , Γ′ ⊢ L ⊑ᶜ L′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
    → Γ , Γ′ ⊢ N ⊑ᶜ N′
      -------------------------------------
    → Γ , Γ′ ⊢ case L M N ⊑ᶜ case L′ M′ N′

  ⊑ᶜ-cast : ∀ {Γ Γ′ A A′ B B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → A ⊑ A′ → B ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------------
    → Γ , Γ′ ⊢ M ⟨ c ⟩ ⊑ᶜ M′ ⟨ c′ ⟩

  ⊑ᶜ-castl : ∀ {Γ Γ′ A A′ B} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
    → A ⊑ A′ → B ⊑ A′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      -----------------------
    → Γ , Γ′ ⊢ M ⟨ c ⟩ ⊑ᶜ M′

  ⊑ᶜ-castr : ∀ {Γ Γ′ A A′ B′} {M : Γ ⊢ A} {M′ : Γ′ ⊢ A′} {c′ : Cast (A′ ⇒ B′)}
    → A ⊑ A′ → A ⊑ B′
    → Γ , Γ′ ⊢ M ⊑ᶜ M′
      ------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ M′ ⟨ c′ ⟩

  ⊑ᶜ-blame : ∀ {Γ Γ′ A A′} {M : Γ ⊢ A} {ℓ}
    → A ⊑ A′
      -------------------------------
    → Γ , Γ′ ⊢ M ⊑ᶜ blame {Γ′} {A′} ℓ


-- Similar to the example in Fig. 5, Refined Criteria.
_ : ∅ , ∅ ⊢ ((ƛ ⋆ ˙ (` Z)) · ($_ 42 {P-Base}) at pos 0) {match⇒⇒} {unk~L} ⊑ᴳ ((ƛ (` Nat) ˙ (` Z)) · ($_ 42 {P-Base}) at pos 0) {match⇒⇒} {base~}
_ = ⊑ᴳ-· (⊑ᴳ-ƛ unk⊑ (⊑ᴳ-var refl)) ⊑ᴳ-prim

_ : ∅ , ∅ ⊢ ƛ_ {B = ⋆} {⋆} (` Z) ⊑ᶜ ƛ_ {B = ` Nat} {` Nat} (` Z)
_ = ⊑ᶜ-ƛ unk⊑ (⊑ᴳ-var refl)

⊑*→⊑ : ∀ {Γ Γ′ A A′}
  → (x : Γ ∋ A) → (x′ : Γ′ ∋ A′)
  → Γ ⊑* Γ′
  → ∋→ℕ x ≡ ∋→ℕ x′
    -----------------
  → A ⊑ A′
⊑*→⊑ Z Z (⊑*-, lp lpc) refl = lp
⊑*→⊑ (S x) (S x′) (⊑*-, _ lpc) eq = ⊑*→⊑ x x′ lpc (suc-injective eq)

▹⇒-pres-prec : ∀ {A A′ A₁ A₁′ A₂ A₂′}
  → (m : A ▹ A₁ ⇒ A₂) → (m′ : A′ ▹ A₁′ ⇒ A₂′)
  → A ⊑ A′
    --------------------
  → A₁ ⊑ A₁′ × A₂ ⊑ A₂′
▹⇒-pres-prec match⇒⇒ match⇒⇒ (fun⊑ lp₁ lp₂) = ⟨ lp₁ , lp₂ ⟩
▹⇒-pres-prec match⇒⇒ match⇒⋆ ()
▹⇒-pres-prec match⇒⋆ match⇒⇒ lp = ⟨ unk⊑ , unk⊑ ⟩
▹⇒-pres-prec match⇒⋆ match⇒⋆ lp = ⟨ unk⊑ , unk⊑ ⟩

▹×-pres-prec : ∀ {A A′ A₁ A₁′ A₂ A₂′}
  → (m : A ▹ A₁ × A₂) → (m′ : A′ ▹ A₁′ × A₂′)
  → A ⊑ A′
  → A₁ ⊑ A₁′ × A₂ ⊑ A₂′
▹×-pres-prec match×× match×× (pair⊑ lp₁ lp₂) = ⟨ lp₁ , lp₂ ⟩
▹×-pres-prec match×× match×⋆ = λ ()
▹×-pres-prec match×⋆ match×× lp = ⟨ unk⊑ , unk⊑ ⟩
▹×-pres-prec match×⋆ match×⋆ lp = ⟨ lp , lp ⟩

▹⊎-pres-prec : ∀ {A A′ A₁ A₁′ A₂ A₂′}
  → (m : A ▹ A₁ ⊎ A₂) (m′ : A′ ▹ A₁′ ⊎ A₂′)
  → A ⊑ A′
    --------------------
  → A₁ ⊑ A₁′ × A₂ ⊑ A₂′
▹⊎-pres-prec match⊎⊎ match⊎⊎ (sum⊑ lp₁ lp₂) = ⟨ lp₁ , lp₂ ⟩
▹⊎-pres-prec match⊎⋆ match⊎⊎ lp = ⟨ unk⊑ , unk⊑ ⟩
▹⊎-pres-prec match⊎⋆ match⊎⋆ lp = ⟨ lp , lp ⟩

⨆-pres-prec : ∀ {A A′ B B′}
  → (aa : A ~ A′) → (bb : B ~ B′)
  → A ⊑ B
  → A′ ⊑ B′
    -------------
  → ⨆ aa ⊑ ⨆ bb
⨆-pres-prec unk~L unk~L unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~L unk~R unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~L base~ unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~L (fun~ _ _) unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~L (pair~ _ _) unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~L (sum~ _ _) unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~R unk~L unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~R unk~R unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~R base~ unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~R (fun~ _ _) unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~R (pair~ _ _) unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~R (sum~ _ _) unk⊑ unk⊑ = unk⊑
⨆-pres-prec unk~L unk~L unk⊑ base⊑ = base⊑
⨆-pres-prec unk~L base~ unk⊑ base⊑ = base⊑
⨆-pres-prec unk~L unk~L unk⊑ (fun⊑ lp₁ lp₂) = fun⊑ lp₁ lp₂
⨆-pres-prec unk~L (fun~ aa bb) unk⊑ (fun⊑ lp₁ lp₂) =
  fun⊑ (⨆-pres-prec unk~R aa lp₁ unk⊑) (⨆-pres-prec unk~L bb unk⊑ lp₂)
⨆-pres-prec unk~L unk~L unk⊑ (pair⊑ lp₁ lp₂) = pair⊑ lp₁ lp₂
⨆-pres-prec unk~L (pair~ aa bb) unk⊑ (pair⊑ lp₁ lp₂) =
  pair⊑ (⨆-pres-prec unk~L aa unk⊑ lp₁) (⨆-pres-prec unk~L bb unk⊑ lp₂)
⨆-pres-prec unk~L unk~L unk⊑ (sum⊑ lp₁ lp₂) = sum⊑ lp₁ lp₂
⨆-pres-prec unk~L (sum~ aa bb) unk⊑ (sum⊑ lp₁ lp₂) =
  sum⊑ (⨆-pres-prec unk~L aa unk⊑ lp₁) (⨆-pres-prec unk~L bb unk⊑ lp₂)
⨆-pres-prec unk~R unk~R base⊑ unk⊑ = base⊑
⨆-pres-prec unk~R base~ base⊑ unk⊑ = base⊑
⨆-pres-prec base~ base~ base⊑ base⊑ = base⊑
⨆-pres-prec unk~R unk~R (fun⊑ lp₁ lp₂) unk⊑ = fun⊑ lp₁ lp₂
⨆-pres-prec unk~R (fun~ aa bb) (fun⊑ lp₁ lp₂) unk⊑ =
  fun⊑ (⨆-pres-prec unk~L aa unk⊑ lp₁) (⨆-pres-prec unk~R bb lp₂ unk⊑)
⨆-pres-prec (fun~ aa₁ aa₂) (fun~ bb₁ bb₂) (fun⊑ lpa₁ lpa₂) (fun⊑ lpb₁ lpb₂) =
  fun⊑ (⨆-pres-prec aa₁ bb₁ lpb₁ lpa₁) (⨆-pres-prec aa₂ bb₂ lpa₂ lpb₂)
⨆-pres-prec unk~R unk~R (pair⊑ lp₁ lp₂) unk⊑ = pair⊑ lp₁ lp₂
⨆-pres-prec unk~R (pair~ bb₁ bb₂) (pair⊑ lp₁ lp₂) unk⊑ =
  pair⊑ (⨆-pres-prec unk~R bb₁ lp₁ unk⊑) (⨆-pres-prec unk~R bb₂ lp₂ unk⊑)
⨆-pres-prec (pair~ aa₁ aa₂) (pair~ bb₁ bb₂) (pair⊑ lpa₁ lpa₂) (pair⊑ lpb₁ lpb₂) =
  pair⊑ (⨆-pres-prec aa₁ bb₁ lpa₁ lpb₁) (⨆-pres-prec aa₂ bb₂ lpa₂ lpb₂)
⨆-pres-prec unk~R unk~R (sum⊑ lp₁ lp₂) unk⊑ = sum⊑ lp₁ lp₂
⨆-pres-prec unk~R (sum~ bb₁ bb₂) (sum⊑ lp₁ lp₂) unk⊑ =
  sum⊑ (⨆-pres-prec unk~R bb₁ lp₁ unk⊑) (⨆-pres-prec unk~R bb₂ lp₂ unk⊑)
⨆-pres-prec (sum~ aa₁ aa₂) (sum~ bb₁ bb₂) (sum⊑ lpa₁ lpa₂) (sum⊑ lpb₁ lpb₂) =
  sum⊑ (⨆-pres-prec aa₁ bb₁ lpa₁ lpb₁) (⨆-pres-prec aa₂ bb₂ lpa₂ lpb₂)

-- Compilation from GTLC to CC preserves precision.
{- We assume Γ ⊢ e ↝ f ⦂ A and Γ′ ⊢ e′ ↝ f′ ⦂ A′ . -}
compile-pres-prec : ∀ {Γ Γ′ A A′} {e : Γ ⊢G A} {e′ : Γ′ ⊢G A′}
  → Γ ⊑* Γ′
  → Γ , Γ′ ⊢ e ⊑ᴳ e′
    -------------------------------
  → (A ⊑ A′) × (Γ , Γ′ ⊢ compile {Γ} {A} e ⊑ᶜ compile {Γ′} {A′} e′)
compile-pres-prec lpc (⊑ᴳ-prim {A = A}) = ⟨ Refl⊑ , ⊑ᶜ-prim ⟩
compile-pres-prec lpc (⊑ᴳ-var {x = x} {x′} eq) = ⟨ ⊑*→⊑ x x′ lpc eq , ⊑ᴳ-var eq ⟩
compile-pres-prec lpc (⊑ᴳ-ƛ lpA lpe) =
  let ⟨ lpB , lpeN ⟩ = compile-pres-prec (⊑*-, lpA lpc) lpe in
    ⟨ (fun⊑ lpA lpB) , ⊑ᶜ-ƛ lpA lpeN ⟩
compile-pres-prec lpc (⊑ᴳ-· lpeL lpeM {m = m} {m′ = m′}) =
  let ⟨ lpA , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
  let ⟨ lpB , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
  let ⟨ lpA₁ , lpA₂ ⟩ = ▹⇒-pres-prec m m′ lpA in
    ⟨ lpA₂ , ⊑ᶜ-· (⊑ᶜ-cast lpA (fun⊑ lpA₁ lpA₂) lpeL′) (⊑ᶜ-cast lpB lpA₁ lpeM′) ⟩
compile-pres-prec lpc (⊑ᴳ-if lpeL lpeM lpeN {aa = aa} {aa′}) =
  let ⟨ lpB , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
  let ⟨ lpA₁ , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
  let ⟨ lpA₂ , lpeN′ ⟩ = compile-pres-prec lpc lpeN in
  let lp⨆aa = ⨆-pres-prec aa aa′ lpA₁ lpA₂ in
    ⟨ lp⨆aa , ⊑ᶜ-if (⊑ᶜ-cast lpB base⊑ lpeL′) (⊑ᶜ-cast lpA₁ lp⨆aa lpeM′) (⊑ᶜ-cast lpA₂ lp⨆aa lpeN′) ⟩
compile-pres-prec lpc (⊑ᴳ-cons lpeM lpeN) =
  let ⟨ lpA , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
  let ⟨ lpB , lpeN′ ⟩ = compile-pres-prec lpc lpeN in
    ⟨ pair⊑ lpA lpB , ⊑ᶜ-cons lpeM′ lpeN′ ⟩
compile-pres-prec lpc (⊑ᴳ-fst lpe {m} {m′}) =
  let ⟨ lp , lpe′ ⟩ = compile-pres-prec lpc lpe in
  let ⟨ lp₁ , lp₂ ⟩ = ▹×-pres-prec m m′ lp in
    ⟨ lp₁ , ⊑ᶜ-fst (⊑ᶜ-cast lp (pair⊑ lp₁ lp₂) lpe′) ⟩
compile-pres-prec lpc (⊑ᴳ-snd lpe {m} {m′}) =
  let ⟨ lp , lpe′ ⟩ = compile-pres-prec lpc lpe in
  let ⟨ lp₁ , lp₂ ⟩ = ▹×-pres-prec m m′ lp in
    ⟨ lp₂ , ⊑ᶜ-snd (⊑ᶜ-cast lp (pair⊑ lp₁ lp₂) lpe′) ⟩
compile-pres-prec lpc (⊑ᴳ-inl lpB lpe) =
  let ⟨ lpA , lpe′ ⟩ = compile-pres-prec lpc lpe in
    ⟨ sum⊑ lpA lpB , ⊑ᶜ-inl lpe′ ⟩
compile-pres-prec lpc (⊑ᴳ-inr lpA lpe) =
  let ⟨ lpB , lpe′ ⟩ = compile-pres-prec lpc lpe in
    ⟨ sum⊑ lpA lpB , ⊑ᶜ-inr lpe′ ⟩
compile-pres-prec lpc (⊑ᴳ-case lpeL lpeM lpeN {ma} {ma′} {mb} {mb′} {mc} {mc′} {bc = bc} {bc′}) =
  let ⟨ lpA , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
  let ⟨ lpB , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
  let ⟨ lpC , lpeN′ ⟩ = compile-pres-prec lpc lpeN in
  let ⟨ lpA₁ , lpA₂ ⟩ = ▹⊎-pres-prec ma ma′ lpA in
  let ⟨ lpB₁ , lpB₂ ⟩ = ▹⇒-pres-prec mb mb′ lpB in
  let ⟨ lpC₁ , lpC₂ ⟩ = ▹⇒-pres-prec mc mc′ lpC in
  let lp⨆bc = ⨆-pres-prec bc bc′ lpB₂ lpC₂ in
    ⟨ lp⨆bc , ⊑ᶜ-case (⊑ᶜ-cast (sum⊑ lpA₁ lpA₂) (sum⊑ lpB₁ lpC₁) (⊑ᶜ-cast lpA (sum⊑ lpA₁ lpA₂) lpeL′))
                       (⊑ᶜ-cast (fun⊑ lpB₁ lpB₂) (fun⊑ lpB₁ lp⨆bc) (⊑ᶜ-cast lpB (fun⊑ lpB₁ lpB₂) lpeM′))
                       (⊑ᶜ-cast (fun⊑ lpC₁ lpC₂) (fun⊑ lpC₁ lp⨆bc) (⊑ᶜ-cast lpC (fun⊑ lpC₁ lpC₂) lpeN′)) ⟩

cast-eq-inv : ∀ {Γ A A′ B} {M : Γ ⊢ A} {M′ : Γ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B)}
  → M ⟨ c ⟩ ≡ M′ ⟨ c′ ⟩
    --------------------
  → Σ[ eq ∈ (A ≡ A′) ] (subst-eq (λ □ → Cast (□ ⇒ B)) eq c ≡ c′) × (subst-eq (λ □ → Γ ⊢ □) eq M ≡ M′)
cast-eq-inv refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

fst-pres-⊑blame : ∀ {Γ Γ′ A A′ B B′} {N : Γ ⊢ A `× B} {ℓ}
  → Γ , Γ′ ⊢ N ⊑ᶜ blame {Γ′} {A′ `× B′} ℓ
  → Γ , Γ′ ⊢ fst N ⊑ᶜ blame {Γ′} {A′} ℓ
fst-pres-⊑blame (⊑ᶜ-castl _ (pair⊑ lp₁ lp₂) lpf) = ⊑ᶜ-blame lp₁
fst-pres-⊑blame (⊑ᶜ-blame (pair⊑ lp₁ lp₂)) = ⊑ᶜ-blame lp₁

blame⋢V : ∀ {Γ Γ′ A A′} {V : Γ′ ⊢ A′} {ℓ}
  → Value V
    ----------------------------------
  → ¬ (Γ , Γ′ ⊢ blame {Γ} {A} ℓ ⊑ᶜ V)
blame⋢V (ParamCastAux.V-cast v) (⊑ᶜ-castr _ _ lp) = blame⋢V v lp

eq-—↠ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ≡ N
  → M —↠ N
eq-—↠ {M = M} {N} eq rewrite eq = N ∎


-- applyCast-pres-⊑V : ∀ {Γ Γ′ S T T′} {V : Γ ⊢ S} {V′ : Γ′ ⊢ T′} {vV : Value V} {c : Cast (S ⇒ T)}
--   → Value V′ → (a : Active c)
--   → S ⊑ T′ → T ⊑ T′
--   → Γ , Γ′ ⊢ V ⊑ᶜ V′
--     ------------------------------------
--   → Γ , Γ′ ⊢ applyCast V vV c {a} ⊑ᶜ V′
-- applyCast-pres-⊑V _ (Active.activeId (cast A .A _)) lp1 lp2 ⊑ᶜ-prim = ⊑ᶜ-prim
-- applyCast-pres-⊑V _ (Active.activeId (cast A .A _)) _ _ (⊑ᶜ-cast lp1 lp2 lpV) = ⊑ᶜ-cast lp1 lp2 lpV
-- applyCast-pres-⊑V _ (Active.activeId (cast A .A _)) _ _ (⊑ᶜ-castl lp1 lp2 lpV) = ⊑ᶜ-castl lp1 lp2 lpV
-- applyCast-pres-⊑V _ (Active.activeId (cast A .A _)) _ _ (⊑ᶜ-castr lp1 lp2 lpV) = ⊑ᶜ-castr lp1 lp2 lpV
-- applyCast-pres-⊑V {V = V} {vV = vV} _ (Active.activeProj (cast ⋆ T _) neq) lp1 lp2 (⊑ᶜ-cast {c = cast A ⋆ _} {cast A′ B′ _ {c~′}} lp3 lp4 lpV)
--   with canonical⋆ V vV
-- ... | ⟨ A₁ , ⟨ M₁ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with cast-eq-inv meq
-- ...   | ⟨ refl , ⟨ refl , refl ⟩ ⟩ with A₁ `~ T
-- ...     | yes _ = ⊑ᶜ-cast lp3 lp2 lpV
-- ...     | no A₁≁T = contradiction (lp-consis c~′ lp3 lp2) A₁≁T
-- applyCast-pres-⊑V {V = V} {vV = vV} _ (Active.activeProj (cast ⋆ T _) neq) lp1 lp2 (⊑ᶜ-castl lp3 lp4 lpV)
--   with canonical⋆ V vV
-- ... | ⟨ A₁ , ⟨ M₁ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with cast-eq-inv meq
-- ...   | ⟨ refl , ⟨ refl , refl ⟩ ⟩ with A₁ `~ T
-- ...     | yes _ = ⊑ᶜ-castl lp3 lp2 lpV
-- ...     | no A₁≁T = contradiction (lp-consis Refl~ lp3 lp2) A₁≁T
-- applyCast-pres-⊑V {V = V} {vV = vV} (ParamCastAux.V-cast {i = i} v) (Active.activeProj (cast ⋆ T _) neq) lp1 lp2 (⊑ᶜ-castr lp3 lp4 lpV)
--   with canonical⋆ V vV
-- ... | ⟨ A₁ , ⟨ M₁ , ⟨ c₁ , ⟨ i₁ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A₁ `~ T
-- ...   | yes _ = {!!}
-- ...   | no _ = {!!}

sim-fst-inert : ∀ {T A A′ B B′} {V : ∅ ⊢ T} {M′ : ∅ ⊢ A′} {N′ : ∅ ⊢ B′} {c : Cast (T ⇒ A `× B)}
  → Value V
  → (i : Inert c)
  → T ⊑ A′ `× B′ → A `× B ⊑ A′ `× B′
  → ∅ , ∅ ⊢ V ⊑ᶜ cons M′ N′
    ----------------------------------------------------
  → ∃[ M ] ((fst (V ⟨ c ⟩) —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ M′))
sim-fst-inert (V-pair vM vN) (Inert.I-pair (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~)) lp1 lp2 (⊑ᶜ-cons {M = M} {N = N} lpV _)
  with lp1 | lp2
... | pair⊑ lp11 lp12 | pair⊑ lp21 lp22 =
    ⟨ M ⟨ fstC (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~) Cross.C-pair ⟩ , ⟨ rd* , (⊑ᶜ-castl lp11 lp21 lpV) ⟩ ⟩
  where
  rd* =
    _
      —→⟨ fst-cast (V-pair vM vN) {Cross.C-pair} ⟩
    _
      —→⟨ ξ {F = F-cast _} (β-fst vM vN) ⟩
    _ ∎
sim-fst-inert (V-cast {i = i₀} vM) (Inert.I-pair (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~)) lp1 lp2 (⊑ᶜ-castl {M = M} {c = c₀} lp3 lp4 lpM)
  with sim-fst-inert vM i₀ lp3 lp1 lpM | lp2 | lp4
... | ⟨ M₁ , ⟨ rd* , lpM₁ ⟩ ⟩ | pair⊑ lp21 lp22 | pair⊑ lp41 lp42 =
  ⟨ (M₁ ⟨ fstC (cast (A₁ `× B₁) (A₂ `× B₂) ℓ c~) Cross.C-pair ⟩) , ⟨ rd*′ , ⊑ᶜ-castl lp41 lp21 lpM₁ ⟩ ⟩
  where
  rd*′ =
    _
      —→⟨ fst-cast (V-cast {i = i₀} vM) {Cross.C-pair} ⟩
    -- By congruence of multi-step reduction.
    plug-cong (F-cast _) rd*

applyCast-castl : ∀ {Γ Γ′ A A′ B B′} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
  → (vV : Value V) → Value V′
  → (a : Active c) → Inert c′
  → A ⊑ A′ → B ⊑ B′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
    -------------------------------------------
  → Γ , Γ′ ⊢ applyCast V vV c {a} ⊑ᶜ V′ ⟨ c′ ⟩
applyCast-castl _ _ (Active.A-id c) (Inert.I-inj x c₁) lp1 lp2 ⊑ᶜ-prim = ⊑ᶜ-castr lp1 lp2 ⊑ᶜ-prim
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-ƛ x lpV) = {!!}
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-cons lpV lpV₁) = {!!}
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-inl lpV) = {!!}
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-inr lpV) = {!!}
applyCast-castl vV vV′ (Active.A-id c) _ lp1 lp2 (⊑ᶜ-cast x x₁ lpV) = ⊑ᶜ-castr x₁ lp2 (⊑ᶜ-cast x x₁ lpV)
applyCast-castl {c′ = cast _ _ _ c~′} vV vV′ (Active.A-proj (cast ⋆ B _ _) x₂) i lp1 lp2 (⊑ᶜ-cast x x₁ lpV)
  with ground? B
... | yes b-g with canonical⋆ _ vV
...   | ⟨ G , ⟨ V₁ , ⟨ c₁ , ⟨ i₁ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq
  with gnd-eq? G B {GroundInertX.inert-ground c₁ i₁} {b-g}
...     | yes ap-b = {!!}
...     | no  ap-b = {!!}
applyCast-castl {c′ = cast _ _ _ c~′} vV vV′ (Active.A-proj (cast ⋆ B _ _) x₂) i lp1 lp2 (⊑ᶜ-cast x x₁ lpV)
    | no b-ng = {!!}

applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-castl x x₁ lpV) = {!!}
applyCast-castl vV vV′ a i lp1 lp2 (⊑ᶜ-castr x x₁ lpV) = {!!}

catchup : ∀ {Γ Γ′ A A′} {M : Γ ⊢ A} {V′ : Γ′ ⊢ A′}
  → Value V′
  → Γ , Γ′ ⊢ M ⊑ᶜ V′
  → ∃[ V ] ((Value V) × (M —↠ V) × (Γ , Γ′ ⊢ V ⊑ᶜ V′))
catchup {M = $ k} v ⊑ᶜ-prim = ⟨ $ k , ⟨ V-const , ⟨ _ ∎ , ⊑ᶜ-prim ⟩ ⟩ ⟩
catchup v (⊑ᶜ-ƛ x lpM) = {!!}
catchup v (⊑ᶜ-cons lpM lpM₁) = {!!}
catchup v (⊑ᶜ-inl lpM) = {!!}
catchup v (⊑ᶜ-inr lpM) = {!!}
catchup (ParamCastAux.V-cast v) (⊑ᶜ-cast {c = c} lp1 lp2 lpM) with catchup v lpM
... | ⟨ V , ⟨ vV , ⟨ rd* , lpV ⟩ ⟩ ⟩ with GroundInertX.ActiveOrInert c
...   | inj₁ a = ⟨ applyCast V vV c {a} , ⟨ {!!} , ⟨ rd*′ , {!!} ⟩ ⟩ ⟩
  where
  rd*′ = ↠-trans (plug-cong (F-cast c) rd*) ( _ —→⟨ _—→_.cast vV {a} ⟩ _ ∎)
...   | inj₂ i = ⟨ V ⟨ c ⟩ , ⟨ ParamCastAux.V-cast {i = i} vV , ⟨ plug-cong (F-cast c) rd* , ⊑ᶜ-cast lp1 lp2 lpV ⟩ ⟩ ⟩
catchup v (⊑ᶜ-castl x x₁ lpM) = {!!}
catchup v (⊑ᶜ-castr x x₁ lpM) = {!!}

sim-fst : ∀ {A A′ B B′} {N : ∅ ⊢ A `× B} {M′ : ∅ ⊢ A′} {N′ : ∅ ⊢ B′}
  → ∅ , ∅ ⊢ N ⊑ᶜ cons M′ N′
    ------------------------------------------
  → ∃[ M ] ((fst N —↠ M) × (∅ , ∅ ⊢ M ⊑ᶜ M′))
sim-fst (⊑ᶜ-cons lpf lpf₁) = {!!}
sim-fst (⊑ᶜ-castl {A = T} {M = N₁} {c = c} lp1 lp2 lpf) = {!!}

gradual-guarantee : ∀ {A A′} {M₁ : ∅ ⊢ A} {M₁′ M₂′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ M₁ ⊑ᶜ M₁′     -- Note M₁′ is more precise here.
  → M₁′ —→ M₂′
    ---------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))

gradual-guarantee-fst : ∀ {A A′ B B′} {N₁ : ∅ ⊢ A `× B} {N₁′ : ∅ ⊢ A′ `× B′} {M₁ : ∅ ⊢ A} {M₁′ M₂′ : ∅ ⊢ A′}
  → ∅ , ∅ ⊢ N₁ ⊑ᶜ N₁′
  → M₁ ≡ fst N₁ → M₁′ ≡ fst N₁′
  → M₁′ —→ M₂′
    -----------------------------------------------
  → ∃[ M₂ ] ((M₁ —↠ M₂) × (∅ , ∅ ⊢ M₂ ⊑ᶜ M₂′))

gradual-guarantee-fst {N₁ = N₁} {N₁′} {M₁} {M₁′} {M₂′} N₁⊑N₁′ refl eq2 (ξ {M′ = N₂′} {F} N₁′→N₂′) with plug-inv-fst F eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩ with gradual-guarantee N₁⊑N₁′ N₁′→N₂′
...   | ⟨ N₂ , ⟨ N₁↠N₂ , N₂⊑N₂′ ⟩ ⟩ = ⟨ fst N₂ , ⟨ plug-cong F-fst N₁↠N₂ , ⊑ᶜ-fst N₂⊑N₂′ ⟩ ⟩
gradual-guarantee-fst {N₁ = N₁} lpf refl eq2 (ξ-blame {F = F}) with plug-inv-fst F eq2
... | ⟨ refl , ⟨ refl , refl ⟩ ⟩ = ⟨ fst N₁ , ⟨ fst N₁ ∎ , fst-pres-⊑blame lpf ⟩ ⟩
gradual-guarantee-fst {N₁ = N₁} lpf refl refl (β-fst {V = V′} {W = W′} vV′ vW′) = sim-fst lpf
gradual-guarantee-fst lpf refl refl (fst-cast x) = {!!}

-- gradual-guarantee (⊑ᶜ-prim) rd = ⊥-elim (V⌿→ V-const rd)
-- gradual-guarantee (⊑ᶜ-ƛ _ _) rd = ⊥-elim (V⌿→ V-ƛ rd)
-- gradual-guarantee (⊑ᶜ-· lpf lpf₁) rd = {!!}
-- gradual-guarantee (⊑ᶜ-if lpf lpf₁ lpf₂) rd = {!!}
-- gradual-guarantee (⊑ᶜ-cons lpf lpf₁) rd = {!!}
-- gradual-guarantee (⊑ᶜ-fst lpf) rd = gradual-guarantee-fst lpf refl refl rd
-- gradual-guarantee (⊑ᶜ-snd lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-inl lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-inr lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-case lpf lpf₁ lpf₂) rd = {!!}
-- gradual-guarantee (⊑ᶜ-cast x x₁ lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-castl x x₁ lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-castr x x₁ lpf) rd = {!!}
-- gradual-guarantee (⊑ᶜ-blame _) rd = ⊥-elim (blame⌿→ rd)
