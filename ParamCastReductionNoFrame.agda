open import Types
open import PreCastStructure
open import CastStructure
open import Labels
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)



module ParamCastReductionNoFrame (cs : CastStruct) where

  open CastStruct cs

  import ParamCastCalculus
  open ParamCastCalculus Cast


  import ParamCastAux
  open ParamCastAux precast


  infix 2 _—→_

  data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    -- Congruence rules
    ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
      → L —→ L′
        ---------------------
      → L · M —→ L′ · M

    ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
      → {v : Value V}
      → M —→ M′
        ------------------
      → V · M —→ V · M′

    ξ-if : ∀ {Γ A} {L L′} {M N : Γ ⊢ A}
      → L —→ L′
        ------------------------
      → if L M N —→ if L′ M N

    ξ-x₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
      → M —→ M′
        ------------------------
      → cons M N —→ cons M′ N

    ξ-×₂ : ∀ {Γ A B} {M : Γ ⊢ A} {N N′ : Γ ⊢ B}
      → N —→ N′
        ------------------------
      → cons M N —→ cons M N′

    ξ-fst : ∀ {Γ A B} {M M′ : Γ ⊢ A `× B}
      → M —→ M′
        ------------------
      → fst M —→ fst M′

    ξ-snd : ∀ {Γ A B} {M M′ : Γ ⊢ A `× B}
      → M —→ M′
      → snd M —→ snd M′

    ξ-inl : ∀ {Γ A B} {M M′ : Γ ⊢ A}
      → M —→ M′
      → inl {B = B} M —→ inl M′

    ξ-inr : ∀ {Γ A B} {M M′ : Γ ⊢ B}
      → M —→ M′
      → inr {A = A} M —→ inr M′

    ξ-case : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⊎ B} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C}
      → L —→ L′
      → case L M N —→ case L′ M N

    ξ-cast : ∀ {Γ A B} {M M′ : Γ ⊢ A} {c : Cast (A ⇒ B)}
      → M —→ M′
      → M ⟨ c ⟩ —→ M′ ⟨ c ⟩

    ξ-blame-·₁ : ∀ {Γ A B} {M : Γ ⊢ A} {ℓ}
        ---------------------
      → (blame {A = A ⇒ B} ℓ) · M —→ blame ℓ

    ξ-blame-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {v : Value V} {ℓ}
        ------------------
      → V · (blame ℓ) —→ blame ℓ

    ξ-blame-if : ∀ {Γ A} {M N : Γ ⊢ A} {ℓ}
        ------------------------
      → if (blame ℓ) M N —→ blame ℓ

    ξ-blame-x₁ : ∀ {Γ A B} {N : Γ ⊢ B} {ℓ}
        ------------------------
      → cons {A = A} (blame ℓ) N —→ blame ℓ

    ξ-blame-×₂ : ∀ {Γ A B} {M : Γ ⊢ A} {ℓ}
        ------------------------
      → cons {B = B} M (blame ℓ) —→ blame ℓ

    ξ-blame-fst : ∀ {Γ A B} {ℓ}
        ------------------
      → fst (blame {Γ = Γ} {A = A `× B} ℓ) —→ blame ℓ

    ξ-blame-snd : ∀ {Γ A B} {ℓ}
      → snd (blame {Γ = Γ} {A = A `× B} ℓ) —→ blame ℓ

    ξ-blame-inl : ∀ {Γ A B} {ℓ}
      → inl {B = B} (blame {Γ} {A} ℓ) —→ blame ℓ

    ξ-blame-inr : ∀ {Γ A B} {ℓ}
      → inr {A = A} (blame {Γ} {B} ℓ) —→ blame ℓ

    ξ-blame-case : ∀ {Γ A B C} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C} {ℓ}
      → case (blame ℓ) M N —→ blame ℓ

    ξ-blame-cast : ∀ {Γ A B} {c : Cast (A ⇒ B)} {ℓ}
      → (blame {Γ = Γ} {A = A} ℓ) ⟨ c ⟩ —→ blame ℓ

    β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
      → Value W
        --------------------
      → (ƛ N) · W —→ N [ W ]

    δ : ∀ {Γ : Context} {A B} {f : rep A → rep B} {k : rep A} {ab} {a} {b}
        ---------------------------------------------------
      → ($_ {Γ}{A ⇒ B} f {ab}) · (($ k){a}) —→ ($ (f k)){b}

    β-if-true :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
        -------------------------
      → if (($ true){f}) M N —→ M

    β-if-false :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
        --------------------------
      → if (($ false){f}) M N —→ N

    β-fst :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        --------------------
      → fst (cons V W) —→ V

    β-snd :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        --------------------
      → snd (cons V W) —→ W

    β-caseL : ∀ {Γ A B C} {V : Γ ⊢ A} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
      → Value V
        --------------------------
      → case (inl V) L M —→ L · V

    β-caseR : ∀ {Γ A B C} {V : Γ ⊢ B} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
      → Value V
        --------------------------
      → case (inr V) L M —→ M · V

    cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
      → (v : Value V) → {a : Active c}
        ------------------------------
      → V ⟨ c ⟩ —→ applyCast V v c {a}

    fun-cast : ∀ {Γ A' B' A₁ A₂} {V : Γ ⊢ A₁ ⇒ A₂} {W : Γ ⊢ A'}
        {c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))}
      → (v : Value V) → Value W → {x : Cross c}
        --------------------------------------------------
      → (V ⟨ c ⟩) · W —→ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩

    fst-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
        {c : Cast ((A `× B) ⇒ (A' `× B'))}
      → Value V → {x : Cross c}
        -------------------------------------
      → fst (V ⟨ c ⟩) —→ (fst V) ⟨ fstC c x ⟩

    snd-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
        {c : Cast ((A `× B) ⇒ (A' `× B'))}
      → Value V → {x : Cross c}
        -------------------------------------
      → snd (V ⟨ c ⟩) —→ (snd V) ⟨ sndC c x ⟩

    case-cast : ∀ {Γ A B A' B' C} {V : Γ ⊢ A `⊎ B}
        {W₁ : Γ ⊢ A' ⇒ C } {W₂ : Γ ⊢ B' ⇒ C}
        {c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))}
      → Value V → {x : Cross c}
        --------------------------------------------
      → case (V ⟨ c ⟩) W₁ W₂ —→
        case V (ƛ ((rename S_ W₁) · ((` Z) ⟨ inlC c x ⟩ )))
               (ƛ ((rename S_ W₂) · ((` Z) ⟨ inrC c x ⟩ )))

  infix  2 _—↠_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  data _—↠_ : ∀{Γ}{A} → Γ ⊢ A → Γ ⊢ A → Set where
    _∎ : ∀ {Γ}{A} (M : Γ ⊢ A)
        ---------
      → M —↠ M

    _—→⟨_⟩_ : ∀ {Γ}{A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
      → L —→ M
      → M —↠ N
        ---------
      → L —↠ N
