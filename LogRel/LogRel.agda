{-# OPTIONS --rewriting #-}
module LogRel.LogRel where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import InjProj.CastCalculus
open import InjProj.Precision
open import InjProj.CastDeterministic
open import InjProj.Reduction
open import StepIndexedLogic
open import EquivalenceRelation

{----------- Definition of Semantic Approximation -----------------------------}

data Dir : Set where
  ≼ : Dir
  ≽ : Dir

{- todo: change to Setᵒ -}
_⊨_⊑_for_ : Dir → Term → Term → ℕ → Set

≼ ⊨ M ⊑ M′ for k = (M ⇓ × M′ ⇓)
                    ⊎ (M′ —↠ blame)
                    ⊎ (∃[ N ] Σ[ r ∈ M —↠ N ] len r ≡ k)
                    
≽ ⊨ M ⊑ M′ for k = (M ⇓ × M′ ⇓)
                    ⊎ (M′ —↠ blame)
                    ⊎ (∃[ N′ ] Σ[ r ∈ M′ —↠ N′ ] len r ≡ k)

⊨_⊑_for_ : Term → Term → ℕ → Set
⊨ M ⊑ M′ for k = (≼ ⊨ M ⊑ M′ for k) × (≽ ⊨ M ⊑ M′ for k)

{----------- Semantic approximation implies the gradual guarantee -------------}

sem-approx⇒GG : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}
   → (∀ k → ⊨ M ⊑ M′ for k)
   → (M′ ⇓ → M ⇓)
   × (M′ ⇑ → M ⇑)
   × (M ⇓ → M′ ⇓ ⊎ M′ —↠ blame)
   × (M ⇑ → M′ ⇑⊎blame)
   × (M —↠ blame → M′ —↠ blame)
sem-approx⇒GG {A}{A′}{A⊑A′}{M}{M′} ⊨M⊑M′ =
  to-value-right , diverge-right , to-value-left , diverge-left , blame-blame
  where
  to-value-right : M′ ⇓ → M ⇓
  to-value-right (V′ , M′→V′ , v′)
      with proj₂ (⊨M⊑M′ (suc (len M′→V′)))
  ... | inj₁ ((V , M→V , v) , _) = V , M→V , v
  ... | inj₂ (inj₁ M′→blame) =
        ⊥-elim (cant-reduce-value-and-blame v′ M′→V′ M′→blame)
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) =
        ⊥-elim (step-value-plus-one M′→N′ M′→V′ v′ eq)
        
  diverge-right : M′ ⇑ → M ⇑
  diverge-right divM′ k
      with proj₁ (⊨M⊑M′ k)
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
        ⊥-elim (diverge-not-halt divM′ (inj₂ (V′ , M′→V′ , v′)))
  ... | inj₂ (inj₁ M′→blame) =
        ⊥-elim (diverge-not-halt divM′ (inj₁ M′→blame))
  ... | inj₂ (inj₂ (N , M→N , eq)) = N , M→N , sym eq

  to-value-left : M ⇓ → M′ ⇓ ⊎ M′ —↠ blame
  to-value-left (V , M→V , v)
      with proj₁ (⊨M⊑M′ (suc (len M→V)))
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) = inj₁ (V′ , M′→V′ , v′)
  ... | inj₂ (inj₁ M′→blame) = inj₂ M′→blame
  ... | inj₂ (inj₂ (N , M→N , eq)) =
        ⊥-elim (step-value-plus-one M→N M→V v eq)

  diverge-left : M ⇑ → M′ ⇑⊎blame
  diverge-left divM k 
      with proj₂ (⊨M⊑M′ k)
  ... | inj₁ ((V , M→V , v) , _) =
        ⊥-elim (diverge-not-halt divM (inj₂ (V , M→V , v)))
  ... | inj₂ (inj₁ M′→blame) = blame , (M′→blame , (inj₂ refl))
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) = N′ , (M′→N′ , (inj₁ (sym eq))) 

  blame-blame : (M —↠ blame → M′ —↠ blame)
  blame-blame M→blame
      with proj₁ (⊨M⊑M′ (suc (len M→blame)))
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
        ⊥-elim (cant-reduce-value-and-blame v M→V M→blame)
  ... | inj₂ (inj₁ M′→blame) = M′→blame
  ... | inj₂ (inj₂ (N , M→N , eq)) =
        ⊥-elim (step-blame-plus-one M→N M→blame eq)

{----------- Definition of the Logical Relation -------------------------------}

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

LR-type : Set
LR-type = (Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)

LR-ctx : Context
LR-ctx = LR-type ∷ []

_∣_ˢ⊑ᴸᴿₜ_⦂_ : Dir → Term → Term → ∀{A}{A′} (A⊑A′ : A ⊑ A′)
   → Setˢ LR-ctx (cons Now ∅)
dir ∣ M ˢ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = (inj₂ ((_ , _ , A⊑A′) , dir , M , M′)) ∈ zeroˢ

_∣_ˢ⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A}{A′} (A⊑A′ : A ⊑ A′)
   → Setˢ LR-ctx (cons Now ∅)
dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ = (inj₁ ((_ , _ , A⊑A′) , dir , V , V′)) ∈ zeroˢ

LRᵥ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)
LRᵥ (.★ , .★ , unk⊑unk) dir (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (dir ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ Refl⊑{gnd⇒ty G}))
... | no neq = ⊥ ˢ
LRᵥ (.★ , .★ , unk⊑unk) dir V V′ = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≼ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ ▷ˢ (≼ ∣ V ˢ⊑ᴸᴿᵥ V′ ⦂ d)
... | no neq = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≽ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (LRᵥ (gnd⇒ty G , A′ , d) ≽ V V′)
... | no neq = ⊥ ˢ
LRᵥ (★ , .A′ , unk⊑{H}{A′} d) dir V V′ = ⊥ ˢ
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir ($ c) ($ c′) = (c ≡ c′) ˢ
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir V V′ = ⊥ ˢ
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir (ƛ N)(ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (dir ∣ W ˢ⊑ᴸᴿᵥ W′ ⦂ A⊑A′)
                  →ˢ ▷ˢ (dir ∣ (N [ W ]) ˢ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′) 
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir V V′ = ⊥ ˢ

LRₜ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)
LRₜ (A , A′ , c) ≼ M M′ =
   (∃ˢ[ N ] (M —→ N)ˢ ×ˢ ▷ˢ (≼ ∣ N ˢ⊑ᴸᴿₜ M′ ⦂ c))
   ⊎ˢ (M′ —↠ blame)ˢ
   ⊎ˢ ((Value M)ˢ ×ˢ ((M′ —↠ blame)ˢ ⊎ˢ
                    (∃ˢ[ V′ ] (M′ —↠ V′)ˢ ×ˢ (Value V′)ˢ
                       ×ˢ (LRᵥ (_ , _ , c) ≼ M V′))))

LRₜ (A , A′ , c) ≽ M M′ =
   (∃ˢ[ N′ ] (M′ —→ N′)ˢ ×ˢ ▷ˢ (≽ ∣ M ˢ⊑ᴸᴿₜ N′ ⦂ c))
   ⊎ˢ (Blame M′)ˢ
   ⊎ˢ ((Value M′)ˢ ×ˢ (∃ˢ[ V ] (M —↠ V)ˢ ×ˢ (Value V)ˢ
                                ×ˢ (LRᵥ (_ , _ , c) ≽ V M′)))

pre-LRₜ⊎LRᵥ : LR-type → Setˢ LR-ctx (cons Later ∅)
pre-LRₜ⊎LRᵥ (inj₁ (c , dir , V , V′)) = LRᵥ c dir V V′
pre-LRₜ⊎LRᵥ (inj₂ (c , dir , M , M′)) = LRₜ c dir M M′

LRₜ⊎LRᵥ : LR-type → Setᵒ
LRₜ⊎LRᵥ X = μᵒ pre-LRₜ⊎LRᵥ X

_∣_⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ = LRₜ⊎LRᵥ (inj₁ ((_ , _ , A⊑A′) , dir , V , V′))

_∣_⊑ᴸᴿₜ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = LRₜ⊎LRᵥ (inj₂ ((_ , _ , A⊑A′) , dir , M , M′))

_⊑ᴸᴿₜ_⦂_ : Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = (≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) ×ᵒ (≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′)

LRₜ-def : ∀{A}{A′} → (A⊑A′ : A ⊑ A′) → Dir → Term → Term → Setᵒ
LRₜ-def A⊑A′ ≼ M M′ =
   (∃ᵒ[ N ] (M —→ N)ᵒ ×ᵒ ▷ᵒ (≼ ∣ N ⊑ᴸᴿₜ M′ ⦂ A⊑A′))
   ⊎ᵒ (M′ —↠ blame)ᵒ
   ⊎ᵒ ((Value M)ᵒ ×ᵒ ((M′ —↠ blame)ᵒ ⊎ᵒ
              (∃ᵒ[ V′ ] (M′ —↠ V′)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (≼ ∣ M ⊑ᴸᴿᵥ V′ ⦂ A⊑A′))))
LRₜ-def A⊑A′ ≽ M M′ =
   (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (≽ ∣ M ⊑ᴸᴿₜ N′ ⦂ A⊑A′))
   ⊎ᵒ (Blame M′)ᵒ
   ⊎ᵒ ((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ
                               ×ᵒ (≽ ∣ V ⊑ᴸᴿᵥ M′ ⦂ A⊑A′)))

LRₜ-stmt : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}
   → dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ ≡ᵒ LRₜ-def A⊑A′ dir M M′
LRₜ-stmt {A}{A′}{A⊑A′}{dir}{M}{M′} =
  dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′
                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-LRₜ⊎LRᵥ (X₂ dir)
                 ⩦⟨ fixpointᵒ pre-LRₜ⊎LRᵥ (X₂ dir) ⟩
  # (pre-LRₜ⊎LRᵥ (X₂ dir)) (LRₜ⊎LRᵥ , ttᵖ)
                 ⩦⟨ EQ{dir} ⟩
  LRₜ-def A⊑A′ dir M M′
  ∎
  where
  c = (A , A′ , A⊑A′)
  X₁ : Dir → LR-type
  X₁ = λ dir → inj₁ (c , dir , M , M′)
  X₂ = λ dir → inj₂ (c , dir , M , M′)
  EQ : ∀{dir} → # (pre-LRₜ⊎LRᵥ (X₂ dir)) (LRₜ⊎LRᵥ , ttᵖ) ≡ᵒ LRₜ-def A⊑A′ dir M M′
  EQ {≼} = cong-⊎ᵒ (≡ᵒ-refl refl)
           (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
             (cong-∃ λ V′ → cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
              ((≡ᵒ-sym (fixpointᵒ pre-LRₜ⊎LRᵥ (inj₁ (c , ≼ , M , V′))))))))))
  EQ {≽} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ λ V → cong-×ᵒ (≡ᵒ-refl refl)
              (cong-×ᵒ (≡ᵒ-refl refl)
               (≡ᵒ-sym (fixpointᵒ pre-LRₜ⊎LRᵥ (inj₁ (c , ≽ , V , M′))))))))

LRₜ-suc : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}{k}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k) ⇔ #(LRₜ-def A⊑A′ dir M M′) (suc k)
LRₜ-suc {A}{A′}{A⊑A′}{dir}{M}{M′}{k} =
   ≡ᵒ⇒⇔{k = suc k} (LRₜ-stmt{A}{A′}{A⊑A′}{dir}{M}{M′})

{----------- Relate Open Terms ------------------------------------------------}

𝓖⟦_⟧ : (Γ : List Prec) → Dir → Subst → Subst → List Setᵒ
𝓖⟦ [] ⟧ dir σ σ′ = []
𝓖⟦ (_ , _ , A⊑A′) ∷ Γ ⟧ dir σ σ′ = (dir ∣ (σ 0) ⊑ᴸᴿᵥ (σ′ 0) ⦂ A⊑A′)
                     ∷ 𝓖⟦ Γ ⟧ dir (λ x → σ (suc x)) (λ x → σ′ (suc x))

_∣_⊨_⊑_⦂_ : List Prec → Dir → Term → Term → Prec → Set
Γ ∣ dir ⊨ M ⊑ M′ ⦂ (_ , _ , A⊑A′) = ∀ (γ γ′ : Subst)
   → 𝓖⟦ Γ ⟧ dir γ γ′ ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′) ⦂ A⊑A′

_⊨_⊑_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ M′ ⦂ c = (Γ ∣ ≼ ⊨ M ⊑ M′ ⦂ c) × (Γ ∣ ≽ ⊨ M ⊑ M′ ⦂ c)

proj : ∀ {Γ}{c}
  → (dir : Dir)
  → (M M′ : Term)
  → Γ ⊨ M ⊑ M′ ⦂ c
  → Γ ∣ dir ⊨ M ⊑ M′ ⦂ c
proj {Γ} {c} ≼ M M′ M⊑M′ = proj₁ M⊑M′
proj {Γ} {c} ≽ M M′ M⊑M′ = proj₂ M⊑M′

{----------- Logical Relation implies Semantic Approximation ------------------}

LR⇒sem-approx : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}{k}{dir}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k)
  → dir ⊨ M ⊑ M′ for k
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {zero} {≼} M⊑M′sk =
    inj₂ (inj₂ (M , (M END) , refl))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {suc k} {≼} M⊑M′sk
    with ⇔-to (LRₜ-suc{dir = ≼}) M⊑M′sk
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (m , inj₁ M′→blame)) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (m , inj₂ (V′ , M′→V′ , v′ , 𝒱≼V′M))) =
      inj₁ ((M , (M END) , m) , (V′ , M′→V′ , v′))
... | inj₁ (N , M→N , ▷N⊑M′)
    with LR⇒sem-approx{dir = ≼} ▷N⊑M′
... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
      inj₁ ((V , (M —→⟨ M→N ⟩ M→V) , v) , (V′ , M′→V′ , v′))
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (L , N→L , eq)) =
      inj₂ (inj₂ (L , (M —→⟨ M→N ⟩ N→L) , cong suc eq))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {zero} {≽} M⊑M′sk =
    inj₂ (inj₂ (M′ , (M′ END) , refl))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {suc k} {≽} M⊑M′sk
    with ⇔-to (LRₜ-suc{dir = ≽}) M⊑M′sk
... | inj₂ (inj₁ isBlame) =
      inj₂ (inj₁ (blame END))
... | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱≽VM′)) =
      inj₁ ((V , M→V , v) , M′ , (M′ END) , m′)
... | inj₁ (N′ , M′→N′ , ▷M⊑N′)
    with LR⇒sem-approx{dir = ≽} ▷M⊑N′
... | inj₁ ((V , M→V , v) , (V′ , N′→V′ , v′)) =
      inj₁ ((V , M→V , v) , V′ , (M′ —→⟨ M′→N′ ⟩ N′→V′) , v′)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′ —→⟨ M′→N′ ⟩ N′→blame))
... | inj₂ (inj₂ (L′ , N′→L′ , eq)) =
      inj₂ (inj₂ (L′ , (M′ —→⟨ M′→N′ ⟩ N′→L′) , cong suc eq))

{----------- Logical relation implies the gradual guarantee -------------------}

LR⇒GG : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}
   → [] ⊢ᵒ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′
   → (M′ ⇓ → M ⇓)
   × (M′ ⇑ → M ⇑)
   × (M ⇓ → M′ ⇓ ⊎ M′ —↠ blame)
   × (M ⇑ → M′ ⇑⊎blame)
   × (M —↠ blame → M′ —↠ blame)
LR⇒GG {A}{A′}{A⊑A′}{M}{M′} ⊨M⊑M′ =
  sem-approx⇒GG{A⊑A′ = A⊑A′} (λ k → ≼⊨M⊑M′ , ≽⊨M⊑M′)
  where
  ≼⊨M⊑M′ : ∀{k} → ≼ ⊨ M ⊑ M′ for k
  ≼⊨M⊑M′ {k} = LR⇒sem-approx {k = k}{dir = ≼}
                   (⊢ᵒ-elim (proj₁ᵒ ⊨M⊑M′) (suc k) tt) 
  ≽⊨M⊑M′ : ∀{k} → ≽ ⊨ M ⊑ M′ for k
  ≽⊨M⊑M′ {k} = LR⇒sem-approx {k = k}{dir = ≽}
                   (⊢ᵒ-elim (proj₂ᵒ ⊨M⊑M′) (suc k) tt)

{----------- LR preserved by anti-reduction (i.e. expansion) ------------------}

anti-reduction-≼-one : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≼ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i
  → (M→N : M —→ N)
    ------------------------
  → #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
anti-reduction-≼-one {c = c} {M} {N} {M′} {i} ℰ≼NM′i M→N = inj₁ (N , M→N , ℰ≼NM′i)

anti-reduction-≽-one : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≽ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M′→N′ : M′ —→ N′)
  → #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
anti-reduction-≽-one {c = c} {M} {M′}{N′} {i} ℰ≽MN′ M′→N′ =
  inj₁ (N′ , M′→N′ , ℰ≽MN′)

anti-reduction-≼-R-one : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≼ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M′→N′ : M′ —→ N′)
  → #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≼-R-one {c = c}{M}{M′}{N′}{zero} ℰMN′ M′→N′ = tz (≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c)
anti-reduction-≼-R-one {c = c}{M}{M′}{N′}{suc i} ℰMN′ M′→N′
    with ℰMN′
... | inj₁ (N , M→N , ▷ℰNN′) =
         let ℰNM′si = anti-reduction-≼-R-one ▷ℰNN′ M′→N′ in
         inj₁ (N , M→N , ℰNM′si)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (unit M′→N′ ++ N′→blame))
... | inj₂ (inj₂ (m , inj₁ N′→blame)) = inj₂ (inj₁ (unit M′→N′ ++ N′→blame))
... | inj₂ (inj₂ (m , inj₂ (V′ , N′→V′ , v′ , 𝒱MV′))) =
      inj₂ (inj₂ (m , inj₂ (V′ , (unit M′→N′ ++ N′→V′) , v′ , 𝒱MV′)))

anti-reduction-≼-R : ∀{A}{A′}{c : A ⊑ A′}{M}{M′}{N′}{i}
  → #(≼ ∣ M ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M′→N′ : M′ —↠ N′)
  → #(≼ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≼-R {M′ = M′} ℰMN′ (.M′ END) = ℰMN′
anti-reduction-≼-R {M′ = M′} {N′} {i} ℰMN′ (.M′ —→⟨ M′→L′ ⟩ L′→*N′) =
  anti-reduction-≼-R-one (anti-reduction-≼-R ℰMN′ L′→*N′) M′→L′

anti-reduction-≽-L-one : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≽ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i
  → (M→N : M —→ N)
  → #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≽-L-one {c = c}{M} {N}{M′} {zero} ℰNM′ M→N =
    tz (≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c)
anti-reduction-≽-L-one {M = M} {N}{M′}  {suc i} ℰNM′ M→N
    with ℰNM′
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      inj₁ (N′ , (M′→N′ , (anti-reduction-≽-L-one ▷ℰMN′ M→N)))
... | inj₂ (inj₁ isBlame) = inj₂ (inj₁ isBlame)
... | inj₂ (inj₂ (m′ , V , N→V , v , 𝒱VM′)) =
      inj₂ (inj₂ (m′ , V , (unit M→N ++ N→V) , v , 𝒱VM′))

anti-reduction-≽-L : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{i}
  → #(≽ ∣ N ⊑ᴸᴿₜ M′ ⦂ c) i
  → (M→N : M —↠ N)
  → #(≽ ∣ M ⊑ᴸᴿₜ M′ ⦂ c) i
anti-reduction-≽-L {c = c} {M} {.M} {N′} {i} ℰNM′ (.M END) = ℰNM′
anti-reduction-≽-L {c = c} {M} {M′} {N′} {i} ℰNM′ (.M —→⟨ M→L ⟩ L→*N) =
  anti-reduction-≽-L-one (anti-reduction-≽-L ℰNM′ L→*N) M→L

anti-reduction : ∀{A}{A′}{c : A ⊑ A′}{M}{N}{M′}{N′}{i}{dir}
  → #(dir ∣ N ⊑ᴸᴿₜ N′ ⦂ c) i
  → (M→N : M —→ N)
  → (M′→N′ : M′ —→ N′)
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ c) (suc i)
anti-reduction {c = c} {M} {N} {M′} {N′} {i} {≼} ℰNN′i M→N M′→N′ =
  let ℰMN′si = anti-reduction-≼-one ℰNN′i M→N in
  let ℰM′N′si = anti-reduction-≼-R-one ℰMN′si M′→N′ in
  ℰM′N′si
anti-reduction {c = c} {M} {N} {M′} {N′} {i} {≽} ℰNN′i M→N M′→N′ =
  let ℰM′Nsi = anti-reduction-≽-one ℰNN′i M′→N′ in
  let ℰM′N′si = anti-reduction-≽-L-one ℰM′Nsi M→N in
  ℰM′N′si

{------------- Related values are syntactic values ----------------------------}

LRᵥ⇒Value : ∀ {k}{dir}{A}{A′} (A⊑A′ : A ⊑ A′) M M′
   → # (dir ∣ M ⊑ᴸᴿᵥ M′ ⦂ A⊑A′) (suc k)
     ----------------------------
   → Value M × Value M′
LRᵥ⇒Value {k}{dir} unk⊑unk (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
LRᵥ⇒Value {k}{≼} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    with G ≡ᵍ H
... | yes refl
    with 𝒱VGV′
... | v , v′ , _ = (v 〈 _ 〉) , v′
LRᵥ⇒Value {k}{≽} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    with G ≡ᵍ H
... | yes refl
    with 𝒱VGV′
... | v , v′ , _ = (v 〈 _ 〉) , v′
LRᵥ⇒Value {k}{dir} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    | no neq = ⊥-elim 𝒱VGV′
LRᵥ⇒Value {k}{dir} (base⊑{ι}) ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
LRᵥ⇒Value {k}{dir} (fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱VV′ =
    (ƛ̬ N) , (ƛ̬ N′)

{--------- Equations, intro, and elim rules for 𝒱 ----------------------------}

LRᵥ-base : ∀{ι}{c}{c′}{dir}
   → dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c′) ⦂ base⊑{ι} ≡ᵒ (c ≡ c′) ᵒ
LRᵥ-base{ι}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

LRᵥ-base-intro-step : ∀{ι}{dir}{c}{k} → # (dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}) k
LRᵥ-base-intro-step {ι} {dir} {c} {zero} = tt
LRᵥ-base-intro-step {ι} {dir} {c} {suc k} = refl

LRᵥ-base-intro : ∀{𝒫}{ι}{c}{dir}
   → 𝒫 ⊢ᵒ dir ∣ ($ c) ⊑ᴸᴿᵥ ($ c) ⦂ base⊑{ι}
LRᵥ-base-intro{𝒫}{ι}{c}{dir} = ⊢ᵒ-intro λ k 𝒫k → LRᵥ-base-intro-step{ι}{dir}{c}{k}

LRᵥ-base-elim-step : ∀{ι}{ι′}{c : $ₜ ι ⊑ $ₜ ι′}{V}{V′}{dir}{k}
  → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) (suc k)
  → ∃[ c ] ι ≡ ι′ × V ≡ $ c × V′ ≡ $ c
LRᵥ-base-elim-step {ι} {.ι} {base⊑} {$ c} {$ c′} {dir} {k} refl =
  c , refl , refl , refl

LRᵥ-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}{dir}
   → (dir ∣ (ƛ N) ⊑ᴸᴿᵥ (ƛ N′) ⦂ fun⊑ A⊑A′ B⊑B′)
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ A⊑A′))
                →ᵒ (▷ᵒ (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′))))
LRᵥ-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′}{dir} =
   let X = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , dir , ƛ N , ƛ N′) in
   (dir ∣ (ƛ N) ⊑ᴸᴿᵥ (ƛ N′) ⦂ fun⊑ A⊑A′ B⊑B′)  ⩦⟨ ≡ᵒ-refl refl ⟩
   LRₜ⊎LRᵥ X                                       ⩦⟨ fixpointᵒ pre-LRₜ⊎LRᵥ X ⟩
   # (pre-LRₜ⊎LRᵥ X) (LRₜ⊎LRᵥ , ttᵖ)                          ⩦⟨ ≡ᵒ-refl refl ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ A⊑A′))
                   →ᵒ (▷ᵒ (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ B⊑B′)))) ∎

LRᵥ-fun-elim-step : ∀{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{dir}{k}{j}
  → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ fun⊑ c d) (suc k)
  → j ≤ k
  → ∃[ N ] ∃[ N′ ] V ≡ ƛ N × V′ ≡ ƛ N′ 
      × (∀{W W′} → # (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c) j
                 → # (dir ∣ (N [ W ]) ⊑ᴸᴿₜ (N′ [ W′ ]) ⦂ d) j)
LRᵥ-fun-elim-step {A}{B}{A′}{B′}{c}{d}{ƛ N}{ƛ N′}{dir}{k}{j} 𝒱VV′ j≤k =
  N , N′ , refl , refl , λ {W}{W′} 𝒱WW′ →
    let 𝒱λNλN′sj = down (dir ∣ (ƛ N) ⊑ᴸᴿᵥ (ƛ N′) ⦂ fun⊑ c d)
                        (suc k) 𝒱VV′ (suc j) (s≤s j≤k) in
    let ℰNWN′W′j = 𝒱λNλN′sj W W′ (suc j) ≤-refl 𝒱WW′ in
    ℰNWN′W′j

LRᵥ-dyn-any-elim-step-≽ : ∀{V}{V′}{k}{H}{A′}{c : gnd⇒ty H ⊑ A′}
   → #(≽ ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) (suc k)
   → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
             × #(≽ ∣ V₁ ⊑ᴸᴿᵥ V′ ⦂ c) (suc k)
LRᵥ-dyn-any-elim-step-≽ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VGV′
... | yes refl
    with 𝒱VGV′
... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′

LRᵥ-dyn-any-elim-step-≼ : ∀{V}{V′}{k}{H}{A′}{c : gnd⇒ty H ⊑ A′}
   → #(≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) (suc k)
   → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
             × #(≼ ∣ V₁ ⊑ᴸᴿᵥ V′ ⦂ c) k
LRᵥ-dyn-any-elim-step-≼ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VGV′
... | yes refl
    with 𝒱VGV′
... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′

LRᵥ-dyn-R-step-≽ : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}
   → #(≽ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≽ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
LRᵥ-dyn-R-step-≽ {G} {c} {V} {V′} {zero} 𝒱VV′ =
     tz (≽ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk)
LRᵥ-dyn-R-step-≽ {G} {c} {V} {V′} {suc k} 𝒱VV′
    with unk⊑gnd-inv c
... | d , refl
    with LRᵥ-dyn-any-elim-step-≽ {V}{V′}{k}{G}{_}{d} 𝒱VV′
... | V₁ , refl , v₁ , v′ , 𝒱V₁V′
    with G ≡ᵍ G
... | no neq = ⊥-elim 𝒱VV′
... | yes refl
    with gnd-prec-unique d Refl⊑
... | refl =
    let 𝒱V₁V′k = down (≽ ∣ V₁ ⊑ᴸᴿᵥ V′ ⦂ d) (suc k) 𝒱V₁V′ k (n≤1+n k) in
    v₁ , v′ , 𝒱V₁V′k

LRᵥ-dyn-R-step-≼ : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}
   → #(≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(≼ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
LRᵥ-dyn-R-step-≼ {G} {c} {V} {V′} {zero} 𝒱VV′ =
     tz (≼ ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk)
LRᵥ-dyn-R-step-≼ {G} {c} {V} {V′} {suc k} 𝒱VV′
    with unk⊑gnd-inv c
... | d , refl
    with LRᵥ-dyn-any-elim-step-≼ {V}{V′}{k}{G}{_}{d} 𝒱VV′
... | V₁ , refl , v₁ , v′ , 𝒱V₁V′
    with G ≡ᵍ G
... | no neq = ⊥-elim 𝒱VV′
... | yes refl
    with gnd-prec-unique d Refl⊑
... | refl = v₁ , v′ , 𝒱V₁V′           {- No use of down! -}

LRᵥ-dyn-R-step : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}{dir}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(dir ∣ V ⊑ᴸᴿᵥ (V′ ⟨ G !⟩) ⦂ unk⊑unk) k
LRᵥ-dyn-R-step {G} {c} {V} {V′} {k} {≼} 𝒱VV′ =
    LRᵥ-dyn-R-step-≼{G} {c} {V} {V′} {k} 𝒱VV′ 
LRᵥ-dyn-R-step {G} {c} {V} {V′} {k} {≽} 𝒱VV′ =
   LRᵥ-dyn-R-step-≽{G} {c} {V} {V′} {k} 𝒱VV′

LRᵥ-dyn-L-step : ∀{G}{A′}{c : gnd⇒ty G ⊑ A′}{V}{V′}{dir}{k}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) k
   → #(dir ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) k
LRᵥ-dyn-L-step {G}{A′}{c}{V}{V′}{dir}{zero} 𝒱VV′k =
    tz (dir ∣ (V ⟨ G !⟩) ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c)
LRᵥ-dyn-L-step {G} {A′} {c} {V} {V′} {≼} {suc k} 𝒱VV′sk
    with G ≡ᵍ G
... | no neq = ⊥-elim (neq refl)
... | yes refl =
    let (v , v′) = LRᵥ⇒Value c V V′ 𝒱VV′sk in
    let 𝒱VV′k = down (≼ ∣ V ⊑ᴸᴿᵥ V′ ⦂ c) (suc k) 𝒱VV′sk k (n≤1+n k) in
    v , v′ , 𝒱VV′k
LRᵥ-dyn-L-step {G} {A′} {c} {V} {V′} {≽} {suc k} 𝒱VV′k
    with G ≡ᵍ G
... | no neq = ⊥-elim (neq refl)
... | yes refl =
      let (v , v′) = LRᵥ⇒Value c V V′ 𝒱VV′k in
      v , v′ , 𝒱VV′k                  {- No use of down! -}

{--------------- Related values are related expressions -----------------------}

LRᵥ⇒LRₜ-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{V V′}{dir}{k}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′) k
     ---------------------------
   → #(dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′) k
LRᵥ⇒LRₜ-step {A}{A′}{A⊑A′}{V} {V′} {dir} {zero} 𝒱VV′k =
   tz (dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′)
LRᵥ⇒LRₜ-step {A}{A′}{A⊑A′}{V} {V′} {≼} {suc k} 𝒱VV′sk =
  ⇔-fro (LRₜ-suc{dir = ≼})
  (let (v , v′) = LRᵥ⇒Value A⊑A′ V V′ 𝒱VV′sk in
  (inj₂ (inj₂ (v , inj₂ (V′ , (V′ END) , v′ , 𝒱VV′sk)))))
LRᵥ⇒LRₜ-step {A}{A′}{A⊑A′}{V} {V′} {≽} {suc k} 𝒱VV′sk =
  ⇔-fro (LRₜ-suc{dir = ≽})
  (let (v , v′) = LRᵥ⇒Value A⊑A′ V V′ 𝒱VV′sk in
  inj₂ (inj₂ (v′ , V , (V END) , v , 𝒱VV′sk)))

LRᵥ⇒LRₜ : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{𝒫}{V V′}{dir}
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′
     ---------------------------
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′
LRᵥ⇒LRₜ {A}{A′}{A⊑A′}{𝒫}{V}{V′}{dir} ⊢𝒱VV′ = ⊢ᵒ-intro λ k 𝒫k →
  LRᵥ⇒LRₜ-step{V = V}{V′}{dir}{k} (⊢ᵒ-elim ⊢𝒱VV′ k 𝒫k)

{--------------- Blame on the right -------------------------------------------}

LRₜ-blame-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{k}
   → #(dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′) k
LRₜ-blame-step {A}{A′}{A⊑A′}{dir} {M} {zero} = tz (dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′)
LRₜ-blame-step {A}{A′}{A⊑A′}{≼} {M} {suc k} = inj₂ (inj₁ (blame END))
LRₜ-blame-step {A}{A′}{A⊑A′}{≽} {M} {suc k} = inj₂ (inj₁ isBlame)

LRₜ-blame : ∀{𝒫}{A}{A′}{A⊑A′ : A ⊑ A′}{M}{dir}
   → 𝒫 ⊢ᵒ dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′
LRₜ-blame {𝒫}{A}{A′}{A⊑A′}{M}{dir} = ⊢ᵒ-intro λ n x → LRₜ-blame-step{dir = dir}
