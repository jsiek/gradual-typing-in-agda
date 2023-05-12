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
  ≺ : Dir
  ≻ : Dir

_⊨_⊑_for_ : Dir → Term → Term → ℕ → Set

≺ ⊨ M ⊑ M′ for k = (ToVal M × ToVal M′)
                    ⊎ (M′ —↠ blame)
                    ⊎ (∃[ N ] Σ[ r ∈ M —↠ N ] len r ≡ k)
                    
≻ ⊨ M ⊑ M′ for k = (ToVal M × ToVal M′)
                    ⊎ (M′ —↠ blame)
                    ⊎ (∃[ N′ ] Σ[ r ∈ M′ —↠ N′ ] len r ≡ k)

{----------- Definition of the Logical Relation -------------------------------}

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

LR-type : Set
LR-type = (Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)

LR-ctx : Context
LR-ctx = LR-type ∷ []

{- todo: rename to use ˢ⊑ᴸᴿₜ -}
LRˢₜ⟦_⟧ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Now ∅)
LRˢₜ⟦ A⊑B ⟧ dir M M′ = (inj₂ (A⊑B , dir , M , M′)) ∈ zeroˢ

{- todo: rename to use ˢ⊑ᴸᴿᵥ -}
LRˢᵥ⟦_⟧ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Now ∅)
LRˢᵥ⟦ A⊑B ⟧ dir V V′ = (inj₁ (A⊑B , dir , V , V′)) ∈ zeroˢ

LRᵥ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)
LRᵥ (.★ , .★ , unk⊑unk) dir (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = let g = gnd⇒ty G in
                 (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (LRˢᵥ⟦ (g , g , Refl⊑) ⟧ dir V V′))
... | no neq = ⊥ ˢ
LRᵥ (.★ , .★ , unk⊑unk) dir V V′ = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≺ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ ▷ˢ (LRˢᵥ⟦ gnd⇒ty G , A′ , d ⟧ ≺ V V′)
... | no neq = ⊥ ˢ
LRᵥ (.★ , .A′ , unk⊑{H}{A′} d) ≻ (V ⟨ G !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (LRᵥ (gnd⇒ty G , A′ , d) ≻ V V′)
... | no neq = ⊥ ˢ
LRᵥ (★ , .A′ , unk⊑{H}{A′} d) dir V V′ = ⊥ ˢ
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir ($ c) ($ c′) = (c ≡ c′) ˢ
LRᵥ (.($ₜ ι) , .($ₜ ι) , base⊑{ι}) dir V V′ = ⊥ ˢ
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir (ƛ N)(ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (LRˢᵥ⟦ (A , A′ , A⊑A′) ⟧ dir W W′)
                  →ˢ ▷ˢ (LRˢₜ⟦ (B , B′ , B⊑B′) ⟧ dir (N [ W ]) (N′ [ W′ ])) 
LRᵥ (.(A ⇒ B) , .(A′ ⇒ B′) , fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) dir V V′ = ⊥ ˢ

LRₜ : Prec → Dir → Term → Term → Setˢ LR-ctx (cons Later ∅)
LRₜ c ≺ M M′ =
   (∃ˢ[ N ] (M —→ N)ˢ ×ˢ ▷ˢ (LRˢₜ⟦ c ⟧ ≺ N M′))
   ⊎ˢ (M′ —↠ blame)ˢ
   ⊎ˢ ((Value M)ˢ ×ˢ ((M′ —↠ blame)ˢ ⊎ˢ
                    (∃ˢ[ V′ ] (M′ —↠ V′)ˢ ×ˢ (Value V′)ˢ ×ˢ (LRᵥ c ≺ M V′))))

LRₜ c ≻ M M′ =
   (∃ˢ[ N′ ] (M′ —→ N′)ˢ ×ˢ ▷ˢ (LRˢₜ⟦ c ⟧ ≻ M N′))
   ⊎ˢ (Blame M′)ˢ
   ⊎ˢ ((Value M′)ˢ ×ˢ (∃ˢ[ V ] (M —↠ V)ˢ ×ˢ (Value V)ˢ ×ˢ (LRᵥ c ≻ V M′)))

LRₜ⊎LRᵥ : LR-type → Setˢ LR-ctx (cons Later ∅)
LRₜ⊎LRᵥ (inj₁ (c , dir , V , V′)) = LRᵥ c dir V V′
LRₜ⊎LRᵥ (inj₂ (c , dir , M , M′)) = LRₜ c dir M M′

ℰ⊎𝒱 : LR-type → Setᵒ
ℰ⊎𝒱 X = μᵒ LRₜ⊎LRᵥ X

𝒱⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
𝒱⟦ c ⟧ dir V V′ = ℰ⊎𝒱 (inj₁ (c , dir , V , V′))

_∣_⊑ᴸᴿᵥ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′ = ℰ⊎𝒱 (inj₁ ((_ , _ , A⊑A′) , dir , V , V′))

ℰ⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
ℰ⟦ c ⟧ dir M M′ = ℰ⊎𝒱 (inj₂ (c , dir , M , M′))

_∣_⊑ᴸᴿₜ_⦂_ : Dir → Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = ℰ⊎𝒱 (inj₂ ((_ , _ , A⊑A′) , dir , M , M′))

_⊑ᴸᴿₜ_⦂_ : Term → Term → ∀{A A′} → A ⊑ A′ → Setᵒ
M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ = (≺ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) ×ᵒ (≻ ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′)

LRₜ-def : ∀{A}{A′} → (A⊑A′ : A ⊑ A′) → Dir → Term → Term → Setᵒ
LRₜ-def A⊑A′ ≺ M M′ =
   (∃ᵒ[ N ] (M —→ N)ᵒ ×ᵒ ▷ᵒ (≺ ∣ N ⊑ᴸᴿₜ M′ ⦂ A⊑A′))
   ⊎ᵒ (M′ —↠ blame)ᵒ
   ⊎ᵒ ((Value M)ᵒ ×ᵒ ((M′ —↠ blame)ᵒ ⊎ᵒ
              (∃ᵒ[ V′ ] (M′ —↠ V′)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (≺ ∣ M ⊑ᴸᴿᵥ V′ ⦂ A⊑A′))))
LRₜ-def A⊑A′ ≻ M M′ =
   (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (≻ ∣ M ⊑ᴸᴿₜ N′ ⦂ A⊑A′))
   ⊎ᵒ (Blame M′)ᵒ
   ⊎ᵒ ((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ
                               ×ᵒ (≻ ∣ V ⊑ᴸᴿᵥ M′ ⦂ A⊑A′)))

LRₜ-stmt : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}
   → dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′ ≡ᵒ LRₜ-def A⊑A′ dir M M′
LRₜ-stmt {A}{A′}{A⊑A′}{dir}{M}{M′} =
  dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′
                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ LRₜ⊎LRᵥ (X₂ dir)
                 ⩦⟨ fixpointᵒ LRₜ⊎LRᵥ (X₂ dir) ⟩
  # (LRₜ⊎LRᵥ (X₂ dir)) (ℰ⊎𝒱 , ttᵖ)
                 ⩦⟨ EQ{dir} ⟩
  LRₜ-def A⊑A′ dir M M′
  ∎
  where
  c = (A , A′ , A⊑A′)
  X₁ : Dir → LR-type
  X₁ = λ dir → inj₁ (c , dir , M , M′)
  X₂ = λ dir → inj₂ (c , dir , M , M′)
  EQ : ∀{dir} → # (LRₜ⊎LRᵥ (X₂ dir)) (ℰ⊎𝒱 , ttᵖ) ≡ᵒ LRₜ-def A⊑A′ dir M M′
  EQ {≺} = cong-⊎ᵒ (≡ᵒ-refl refl)
           (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
             (cong-∃ λ V′ → cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
              ((≡ᵒ-sym (fixpointᵒ LRₜ⊎LRᵥ (inj₁ (c , ≺ , M , V′))))))))))
  EQ {≻} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ λ V → cong-×ᵒ (≡ᵒ-refl refl)
              (cong-×ᵒ (≡ᵒ-refl refl)
               (≡ᵒ-sym (fixpointᵒ LRₜ⊎LRᵥ (inj₁ (c , ≻ , V , M′))))))))

LRₜ-suc : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{M′}{k}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k) ⇔ #(LRₜ-def A⊑A′ dir M M′) (suc k)
LRₜ-suc {A}{A′}{A⊑A′}{dir}{M}{M′}{k} =
   ≡ᵒ⇒⇔{k = suc k} (LRₜ-stmt{A}{A′}{A⊑A′}{dir}{M}{M′})

{----------- Relate Open Terms ------------------------------------------------}

𝓖⟦_⟧ : (Γ : List Prec) → Dir → Subst → Subst → List Setᵒ
𝓖⟦ [] ⟧ dir σ σ′ = []
𝓖⟦ c ∷ Γ ⟧ dir σ σ′ = (𝒱⟦ c ⟧ dir (σ 0) (σ′ 0))
                     ∷ 𝓖⟦ Γ ⟧ dir (λ x → σ (suc x)) (λ x → σ′ (suc x))

_∣_⊨_⊑_⦂_ : List Prec → Dir → Term → Term → Prec → Set
Γ ∣ dir ⊨ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst)
   → 𝓖⟦ Γ ⟧ dir γ γ′ ⊢ᵒ ℰ⟦ c ⟧ dir (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

_⊨_⊑_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ M′ ⦂ c = (Γ ∣ ≺ ⊨ M ⊑ M′ ⦂ c) × (Γ ∣ ≻ ⊨ M ⊑ M′ ⦂ c)

proj : ∀ {Γ}{c}
  → (dir : Dir)
  → (M M′ : Term)
  → Γ ⊨ M ⊑ M′ ⦂ c
  → Γ ∣ dir ⊨ M ⊑ M′ ⦂ c
proj {Γ} {c} ≺ M M′ M⊑M′ = proj₁ M⊑M′
proj {Γ} {c} ≻ M M′ M⊑M′ = proj₂ M⊑M′

{----------- Logical Relation implies Semantic Approximation ------------------}

LR⇒sem-approx : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}{k}{dir}
  → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′) (suc k)
  → dir ⊨ M ⊑ M′ for k
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {zero} {≺} M⊑M′sk =
    inj₂ (inj₂ (M , (M END) , refl))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {suc k} {≺} M⊑M′sk
    with ⇔-to (LRₜ-suc{dir = ≺}) M⊑M′sk
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (m , inj₁ M′→blame)) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (m , inj₂ (V′ , M′→V′ , v′ , 𝒱≺V′M))) =
      inj₁ ((M , (M END) , m) , (V′ , M′→V′ , v′))
... | inj₁ (N , M→N , ▷N⊑M′)
    with LR⇒sem-approx{dir = ≺} ▷N⊑M′
... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
      inj₁ ((V , (M —→⟨ M→N ⟩ M→V) , v) , (V′ , M′→V′ , v′))
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (L , N→L , eq)) =
      inj₂ (inj₂ (L , (M —→⟨ M→N ⟩ N→L) , cong suc eq))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {zero} {≻} M⊑M′sk =
    inj₂ (inj₂ (M′ , (M′ END) , refl))
LR⇒sem-approx {A} {A′} {A⊑A′} {M} {M′} {suc k} {≻} M⊑M′sk
    with ⇔-to (LRₜ-suc{dir = ≻}) M⊑M′sk
... | inj₂ (inj₁ isBlame) =
      inj₂ (inj₁ (blame END))
... | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱≻VM′)) =
      inj₁ ((V , M→V , v) , M′ , (M′ END) , m′)
... | inj₁ (N′ , M′→N′ , ▷M⊑N′)
    with LR⇒sem-approx{dir = ≻} ▷M⊑N′
... | inj₁ ((V , M→V , v) , (V′ , N′→V′ , v′)) =
      inj₁ ((V , M→V , v) , V′ , (M′ —→⟨ M′→N′ ⟩ N′→V′) , v′)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′ —→⟨ M′→N′ ⟩ N′→blame))
... | inj₂ (inj₂ (L′ , N′→L′ , eq)) =
      inj₂ (inj₂ (L′ , (M′ —→⟨ M′→N′ ⟩ N′→L′) , cong suc eq))

{----------- Logical relation implies the gradual guarantee -------------------}

LR⇒GG : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}
   → [] ⊢ᵒ M ⊑ᴸᴿₜ M′ ⦂ A⊑A′
   → (ToVal M′ → ToVal M)
   × (diverge M′ → diverge M)
   × (ToVal M → ToVal M′ ⊎ M′ —↠ blame)
   × (diverge M → diverge⊎blame M′)
LR⇒GG {A}{A′}{A⊑A′}{M}{M′} ⊨M⊑M′ =
  to-value-right , diverge-right , to-value-left , diverge-left
  where
  to-value-right : ToVal M′ → ToVal M
  to-value-right (V′ , M′→V′ , v′)
      with LR⇒sem-approx {k = suc (len M′→V′)}{dir = ≻}
                    (⊢ᵒ-elim (proj₂ᵒ ⊨M⊑M′) (suc (suc (len M′→V′))) tt)
  ... | inj₁ ((V , M→V , v) , _) = V , M→V , v
  ... | inj₂ (inj₁ M′→blame) =
        ⊥-elim (cant-reduce-value-and-blame v′ M′→V′ M′→blame)
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) =
        ⊥-elim (step-value-plus-one M′→N′ M′→V′ v′ eq)

  diverge-right : diverge M′ → diverge M
  diverge-right divM′ k
      with LR⇒sem-approx {k = k}{dir = ≺} (⊢ᵒ-elim (proj₁ᵒ ⊨M⊑M′) (suc k) tt)
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) =
        ⊥-elim (diverge-not-halt divM′ (inj₂ (V′ , M′→V′ , v′)))
  ... | inj₂ (inj₁ M′→blame) =
        ⊥-elim (diverge-not-halt divM′ (inj₁ M′→blame))
  ... | inj₂ (inj₂ (N , M→N , eq)) = N , M→N , sym eq

  to-value-left : ToVal M → ToVal M′ ⊎ M′ —↠ blame
  to-value-left (V , M→V , v)
      with LR⇒sem-approx{k = suc (len M→V)}{dir =  ≺}
                        (⊢ᵒ-elim (proj₁ᵒ ⊨M⊑M′) (suc (suc (len M→V))) tt)
  ... | inj₁ ((V , M→V , v) , (V′ , M′→V′ , v′)) = inj₁ (V′ , M′→V′ , v′)
  ... | inj₂ (inj₁ M′→blame) = inj₂ M′→blame
  ... | inj₂ (inj₂ (N , M→N , eq)) =
        ⊥-elim (step-value-plus-one M→N M→V v eq)

  diverge-left : diverge M → diverge⊎blame M′
  diverge-left divM k 
      with LR⇒sem-approx {k = k}{dir = ≻} (⊢ᵒ-elim (proj₂ᵒ ⊨M⊑M′) (suc k) tt)
  ... | inj₁ ((V , M→V , v) , _) =
        ⊥-elim (diverge-not-halt divM (inj₂ (V , M→V , v)))
  ... | inj₂ (inj₁ M′→blame) = blame , (M′→blame , (inj₂ refl))
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) = N′ , (M′→N′ , (inj₁ (sym eq))) 

{----------- LR preserved by anti-reduction (i.e. expansion) ------------------}

anti-reduction-≺-one : ∀{c}{M}{N}{M′}{i}
  → #(ℰ⟦ c ⟧ ≺ N M′) i
  → (M→N : M —→ N)
    ------------------------
  → #(ℰ⟦ c ⟧ ≺ M M′) (suc i)
anti-reduction-≺-one {c} {M} {N} {M′} {i} ℰ≺NM′i M→N = inj₁ (N , M→N , ℰ≺NM′i)

anti-reduction-≻-one : ∀{c}{M}{M′}{N′}{i}
  → #(ℰ⟦ c ⟧ ≻ M N′) i
  → (M′→N′ : M′ —→ N′)
  → #(ℰ⟦ c ⟧ ≻ M M′) (suc i)
anti-reduction-≻-one {c} {M} {M′}{N′} {i} ℰ≻MN′ M′→N′ =
  inj₁ (N′ , M′→N′ , ℰ≻MN′)

anti-reduction-≺-R-one : ∀{c}{M}{M′}{N′}{i}
  → #(ℰ⟦ c ⟧ ≺ M N′) i
  → (M′→N′ : M′ —→ N′)
  → #(ℰ⟦ c ⟧ ≺ M M′) i
anti-reduction-≺-R-one {c}{M}{M′}{N′}{zero} ℰMN′ M′→N′ = tz (ℰ⟦ c ⟧ ≺ M M′)
anti-reduction-≺-R-one {c}{M}{M′}{N′}{suc i} ℰMN′ M′→N′
    with ℰMN′
... | inj₁ (N , M→N , ▷ℰNN′) =
         let ℰNM′si = anti-reduction-≺-R-one ▷ℰNN′ M′→N′ in
         inj₁ (N , M→N , ℰNM′si)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (unit M′→N′ ++ N′→blame))
... | inj₂ (inj₂ (m , inj₁ N′→blame)) = inj₂ (inj₁ (unit M′→N′ ++ N′→blame))
... | inj₂ (inj₂ (m , inj₂ (V′ , N′→V′ , v′ , 𝒱MV′))) =
      inj₂ (inj₂ (m , inj₂ (V′ , (unit M′→N′ ++ N′→V′) , v′ , 𝒱MV′)))

anti-reduction-≺-R : ∀{c}{M}{M′}{N′}{i}
  → #(ℰ⟦ c ⟧ ≺ M N′) i
  → (M′→N′ : M′ —↠ N′)
  → #(ℰ⟦ c ⟧ ≺ M M′) i
anti-reduction-≺-R {c} {M} {M′} {.M′} {i} ℰMN′ (.M′ END) = ℰMN′
anti-reduction-≺-R {c} {M} {M′} {N′} {i} ℰMN′ (.M′ —→⟨ M′→L′ ⟩ L′→*N′) =
  anti-reduction-≺-R-one (anti-reduction-≺-R ℰMN′ L′→*N′) M′→L′

anti-reduction-≻-L-one : ∀{c}{M}{N}{M′}{i}
  → #(ℰ⟦ c ⟧ ≻ N M′) i
  → (M→N : M —→ N)
  → #(ℰ⟦ c ⟧ ≻ M M′) i
anti-reduction-≻-L-one {c} {M} {M′} {N′} {zero} ℰNM′ M→N = tz (ℰ⟦ c ⟧ ≻ M N′)
anti-reduction-≻-L-one {c} {M} {N}{M′}  {suc i} ℰNM′ M→N
    with ℰNM′
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      inj₁ (N′ , (M′→N′ , (anti-reduction-≻-L-one ▷ℰMN′ M→N)))
... | inj₂ (inj₁ isBlame) = inj₂ (inj₁ isBlame)
... | inj₂ (inj₂ (m′ , V , N→V , v , 𝒱VM′)) =
      inj₂ (inj₂ (m′ , V , (unit M→N ++ N→V) , v , 𝒱VM′))

anti-reduction-≻-L : ∀{c}{M}{N}{M′}{i}
  → #(ℰ⟦ c ⟧ ≻ N M′) i
  → (M→N : M —↠ N)
  → #(ℰ⟦ c ⟧ ≻ M M′) i
anti-reduction-≻-L {c} {M} {.M} {N′} {i} ℰNM′ (.M END) = ℰNM′
anti-reduction-≻-L {c} {M} {M′} {N′} {i} ℰNM′ (.M —→⟨ M→L ⟩ L→*N) =
  anti-reduction-≻-L-one (anti-reduction-≻-L ℰNM′ L→*N) M→L

anti-reduction : ∀{c}{M}{N}{M′}{N′}{i}{dir}
  → #(ℰ⟦ c ⟧ dir N N′) i
  → (M→N : M —→ N)
  → (M′→N′ : M′ —→ N′)
  → #(ℰ⟦ c ⟧ dir M M′) (suc i)
anti-reduction {c} {M} {N} {M′} {N′} {i} {≺} ℰNN′i M→N M′→N′ =
  let ℰMN′si = anti-reduction-≺-one ℰNN′i M→N in
  let ℰM′N′si = anti-reduction-≺-R-one ℰMN′si M′→N′ in
  ℰM′N′si
anti-reduction {c} {M} {N} {M′} {N′} {i} {≻} ℰNN′i M→N M′→N′ =
  let ℰM′Nsi = anti-reduction-≻-one ℰNN′i M′→N′ in
  let ℰM′N′si = anti-reduction-≻-L-one ℰM′Nsi M→N in
  ℰM′N′si

{------------- Related values are syntactic values ----------------------------}

𝒱⇒Value : ∀ {k}{dir}{A}{A′} (A⊑A′ : A ⊑ A′) M M′
   → # (dir ∣ M ⊑ᴸᴿᵥ M′ ⦂ A⊑A′) (suc k)
     ----------------------------
   → Value M × Value M′
𝒱⇒Value {k}{dir} unk⊑unk (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
𝒱⇒Value {k}{≺} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    with G ≡ᵍ H
... | yes refl
    with 𝒱VGV′
... | v , v′ , _ = (v 〈 _ 〉) , v′
𝒱⇒Value {k}{≻} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    with G ≡ᵍ H
... | yes refl
    with 𝒱VGV′
... | v , v′ , _ = (v 〈 _ 〉) , v′
𝒱⇒Value {k}{dir} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    | no neq = ⊥-elim 𝒱VGV′
𝒱⇒Value {k}{dir} (base⊑{ι}) ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
𝒱⇒Value {k}{dir} (fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱VV′ =
    (ƛ̬ N) , (ƛ̬ N′)

{--------- Equations, intro, and elim rules for 𝒱 ----------------------------}

𝒱-base : ∀{ι}{c}{c′}{dir}
   → 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ dir ($ c) ($ c′) ≡ᵒ (c ≡ c′) ᵒ
𝒱-base{ι}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

𝒱-base-intro-step : ∀{ι}{dir}{c}{k}
   → # (𝒱⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ dir ($ c) ($ c)) k
𝒱-base-intro-step {ι} {dir} {c} {zero} = tt
𝒱-base-intro-step {ι} {dir} {c} {suc k} = refl

𝒱-base-intro : ∀{𝒫}{ι}{c}{dir}
   → 𝒫 ⊢ᵒ 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ dir ($ c) ($ c)
𝒱-base-intro{𝒫}{ι}{c}{dir} = ⊢ᵒ-intro λ k 𝒫k → 𝒱-base-intro-step{ι}{dir}{c}{k}

𝒱-base-elim-step : ∀{ι}{ι′}{c}{V}{V′}{dir}{k}
  → #(𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ dir V V′) (suc k)
  → ∃[ c ] ι ≡ ι′ × V ≡ $ c × V′ ≡ $ c
𝒱-base-elim-step {ι} {.ι} {base⊑} {$ c} {$ c′} {dir} {k} refl =
  c , refl , refl , refl

𝒱-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}{dir}
   → (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ dir (ƛ N) (ƛ N′))
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (𝒱⟦ A , A′ , A⊑A′ ⟧ dir W W′))
                       →ᵒ (▷ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ dir (N [ W ]) (N′ [ W′ ])))))
𝒱-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′}{dir} =
   let X = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , dir , ƛ N , ƛ N′) in
   (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ dir (ƛ N) (ƛ N′))  ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                              ⩦⟨ fixpointᵒ LRₜ⊎LRᵥ X ⟩
   # (LRₜ⊎LRᵥ X) (ℰ⊎𝒱 , ttᵖ)                                 ⩦⟨ ≡ᵒ-refl refl ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (𝒱⟦ A , A′ , A⊑A′ ⟧ dir W W′))
                 →ᵒ (▷ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ dir (N [ W ]) (N′ [ W′ ]))))) ∎

𝒱-fun-elim-step : ∀{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{dir}{k}{j}
  → #(𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′) (suc k)
  → j ≤ k
  → ∃[ N ] ∃[ N′ ] V ≡ ƛ N × V′ ≡ ƛ N′ 
      × (∀{W W′} → # (𝒱⟦ A , A′ , c ⟧ dir W W′) j
                 → # (ℰ⟦ B , B′ , d ⟧ dir (N [ W ]) (N′ [ W′ ])) j)
𝒱-fun-elim-step {A}{B}{A′}{B′}{c}{d}{ƛ N}{ƛ N′}{dir}{k}{j} 𝒱VV′ j≤k =
  N , N′ , refl , refl , λ {W}{W′} 𝒱WW′ →
    let 𝒱λNλN′sj = down (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir (ƛ N) (ƛ N′))
                        (suc k) 𝒱VV′ (suc j) (s≤s j≤k) in
    let ℰNWN′W′j = 𝒱λNλN′sj W W′ (suc j) ≤-refl 𝒱WW′ in
    ℰNWN′W′j

𝒱-dyn-any-elim-step-≻ : ∀{V}{V′}{k}{H}{A′}{c : gnd⇒ty H ⊑ A′}
   → #(𝒱⟦ ★ , A′ , unk⊑ c ⟧ ≻ V V′) (suc k)
   → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
             × #(𝒱⟦ gnd⇒ty H , A′ , c ⟧ ≻ V₁ V′) (suc k)
𝒱-dyn-any-elim-step-≻ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VGV′
... | yes refl
    with 𝒱VGV′
... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′

𝒱-dyn-any-elim-step-≺ : ∀{V}{V′}{k}{H}{A′}{c : gnd⇒ty H ⊑ A′}
   → #(𝒱⟦ ★ , A′ , unk⊑ c ⟧ ≺ V V′) (suc k)
   → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
             × #(𝒱⟦ gnd⇒ty H , A′ , c ⟧ ≺ V₁ V′) k
𝒱-dyn-any-elim-step-≺ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VGV′
... | yes refl
    with 𝒱VGV′
... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′

𝒱-dyn-R-step-≻ : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}
   → #(𝒱⟦ ★ , gnd⇒ty G , c ⟧ ≻ V V′) k
   → #(𝒱⟦ ★ , ★ , unk⊑unk ⟧ ≻ V (V′ ⟨ G !⟩)) k
𝒱-dyn-R-step-≻ {G} {c} {V} {V′} {zero} 𝒱VV′ =
     tz (𝒱⟦ ★ , ★ , unk⊑unk ⟧ ≻ V (V′ ⟨ G !⟩))
𝒱-dyn-R-step-≻ {G} {c} {V} {V′} {suc k} 𝒱VV′
    with unk⊑gnd-inv c
... | d , refl
    with 𝒱-dyn-any-elim-step-≻ {V}{V′}{k}{G}{_}{d} 𝒱VV′
... | V₁ , refl , v₁ , v′ , 𝒱V₁V′
    with G ≡ᵍ G
... | no neq = ⊥-elim 𝒱VV′
... | yes refl
    with gnd-prec-unique d Refl⊑
... | refl =
    let 𝒱V₁V′k = down (𝒱⟦ gnd⇒ty G , gnd⇒ty G , d ⟧ ≻ V₁ V′)
                       (suc k) 𝒱V₁V′ k (n≤1+n k) in
    v₁ , v′ , 𝒱V₁V′k

𝒱-dyn-R-step-≺ : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}
   → #(𝒱⟦ ★ , gnd⇒ty G , c ⟧ ≺ V V′) k
   → #(𝒱⟦ ★ , ★ , unk⊑unk ⟧ ≺ V (V′ ⟨ G !⟩)) k
𝒱-dyn-R-step-≺ {G} {c} {V} {V′} {zero} 𝒱VV′ =
     tz (𝒱⟦ ★ , ★ , unk⊑unk ⟧ ≺ V (V′ ⟨ G !⟩))
𝒱-dyn-R-step-≺ {G} {c} {V} {V′} {suc k} 𝒱VV′
    with unk⊑gnd-inv c
... | d , refl
    with 𝒱-dyn-any-elim-step-≺ {V}{V′}{k}{G}{_}{d} 𝒱VV′
... | V₁ , refl , v₁ , v′ , 𝒱V₁V′
    with G ≡ᵍ G
... | no neq = ⊥-elim 𝒱VV′
... | yes refl
    with gnd-prec-unique d Refl⊑
... | refl = v₁ , v′ , 𝒱V₁V′           {- No use of down! -}

𝒱-dyn-R-step : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}{dir}
   → #(𝒱⟦ ★ , gnd⇒ty G , c ⟧ dir V V′) k
   → #(𝒱⟦ ★ , ★ , unk⊑unk ⟧ dir V (V′ ⟨ G !⟩)) k
𝒱-dyn-R-step {G} {c} {V} {V′} {k} {≺} 𝒱VV′ =
    𝒱-dyn-R-step-≺{G} {c} {V} {V′} {k} 𝒱VV′ 
𝒱-dyn-R-step {G} {c} {V} {V′} {k} {≻} 𝒱VV′ =
   𝒱-dyn-R-step-≻{G} {c} {V} {V′} {k} 𝒱VV′

𝒱-dyn-L-step : ∀{G}{A′}{c : gnd⇒ty G ⊑ A′}{V}{V′}{dir}{k}
   → #(𝒱⟦ gnd⇒ty G , A′ , c ⟧ dir V V′) k
   → #(𝒱⟦ ★ , A′ , unk⊑ c ⟧ dir (V ⟨ G !⟩) V′) k
𝒱-dyn-L-step {G}{A′}{c}{V}{V′}{dir}{zero} 𝒱VV′k =
    tz (𝒱⟦ ★ , A′ , unk⊑ c ⟧ dir (V ⟨ G !⟩) V′)
𝒱-dyn-L-step {G} {A′} {c} {V} {V′} {≺} {suc k} 𝒱VV′sk
    with G ≡ᵍ G
... | no neq = ⊥-elim (neq refl)
... | yes refl =
    let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′sk in
    let 𝒱VV′k = down (𝒱⟦ gnd⇒ty G , A′ , c ⟧ ≺ V V′) (suc k) 𝒱VV′sk
                      k (n≤1+n k) in
    v , v′ , 𝒱VV′k
𝒱-dyn-L-step {G} {A′} {c} {V} {V′} {≻} {suc k} 𝒱VV′k
    with G ≡ᵍ G
... | no neq = ⊥-elim (neq refl)
... | yes refl =
      let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′k in
      v , v′ , 𝒱VV′k                  {- No use of down! -}

{--------------- Related values are related expressions -----------------------}

𝒱⇒ℰ-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{V V′}{dir}{k}
   → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′) k
     ---------------------------
   → #(dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′) k
𝒱⇒ℰ-step {A}{A′}{A⊑A′}{V} {V′} {dir} {zero} 𝒱VV′k =
   tz (dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′)
𝒱⇒ℰ-step {A}{A′}{A⊑A′}{V} {V′} {≺} {suc k} 𝒱VV′sk =
  ⇔-fro (LRₜ-suc{dir = ≺})
  (let (v , v′) = 𝒱⇒Value A⊑A′ V V′ 𝒱VV′sk in
  (inj₂ (inj₂ (v , inj₂ (V′ , (V′ END) , v′ , 𝒱VV′sk)))))
𝒱⇒ℰ-step {A}{A′}{A⊑A′}{V} {V′} {≻} {suc k} 𝒱VV′sk =
  ⇔-fro (LRₜ-suc{dir = ≻})
  (let (v , v′) = 𝒱⇒Value A⊑A′ V V′ 𝒱VV′sk in
  inj₂ (inj₂ (v′ , V , (V END) , v , 𝒱VV′sk)))

𝒱⇒ℰ : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{𝒫}{V V′}{dir}
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ A⊑A′
     ---------------------------
   → 𝒫 ⊢ᵒ dir ∣ V ⊑ᴸᴿₜ V′ ⦂ A⊑A′
𝒱⇒ℰ {A}{A′}{A⊑A′}{𝒫}{V}{V′}{dir} ⊢𝒱VV′ = ⊢ᵒ-intro λ k 𝒫k →
  𝒱⇒ℰ-step{V = V}{V′}{dir}{k} (⊢ᵒ-elim ⊢𝒱VV′ k 𝒫k)

{--------------- Blame on the right -------------------------------------------}

ℰ-blame-step : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{dir}{M}{k}
   → #(dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′) k
ℰ-blame-step {A}{A′}{A⊑A′}{dir} {M} {zero} = tz (dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′)
ℰ-blame-step {A}{A′}{A⊑A′}{≺} {M} {suc k} = inj₂ (inj₁ (blame END))
ℰ-blame-step {A}{A′}{A⊑A′}{≻} {M} {suc k} = inj₂ (inj₁ isBlame)

ℰ-blame : ∀{𝒫}{A}{A′}{A⊑A′ : A ⊑ A′}{M}{dir} → 𝒫 ⊢ᵒ dir ∣ M ⊑ᴸᴿₜ blame ⦂ A⊑A′
ℰ-blame {𝒫}{A}{A′}{A⊑A′}{M}{dir} = ⊢ᵒ-intro λ n x → ℰ-blame-step{dir = dir}
