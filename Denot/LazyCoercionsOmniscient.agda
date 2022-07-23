open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app;
            inspect; [_])
open import Level using (lower)

module Denot.LazyCoercionsOmniscient where

  open import Types
  open import Labels
  open import CastStructureABT
  open import LazyCoercionsABT
  open import LazyCoercions using (I-inj; coerce-aux)
  open import Denot.Value
  open import Denot.OpOmni
  open import Denot.ConsisOmni
  open import SetsAsPredicates
  open import Syntax hiding (id)



  data Proj : (B : Type) (ℓ : Label) (D : 𝒫 Val) → 𝒫 Val where
      proj-ok : ∀ {B ℓ D u} → (u∈ : u ∈ D) → (nbu : ¬isBlame u) → (u∶B : ⟦ u ∶ B ⟧) → u ∈ Proj B ℓ D
      proj-fail : ∀ {B ℓ D u} → (u∈ : u ∈ D) → (nbu : ¬isBlame u) → (¬u∶B : ¬ ⟦ u ∶ B ⟧) → (blame ℓ) ∈ Proj B ℓ D
            {- V ↦ (blame ℓ) -}
      proj-blame : ∀ {B ℓ ℓ' D} → (bl∈ : blame ℓ ∈ D) → blame ℓ ∈ Proj B ℓ' D

  {- Ground Coercion Semantics -}

  {- two ideas:
    idea 1 : produce blame immediately at function cast
      -- idea 1 is what I think the def of "omniscient" is
    idea 2 : decide whether to blame or not based on type information of values
             instead of by the coercion calculus  
  -}

  {-
  definition for omniscient semantics:
     c : Cast (A ⇒ B) L
  𝒞 D ⟨ c ⟩ d = 
    { d is blame, and d ∈ D  }
    ⊎ { d ∈ D and d is not blame and d ∶ B}
    ⊎ { d is blame L and ∃v. v ∈ D and ¬ (v ∶ B) }

  c' = c L1 ↣ d L1

  d : Int ⇒ Int
  c : ⋆ ⇒ Int

  Λ ⋆ 

  c L1 ↣ d L2 : (Int → Int) ⇒ (⋆ → Int)

  [ false ] → L1



  (∗ → Int) ⇒ (Int → Int)
  


  d is blame L1 and ∃v. v ∈ D and ¬ (v : A' ⇒ B')

  applyCast (c L1 ↣ d L1) (λ N) 
      = λ (λ x → (N · ⟨ c ⟩ x) ⟨ d ⟩)
  

  -}



  {-
  
  Proj (⋆ ⇒ (A' ⇒ B'))
  Proj (⋆ ⇒ (⋆ ⇒ ⋆) ⇒ (A' ⇒ B'))
  
  let id = λ x:Int. x
  let f = id ⟨ ⋆ ⟩ L1
  let g = f ⟨ cseq (⋆ → ⋆) ((⋆ → ⋆) → ⋆) ((Int → Int) → Int) ⟩ L2
  (g id)
  -}

  𝒞_⟨_⟩ : ∀ {A B} → (D : 𝒫 Val) → (c : Cast (A ⇒ B)) → 𝒫 Val
  𝒞 D ⟨ id ⟩ = D
  𝒞 D ⟨ _!! A {j} ⟩ = D
  𝒞 D ⟨ (B ?? ℓ) {¬⋆} ⟩ = Proj B ℓ D
  𝒞_⟨_⟩ {A ⇒ B} {A' ⇒ B'} D (c ↣ d) (V ↦ w) = V ↦ w ∈ ((Λ (A ⇒ B) (λ Y → (Λ A' (λ X → 𝒞 (Y ∗ (𝒞 X ⟨ c ⟩)) ⟨ d ⟩)))) ∗ D)
{-
"V' ↦ blame ℓ"

cod-fail
dom-fail



-}
  𝒞_⟨_⟩ {A ⇒ B} {A' ⇒ B'} D (c ↣ d) ν = ν ∈ D
  𝒞_⟨_⟩ {A ⇒ B} {A' ⇒ B'} D (c ↣ d) (blame ℓ) = blame ℓ ∈ D
  𝒞_⟨_⟩ {A ⇒ B} {A' ⇒ B'} D (c ↣ d) v = False
  𝒞 D ⟨ c `× d ⟩ = pair (𝒞 (car D) ⟨ c ⟩) (𝒞 (cdr D) ⟨ d ⟩)
  𝒞 D ⟨ c `+ d ⟩ = cond D (λ X → inleft (𝒞 X ⟨ c ⟩)) (λ Y → inright (𝒞 Y ⟨ d ⟩))
  𝒞 D ⟨ ⊥ A ⟨ ℓ ⟩ B ⟩ (blame ℓ') = blame ℓ' ∈ D ⊎ (Σ[ v ∈ Val ] v ∈ D × ¬isBlame v × ℓ' ≡ ℓ)
  𝒞 D ⟨ ⊥ A ⟨ ℓ ⟩ B ⟩ v = False


  𝒞-mono : ∀ {A B} (c : Cast (A ⇒ B)) {D D'} → scD D' → D ⊆ D' → 𝒞 D ⟨ c ⟩ ⊆ 𝒞 D' ⟨ c ⟩
  𝒞-mono = {!   !}

  postulate
    Λ-scD : ∀ A {F} → scD-1 F → scD (Λ A F)
    ∗-scD : ∀ {D E} → scD D → scD E → scD (D ∗ E)
    pair-scD : ∀ {D E} → scD D → scD E → scD (pair D E)
    car-scD : ∀ {D} → scD D → scD (car D)
    cdr-scD : ∀ {D} → scD D → scD (cdr D)
    inleft-scD : ∀ {D} → scD D → scD (inleft D)
    inright-scD : ∀ {D} → scD D → scD (inright D)
    cond-scD : ∀ {T D E} → scD T → scD-1 D → scD-1 E → scD (cond T D E)
    If-scD : ∀ {T D E} → scD T → scD D → scD E → scD (If T D E)
    𝒞-scD : ∀ {A B} (c : Cast (A ⇒ B)) {D} → scD D → scD (𝒞 D ⟨ c ⟩)
    ℘-scD : ∀ {B P f} → scD (℘ {B} P f )

{-
  postulate
    ∗-mono : ∀ {D E D' E'} → scD D' → scD E' → D ⊆ D' → E ⊆ E' → (D ∗ E) ⊆ (D' ∗ E')
    pair-mono : ∀ {D E D' E'} → scD D' → scD E' → D ⊆ D' → E ⊆ E' → (pair D E) ⊆ (pair D' E')
    car-mono : ∀ {D D'} → scD D' → D ⊆ D' → car D ⊆ car D'
    cdr-mono : ∀ {D D'} → scD D' → D ⊆ D' → cdr D ⊆ cdr D'
    inleft-mono : ∀ {D D'} → scD D' → D ⊆ D' → inleft D ⊆ inleft D'
    inright-mono : ∀ {D D'} → scD D' → D ⊆ D' → inright D ⊆ inright D'
    cond-mono : ∀ {T D E T' D' E'} → scD T' → T ⊆ T' 
      → (monoD-1 D D') → (monoD-1 E E') → cond T D E ⊆ cond T' D' E'
    If-mono : ∀ {T D E T' D' E'} → scD T' → T ⊆ T' → D ⊆ D' → E ⊆ E' → If T D E ⊆ If T' D' E'
  -}

  open import Denot.CastStructureOmni

  instance 
    dcs : DenotCastStruct
    dcs = record
            { cast = cs
            ; 𝒞 = λ c D → 𝒞 D ⟨ c ⟩ }

  
  open DenotCastStruct dcs using () renaming (⟦_⟧ to 𝒪⟦_⟧)

  _⟶_ = _—→_


  postulate
    𝒪-scD : ∀ M ρ (scDρ : ∀ i → scD (ρ i)) → scD (𝒪⟦ M ⟧ ρ)
    𝒪-mono : ∀ M ρ ρ' (monoρ : ∀ i → ρ i ⊆ ρ' i) → 𝒪⟦ M ⟧ ρ ⊆ 𝒪⟦ M ⟧ ρ'
    rebind : ∀ {X X' Y ρ} N → X ⊆ X' → 𝒪⟦ rename (ext suc) N ⟧ (X • Y • ρ) ⊆ 𝒪⟦ N ⟧ (X' • ρ)
    𝒪-wt : ∀ M ρ {A Γ} → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) → (Γ⊢M∶A : Γ ⊢ M ⦂ A) → ∈⟦ 𝒪⟦ M ⟧ ρ ∶ A ⟧
    nb∈mem→nb₊ : ∀ {V} → ¬isBlame-∈ (mem V) → ¬isBlame₊ V
    ∈mem→ne : ∀ {A}{V : List A} v → v ∈ mem V → V ≢ []
    ne→∈mem : ∀ {A}{V : List A} → V ≢ [] → Σ[ a ∈ A ] a ∈ mem V
    ¬isBlame-∈-℘ : ∀ {B} (P : Prim B) f → ¬isBlame-∈ (℘ P f)
    ¬isBlame-∈-Λ : ∀ A F → ¬isBlame-∈ (Λ A F)
    neValue : ∀ V ρ → (vV : Value V) → Σ[ d ∈ Val ] d ∈ 𝒪⟦ V ⟧ ρ × ¬isBlame d
    car-wt : ∀ {D A B} → ∈⟦ D ∶ A `× B ⟧ → ∈⟦ car D ∶ A ⟧
    cdr-wt : ∀ {D A B} → ∈⟦ D ∶ A `× B ⟧ → ∈⟦ cdr D ∶ B ⟧
    Dsubst-⊇ : ∀ N X Y Y' ρ → Y ⊆ Y' → 𝒪⟦ (rename (ext suc) N) ⟧ (Y • X • ρ)
            ⊆ 𝒪⟦ N ⟧ (Y' • ρ)                
    subst-⊇ : ∀ M N ρ → 𝒪⟦ _[_] M N ⟧ ρ ⊆ 𝒪⟦ M ⟧ ((𝒪⟦ N ⟧ ρ) • ρ)
    ν∈Fun : ∀ {M ρ Γ A B} → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) → (Γ⊢M∶A : Γ ⊢ M ⦂ A ⇒ B) → ν ∈ 𝒪⟦ M ⟧ ρ
    -- going to need a closed-down lemma as well

  β-⊇ : ∀ {A} (F : 𝒫 Val → 𝒫 Val) D
    → (D∶A : ∈⟦ D ∶ A ⟧)
    → (scD : scD D)
    → (nbD : ¬isBlame-∈ D)
    → (F-cont : ∀ D' d → d ∈ F D' → Σ[ V ∈ List Val ] (mem V) ⊆ D' × d ∈ F (mem V) × V ≢ [])
    → F D ⊆ ((Λ A F) ∗ D)
  β-⊇ {A} F D D∶A scD nbD F-cont d d∈ with F-cont D d d∈
  ... | ⟨ V , ⟨ V⊆ , ⟨ d∈' , neV ⟩ ⟩ ⟩ = 
    ∗-app {V = V} (Λ-↦ d∈' (∈→⟦∶⟧₊ (λ d z → D∶A d (V⊆ d z))) 
                      (λ u v z z₁ → scD u v (V⊆ u z) (V⊆ v z₁)) 
                      (nb∈mem→nb₊ (λ d z → nbD d (V⊆ d z))) neV) 
                  V⊆ (nb∈mem→nb₊ (λ d z → nbD d (V⊆ d z)))

  β-⊆' : ∀ {A} (F : 𝒫 Val → 𝒫 Val) (D : 𝒫 Val)
      → scD D
      → monoD-1 F F
      → (blF : ∀ D ℓ → blame ℓ ∈ D → blame ℓ ∈ F D)
      → ((Λ A F) ∗ D) ⊆ F D
  β-⊆' F D scDD Fmono blF d (∗-app (Λ-↦ {V = V} w∈ V∶A scV nbV₁ neV) V⊆ nbV) = Fmono (mem V) D scDD V⊆ d w∈
  β-⊆' F D scDD Fmono blF (blame ℓ) (∗-blame-rand bl∈) = blF D ℓ bl∈

  β-⊆ : ∀ {A} (F : 𝒫 Val → 𝒫 Val) (D : 𝒫 Val)
      → scD D
      → monoD-1 F F
      → ¬isBlame-∈ D
      → ((Λ A F) ∗ D) ⊆ F D
  β-⊆ F D scDD Fmono nbD d (∗-app (Λ-↦ {V = V} w∈ V∶A scV nbV₁ neV) V⊆ nbV) = Fmono (mem V) D scDD V⊆ d w∈
  β-⊆ F D scDD Fmono nbD (blame ℓ) (∗-blame-rand bl∈) = ⊥-elim (nbD (blame ℓ) bl∈ tt)


  ¬⌣→¬⟦∶⟧ : ∀ A B → ¬ A ⌣ B → ∀ d  → ¬isBlame d → ⟦ d ∶ A ⟧ → ¬ ⟦ d ∶ B ⟧
  ¬⌣→¬⟦∶⟧ ⋆ B ¬A⌣B d nbd d∶A = ⊥-elim (¬A⌣B unk⌣L)
  ¬⌣→¬⟦∶⟧ A ⋆ ¬A⌣B d nbd d∶A = ⊥-elim (¬A⌣B unk⌣R)
  ¬⌣→¬⟦∶⟧ (` x) (` x₁) ¬A⌣B (const {ι} k) nbd d∶A with base-eq? x ι | base-eq? x₁ ι 
  ... | no neq | q' = ⊥-elim d∶A
  ... | yes refl | no neq = λ z → z
  ... | yes refl | yes refl = ⊥-elim (nbd (¬A⌣B base⌣))
  ¬⌣→¬⟦∶⟧ (` x) (` x₁) ¬A⌣B (blame ℓ) nbd d∶A = ⊥-elim (nbd tt)
  ¬⌣→¬⟦∶⟧ (` x) (B ⇒ B₁) ¬A⌣B (const k) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (` x) (B ⇒ B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (` x) (B `× B₁) ¬A⌣B (const k) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (` x) (B `× B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (` x) (B `⊎ B₁) ¬A⌣B (const k) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (` x) (B `⊎ B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (` x) ¬A⌣B (V ↦ d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (` x) ¬A⌣B ν nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (` x) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (B ⇒ B₁) ¬A⌣B d nbd d∶A = λ _ → ¬A⌣B fun⌣
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (B `× B₁) ¬A⌣B (V ↦ d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (B `× B₁) ¬A⌣B ν nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (B `× B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (B `⊎ B₁) ¬A⌣B (V ↦ d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (B `⊎ B₁) ¬A⌣B ν nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A ⇒ A₁) (B `⊎ B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A `× A₁) (` x) ¬A⌣B (fst d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `× A₁) (` x) ¬A⌣B (snd d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `× A₁) (` x) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A `× A₁) (B ⇒ B₁) ¬A⌣B (fst d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `× A₁) (B ⇒ B₁) ¬A⌣B (snd d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `× A₁) (B ⇒ B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A `× A₁) (B `× B₁) ¬A⌣B d nbd d∶A = λ _ → ¬A⌣B pair⌣
  ¬⌣→¬⟦∶⟧ (A `× A₁) (B `⊎ B₁) ¬A⌣B (fst d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `× A₁) (B `⊎ B₁) ¬A⌣B (snd d) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `× A₁) (B `⊎ B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (` x) ¬A⌣B (inl V) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (` x) ¬A⌣B (inr V) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (` x) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (B ⇒ B₁) ¬A⌣B (inl V) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (B ⇒ B₁) ¬A⌣B (inr V) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (B ⇒ B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (B `× B₁) ¬A⌣B (inl V) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (B `× B₁) ¬A⌣B (inr V) nbd d∶A = λ z → z
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (B `× B₁) ¬A⌣B (blame ℓ) nbd d∶A = λ _ → nbd tt
  ¬⌣→¬⟦∶⟧ (A `⊎ A₁) (B `⊎ B₁) ¬A⌣B d nbd d∶A = λ _ → ¬A⌣B sum⌣
  
  data _𝒪∼[_]_ : Val → Type → Val → Set where
    omni-ok : ∀ {u τ} → ¬isBlame u → u 𝒪∼[ τ ] u
    omni-blame : ∀ {ℓ τ} → (blame ℓ) 𝒪∼[ τ ] (blame ℓ)
    omni-fun : ∀ {V w ℓ A B} → (V∶A : ∈⟦ (mem V) ∶ A ⟧)
             → (w∼ : w 𝒪∼[ B ] (blame ℓ)) 
             → (V ↦ w) 𝒪∼[ A ⇒ B ] (blame ℓ)

  𝒪∼-refl : ∀ {v τ} → v 𝒪∼[ τ ] v
  𝒪∼-refl {const k} = omni-ok (λ z → z)
  𝒪∼-refl {V ↦ v} = omni-ok (λ z → z)
  𝒪∼-refl {ν} = omni-ok (λ z → z)
  𝒪∼-refl {fst v} = omni-ok (λ z → z)
  𝒪∼-refl {snd v} = omni-ok (λ z → z)
  𝒪∼-refl {inl V} = omni-ok (λ z → z)
  𝒪∼-refl {inr V} = omni-ok (λ z → z)
  𝒪∼-refl {blame ℓ} = omni-blame

  _𝒪⊆[_]_ : 𝒫 Val → Type → 𝒫 Val → Set
  S 𝒪⊆[ τ ] T = ∀ d → d ∈ S → Σ[ d' ∈ Val ] d' ∈ T × d 𝒪∼[ τ ] d'

  𝒪⊆→⊆ : ∀ {D τ D'} → D 𝒪⊆[ τ ] D' → D ⊆ D'
  𝒪⊆→⊆ 𝒪⊆ d d∈ with 𝒪⊆ d d∈
  ... | ⟨ d' , ⟨ d'∈ , d∼ ⟩ ⟩ = {!   !}

  coerce-Proj : ∀ A B ℓ D → ∈⟦ D ∶ A ⟧ → 𝒞 D ⟨ coerce A B ℓ ⟩ 𝒪⊆[ B ] Proj B ℓ D
  coerce-aux-Proj : ∀ A B (A⌣B : A ⌣ B) ℓ D → ∈⟦ D ∶ A ⟧ → 𝒞 D ⟨ coerce-aux A⌣B ℓ ⟩ 𝒪⊆[ B ] Proj B ℓ D
  coerce-Proj A B ℓ D D∶A d d∈𝒞coerceD with A `⌣ B | d | d∈𝒞coerceD
  ... | yes A⌣B | d | d∈ = coerce-aux-Proj A B A⌣B ℓ D D∶A d d∈
  ... | no ¬A⌣B | blame ℓ' | inj₁ bl∈D = ⟨ blame ℓ' , ⟨ proj-blame bl∈D , omni-blame ⟩ ⟩
  ... | no ¬A⌣B | blame ℓ' | inj₂ ⟨ u , ⟨ u∈D , ⟨ nbu , refl ⟩ ⟩ ⟩ = 
    ⟨ blame ℓ , ⟨ proj-fail u∈D nbu (¬⌣→¬⟦∶⟧ A B ¬A⌣B u nbu (D∶A u u∈D)) , omni-blame ⟩ ⟩
  coerce-aux-Proj .⋆ B unk⌣L ℓ D D∶A d d∈𝒞coerce-aux with eq-unk B | d | d∈𝒞coerce-aux
  ... | yes refl | const k | d∈ = ⟨ const k , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | V ↦ d₁ | d∈ = ⟨ V ↦ d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | ν | d∈ = ⟨ ν , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | fst d₁ | d∈ = ⟨ fst d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | snd d₁ | d∈ = ⟨ snd d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | inl V | d∈ = ⟨ inl V , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | inr V | d∈ = ⟨ inr V , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | blame ℓ₁ | d∈ = ⟨ blame ℓ₁ , ⟨ proj-blame d∈ , omni-blame ⟩ ⟩
  ... | no neq | d | d∈ = ⟨ d , ⟨ d∈ , 𝒪∼-refl ⟩ ⟩
  coerce-aux-Proj A .⋆ unk⌣R ℓ D D∶A d d∈𝒞coerce-aux with eq-unk A | d | d∈𝒞coerce-aux
  ... | yes refl | const k | d∈ = ⟨ const k , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | V ↦ d₁ | d∈ = ⟨ V ↦ d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | ν | d∈ = ⟨ ν , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | fst d₁ | d∈ = ⟨ fst d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | snd d₁ | d∈ = ⟨ snd d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | inl V | d∈ = ⟨ inl V , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | inr V | d∈ = ⟨ inr V , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | yes refl | blame ℓ₁ | d∈ = ⟨ blame ℓ₁ , ⟨ proj-blame d∈ , omni-blame ⟩ ⟩
  ... | no neq | const k | d∈ = ⟨ const k , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | no neq | V ↦ d₁ | d∈ = ⟨ V ↦ d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | no neq | ν | d∈ = ⟨ ν , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | no neq | fst d₁ | d∈ = ⟨ fst d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | no neq | snd d₁ | d∈ = ⟨ snd d₁ , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | no neq | inl V | d∈ = ⟨ inl V , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | no neq | inr V | d∈ = ⟨ inr V , ⟨ proj-ok d∈ (λ z → z) tt , omni-ok (λ z → z) ⟩ ⟩
  ... | no neq | blame ℓ₁ | d∈ = ⟨ blame ℓ₁ , ⟨ proj-blame d∈ , omni-blame ⟩ ⟩
  coerce-aux-Proj .(` _) .(` _) base⌣ ℓ D D∶A d d∈𝒞coerce-aux with d | (D∶A d d∈𝒞coerce-aux) | d∈𝒞coerce-aux
  ... | const k | d∶A | d∈ = ⟨ const k , ⟨ proj-ok d∈ (λ z → z) d∶A , omni-ok (λ z → z) ⟩ ⟩
  ... | blame ℓ₁ | d∶A | d∈ = ⟨ blame ℓ₁ , ⟨ proj-blame d∈ , omni-blame ⟩ ⟩
  coerce-aux-Proj (A ⇒ B) (A' ⇒ B') fun⌣ ℓ D D∶A (V ↦ w) v∈
    with β-⊆ {!   !} D {!   !} {!   !} {!   !} (V ↦ w) v∈
  ... | Λ-↦ w∈ V∶A scV nbV neV 
     with coerce-Proj B B' ℓ {!   !} {!   !} w w∈
  ... | ⟨ u , ⟨ proj-ok u∈ nbu u∶B , u∼ ⟩ ⟩ = {!   !}
  ... | ⟨ blame ℓ , ⟨ proj-fail (∗-app {V = V'} V↦w∈ V⊆ nbV₁) nbu ¬u∶B , u∼ ⟩ ⟩ = {!   !}
  ... | ⟨ blame ℓ , ⟨ proj-fail (∗-blame-rator bl∈) nbu ¬u∶B , u∼ ⟩ ⟩ = ⊥-elim (nbu tt)
  ... | ⟨ blame ℓ , ⟨ proj-fail (∗-blame-rand bl∈) nbu ¬u∶B , u∼ ⟩ ⟩ = ⊥-elim (nbu tt)
  ... | ⟨ blame ℓ' , ⟨ proj-blame (∗-app {V = V'} V↦w∈ V⊆ nbV₁) , u∼ ⟩ ⟩ = ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩
  ... | ⟨ blame ℓ' , ⟨ proj-blame (∗-blame-rator bl∈) , u∼ ⟩ ⟩ = ⟨ blame ℓ' , ⟨ proj-blame bl∈ , omni-fun (⟦∶⟧₊→∈ V∶A) u∼ ⟩ ⟩
  ... | ⟨ blame ℓ' , ⟨ proj-blame (∗-blame-rand bl∈) , u∼ ⟩ ⟩ = {!   !}
  coerce-aux-Proj (A ⇒ B) (A' ⇒ B') fun⌣ ℓ D D∶A ν ν∈ = {!   !}
  coerce-aux-Proj (A ⇒ B) (A' ⇒ B') fun⌣ ℓ D D∶A (blame ℓ') bl∈ = {!   !}
  coerce-aux-Proj .(_ `× _) .(_ `× _) pair⌣ ℓ D D∶A d d∈𝒞coerce-aux = {!   !}
  coerce-aux-Proj .(_ `⊎ _) .(_ `⊎ _) sum⌣ ℓ D D∶A d d∈𝒞coerce-aux = {!   !}


{-

  coerce-aux-Proj (A ⇒ B) (A' ⇒ B') fun⌣ ℓ D D∶A (V ↦ w) v∈ 
    with β-⊆ {!   !} D {!   !} {!   !} {!   !} (V ↦ w) v∈
  ... | Λ-↦ w∈ V∶A scV nbV neV 
     with coerce-Proj B B' ℓ {!   !} {!   !} w w∈
  ... | proj-ok (∗-app V↦w∈ V⊆ nbV₁) nbu u∶B = {!   !}
  ... | proj-ok (∗-blame-rator bl∈) nbu u∶B = ⊥-elim (nbu tt)
  ... | proj-ok (∗-blame-rand bl∈) nbu u∶B = ⊥-elim (nbu tt)
  ... | proj-fail (∗-app V↦w∈ V⊆ nbV₁) nbu ¬u∶B = {! proj-fail V↦w∈ ? ?  !}
  ... | proj-fail (∗-blame-rator bl∈) nbu ¬u∶B = ⊥-elim (nbu tt)
  ... | proj-fail (∗-blame-rand bl∈) nbu ¬u∶B = ⊥-elim (nbu tt)
  ... | proj-blame (∗-app V↦w∈ V⊆ nbV₁) = {!   !}
  ... | proj-blame (∗-blame-rator bl∈) = {!   !}
  ... | proj-blame (∗-blame-rand bl∈) = {!   !}
  {-
  coerce-aux-Proj (A ⇒ B) (A' ⇒ B') fun⌣ ℓ D D∶A (V ↦ w) 
    (∗-app (Λ-↦ {V = V'} (Λ-↦ {V = V} w∈ V∶A₁ scV₁ nbV₂ neV₁) V∶A scV nbV₁ neV) V⊆ nbV) 
    with coerce-Proj B B' ℓ ((mem V') ∗ 𝒞 (mem V) ⟨ coerce A' A (flip ℓ) ⟩) {!  !} w w∈
  ... | proj-ok (∗-app {V = V''} V↦w∈ V⊆₁ nbV₃) nbu u∶B = 
     proj-ok (V⊆ (V ↦ w) {! V↦w∈   !}) (λ z → z) (λ _ → u∶B)
       where
       V⊆' : (mem V'') ⊆ (mem V)
       V⊆' u u∈V'' with coerce-Proj A' A (flip ℓ) (mem V) {!   !} u (V⊆₁ u u∈V'')
       ... | proj-ok u∈ nbu u∶B = u∈
       ... | proj-fail {u = u₁} u₁∈ nbu₁ ¬u∶B = ⊥-elim (lookup nbV₃ u∈V'' tt)
       ... | proj-blame bl∈ = bl∈
  ... | proj-ok (∗-blame-rator bl∈) nbu u∶B = ⊥-elim (nbu tt)
  ... | proj-ok (∗-blame-rand bl∈) nbu u∶B = ⊥-elim (nbu tt)
  ... | proj-fail (∗-app V↦w∈ V⊆₁ nbV₃) nbu ¬u∶B = {! w∈  !}
  ... | proj-fail (∗-blame-rator bl∈) nbu ¬u∶B = ⊥-elim (nbu tt)
  ... | proj-fail (∗-blame-rand bl∈) nbu ¬u∶B = ⊥-elim (nbu tt)
  ... | proj-blame (∗-app V↦w∈ V⊆₁ nbV₃) = {!  !}
  ... | proj-blame (∗-blame-rator bl∈) = ⊥-elim (lookup nbV₁ bl∈ tt)
  ... | proj-blame (∗-blame-rand bl∈) = {! bl∈  !}

  -}
  {-
    with coerce-Proj B B' ℓ (D ∗ (𝒞 (mem V) ⟨ coerce A' A (flip ℓ) ⟩)) {! w∈  !} w w∈
  ... | proj-ok (∗-app V↦w∈ V⊆ nbV₁) nbw w∶B' = {!   !}
  ... | proj-ok (∗-blame-rator bl∈) nbw w∶B' = ⊥-elim (nbw tt)
  ... | proj-ok (∗-blame-rand bl∈) nbw w∶B' = ⊥-elim (nbw tt)
  ... | proj-fail (∗-app V↦w∈ V⊆ nbV₁) nbw ¬w∶B' = {!   !}
  ... | proj-fail (∗-blame-rator bl∈) nbw ¬w∶B' = ⊥-elim (nbw tt)
  ... | proj-fail (∗-blame-rand bl∈) nbw ¬w∶B' = ⊥-elim (nbw tt)
  ... | proj-blame (∗-app V↦w∈ V⊆ nbV₁) = {!   !}
  ... | proj-blame (∗-blame-rator bl∈) = {! bl∈ !}
  ... | proj-blame (∗-blame-rand bl∈) = {! bl∈  !}
  -}
  coerce-aux-Proj (A ⇒ B) (A' ⇒ B') fun⌣ ℓ D D∶A ν ν∈ = proj-ok ν∈ (λ z → z) tt
  coerce-aux-Proj (A ⇒ B) (A' ⇒ B') fun⌣ ℓ D D∶A (blame ℓ') bl∈ = proj-blame bl∈
  coerce-aux-Proj (A `× B) (A' `× B') pair⌣ ℓ D D∶A (fst u) (pair-fst u∈ v∈ nbu nbv)
    with coerce-Proj A A' ℓ (car D) (car-wt D∶A) u u∈
  ... | proj-ok (car-fst fstu∈ nbu₂) nbu₁ u∶B = proj-ok fstu∈ (λ z → z) u∶B
  ... | proj-ok (car-blame bl∈) nbu₁ u∶B = ⊥-elim (nbu tt)
  ... | proj-fail u∈₁ nbu₁ ¬u∶B = ⊥-elim (nbu tt)
  ... | proj-blame bl∈ = ⊥-elim (nbu tt)
  coerce-aux-Proj (A `× B) (A' `× B') pair⌣ ℓ D D∶A (snd v) (pair-snd u∈ v∈ nbu nbv)
    with coerce-Proj B B' ℓ (cdr D) (cdr-wt D∶A) v v∈
  ... | proj-ok (cdr-snd sndv∈ nbv₁) nbu₁ u∶B = proj-ok sndv∈ (λ z → z) u∶B
  ... | proj-ok (cdr-blame bl∈) nbu₁ u∶B = ⊥-elim (nbv tt)
  ... | proj-fail u∈₁ nbu₁ ¬u∶B = ⊥-elim (nbv tt)
  ... | proj-blame bl∈ = ⊥-elim (nbv tt)
  coerce-aux-Proj (A `× B) (A' `× B') pair⌣ ℓ D D∶A (blame ℓ') (pair-blame-fst bl∈)
    with coerce-Proj A A' ℓ (car D) (car-wt D∶A) (blame ℓ') bl∈
  ... | proj-ok u∈ nbu u∶B = ⊥-elim (nbu tt)
  ... | proj-fail (car-fst fstu∈ nbu₁) nbu ¬u∶B = proj-fail fstu∈ (λ z → z) ¬u∶B
  ... | proj-fail (car-blame bl∈₁) nbu ¬u∶B = ⊥-elim (nbu tt)
  ... | proj-blame (car-fst fstu∈ nbu) = ⊥-elim (nbu tt)
  ... | proj-blame (car-blame bl∈₁) = proj-blame bl∈₁
  coerce-aux-Proj (A `× B) (A' `× B') pair⌣ ℓ D D∶A (blame ℓ') (pair-blame-snd bl∈)
    with coerce-Proj B B' ℓ (cdr D) (cdr-wt D∶A) (blame ℓ') bl∈
  ... | proj-ok u∈ nbu u∶B = ⊥-elim (nbu tt)
  ... | proj-fail (cdr-snd sndv∈ nbv) nbu ¬u∶B = proj-fail sndv∈ (λ z → z) ¬u∶B
  ... | proj-fail (cdr-blame bl∈₁) nbu ¬u∶B = ⊥-elim (nbu tt)
  ... | proj-blame (cdr-snd sndv∈ nbv) = ⊥-elim (nbv tt)
  ... | proj-blame (cdr-blame bl∈₁) = proj-blame bl∈₁
  coerce-aux-Proj (A `⊎ B) (A' `⊎ B') sum⌣ ℓ D D∶A (inl V) (cond-inl {V = V'} LV∈ nbV (inleft-inl V⊆ nbV₁)) = 
    proj-ok {! LV∈  !} (λ z → z) {!  V⊆  !}
  coerce-aux-Proj (A `⊎ B) (A' `⊎ B') sum⌣ ℓ D D∶A (blame ℓ') (cond-inl {V = V'} LV∈ nbV (inleft-blame bl∈)) = {!   !}
  coerce-aux-Proj (A `⊎ B) (A' `⊎ B') sum⌣ ℓ D D∶A .(inr _) (cond-inr {V = V'} RV∈ nbV (inright-inr V⊆ nbV₁)) = {!   !}
  coerce-aux-Proj (A `⊎ B) (A' `⊎ B') sum⌣ ℓ D D∶A .(blame _) (cond-inr {V = V'} RV∈ nbV (inright-blame bl∈)) = {!   !}
  coerce-aux-Proj (A `⊎ B) (A' `⊎ B') sum⌣ ℓ D D∶A (blame ℓ') (cond-blame x) = proj-blame x




  coerce-sound-⊇ : ∀ {A B Γ}
                 → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ∀ V → (vV : Value V) 
                 → ∀ ρ → (scρ : ∀ i → scD (ρ i)) → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) 
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) 
                 → 𝒪⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ (𝒞_⟨_⟩ (𝒪⟦ V ⟧ ρ) c)
  coerce-sound-⊇ {A}{.A}{Γ} id V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ = v∈
  coerce-sound-⊇ {.⋆}{B}{Γ} (_??_ .B x {j}) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ 
    with canonical⋆ Γ⊢V∶A vV
  ... | ⟨ A' , ⟨ M , ⟨ (_!! A' {j'}) , ⟨ i , ⟨ Γ⊢M∶A' , refl ⟩ ⟩ ⟩ ⟩ ⟩ = 
    coerce-Proj A' B x (𝒪⟦ M ⟧ ρ) (𝒪-wt M ρ ρ∶Γ Γ⊢M∶A') v v∈
  coerce-sound-⊇ {A ⇒ B}{A' ⇒ B'}{Γ} (c ↣ d) V vV ρ scρ ρ∶Γ Γ⊢V∶A (V' ↦ w) v∈
    with V | vV | Γ⊢V∶A
  ... | (ƛ A ˙ N) | vV | (⊢ƛ A ⊢N ⟨ refl , refl ⟩) = 
    β-⊇ (λ z → Λ A' (λ z₁ → 𝒞 z ∗ 𝒞 z₁ ⟨ c ⟩ ⟨ d ⟩)) (Λ A (λ X → 𝒪⟦ N ⟧ (X • ρ))) 
         (𝒪-wt (ƛ A ˙ N) ρ {Γ = Γ} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩)) 
         (Λ-scD A λ D scD → 𝒪-scD N (D • ρ) λ { zero → scD ; (suc i) → scρ i}) 
         (¬isBlame-∈-Λ A (λ X → 𝒪⟦ N ⟧ (X • ρ))) 
         {!   !} 
         (V' ↦ w) 
         ((Λ-mono (λ X X' scX' X⊆ → 𝒞-mono d 
            ((∗-scD (Λ-scD A (λ D scD → 𝒪-scD N (D • ρ) λ { zero → scD ; (suc i) → scρ i})) (𝒞-scD c scX'))) 
            {!   !})) (V' ↦ w) v∈)

{-
Λ-mono (λ X X' scX' X⊆ → 𝒞-mono d 
          (∗-scD (Λ-scD A (λ X scX → 𝒪-scD N (X • ρ) 
                    (λ {zero → scX ; (suc i) → scρ i}))) (𝒞-scD c scX')) 
          (∗-mono ? {- (Λ-scD A (λ X scX → 𝒪-scD  N (X • ρ) 
                    (λ {zero → scX ; (suc i) → scρ i})))-} {- (𝒞-scD c scX') -} HOLE
                  (Λ-mono (λ X X' scX' X⊆ → rebind N X⊆)) 
                  (𝒞-mono c scX' X⊆)))
-}

  {-
    β-⊇  (λ z → Λ A' (λ z₁ → 𝒞 z ∗ 𝒞 z₁ ⟨ c ⟩ ⟨ d ⟩)) (Λ A (λ X → 𝒪⟦ N ⟧ (X • ρ))) 
          (𝒪-wt (ƛ A ˙ N) ρ {Γ = Γ} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩)) 
          (𝒪-scD (ƛ A ˙ N) ρ scρ) (¬isBlame-∈-Λ A (λ X → 𝒪⟦ N ⟧ (X • ρ))) 
       ?
       (V' ↦ w) 
       (Λ-mono (λ X X' scX' X⊆ → 𝒞-mono d 
          (∗-scD (Λ-scD A (λ X scX → 𝒪-scD N (X • ρ) 
                    (λ {zero → scX ; (suc i) → scρ i}))) (𝒞-scD c scX')) 
          (∗-mono ? {- (Λ-scD A (λ X scX → 𝒪-scD  N (X • ρ) 
                    (λ {zero → scX ; (suc i) → scρ i})))-} {- (𝒞-scD c scX') -} HOLE 
                  (Λ-mono (λ X X' scX' X⊆ → rebind N X⊆)) 
                  (𝒞-mono c scX' X⊆))) (V' ↦ w) v∈) 
                  -}
  ... | ($ f # (P-Fun P)) | vV | (⊢$ f (P-Fun {ι}{τ} P) refl) = 
      β-⊇ (λ z → Λ A' (λ z₁ → 𝒞 z ∗ 𝒞 z₁ ⟨ c ⟩ ⟨ d ⟩)) (℘ (P-Fun P) f) 
         (𝒪-wt ($ f # (P-Fun P)) ρ {` ι ⇒ τ}{Γ} ρ∶Γ (⊢$ f (P-Fun P) refl)) 
         ℘-scD (¬isBlame-∈-℘ (P-Fun P) f) 
         {!   !} 
         (V' ↦ w) v∈  
  ... | ⟦ M , N ⟧ | vV | (⊢cons ⊢M ⊢N ())
  ... | (inl M other B) | vV | (⊢inl B ⊢M ())
  ... | (inr M other A) | vV | (⊢inr A ⊢M ())
  ... | (M ⟨ c₁ ₍ I-inj ₎⟩) | vV | (⊢wrap c₁ I-inj ⊢M ⟨ eq₁ , () ⟩)
  coerce-sound-⊇ {A ⇒ B}{A' ⇒ B'}{Γ} (c ↣ d) V vV ρ scρ ρ∶Γ Γ⊢V∶A (blame l) v∈ = {!   !}
  coerce-sound-⊇ {A ⇒ B} {A' ⇒ B'} {Γ} (c ↣ d) V vV ρ scρ ρ∶Γ Γ⊢V∶A ν Λ-ν = {!   !}
  coerce-sound-⊇ {(A `× B)}{(A' `× B')}{Γ} (c `× c₁) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ = v∈
  coerce-sound-⊇ {(A `⊎ B)}{(A' `⊎ B')}{Γ} (c `+ c₁) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ = v∈
  coerce-sound-⊇ {A}{B}{Γ}(⊥ .A ⟨ x ⟩ .B) V vV ρ scρ ρ∶Γ Γ⊢V∶A (blame ℓ) v∈ with neValue V ρ vV
  ... | ⟨ d , ⟨ d∈ , nbd ⟩ ⟩  = inj₂ ⟨ d , ⟨ d∈ , ⟨ nbd , v∈ ⟩ ⟩ ⟩


  postulate
    ξ-⊇ : ∀ {A B M N ρ} (F : Frame A B) → M ⟶ N → 𝒪⟦ plug N F ⟧ ρ ⊆ 𝒪⟦ plug M F ⟧ ρ
    ξ-blame-⊇ : ∀ {A B} (F : Frame A B) {ℓ ρ} → ℬ ℓ ⊆ 𝒪⟦ plug (mkblame A ℓ) F ⟧ ρ
    β-⊇' : ∀ {A F D} → F D ⊆ ((Λ A F) ∗ D)
    δ-⊇ : ∀ {A B} {a : Prim A} {b : Prim B} {ab : Prim (A ⇒ B)}{f k} → ℘ b (f k) ⊆ (℘ ab f  ∗ ℘ a k)
    β-if-true-⊇ : ∀ {P D E} → D ⊆ If (℘ P true) D E
    β-if-false-⊇ : ∀ {P D E} → E ⊆ If (℘ P false) D E
    β-fst-⊇ : ∀ {D E} → D ⊆ car (pair D E)
    β-snd-⊇ : ∀ {D E} → E ⊆ cdr (pair D E)
    β-caseL-⊇ : ∀ {D F G} → F D ⊆ cond (inleft D) F G
    β-caseR-⊇ : ∀ {D F G} → G D ⊆ cond (inright D) F G

  𝒪-sound-⊇ : ∀ {M N ρ} → M ⟶ N
     → ∀ {Γ A} 
     → (scρ : ∀ i → scD (ρ i))
     → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) 
     → (Γ⊢M∶A : Γ ⊢ M ⦂ A)
     → 𝒪⟦ N ⟧ ρ ⊆ 𝒪⟦ M ⟧ ρ
  𝒪-sound-⊇ (ξ {F = F} ⊢M M⟶N) scρ ρ∶Γ Γ⊢M∶A = ξ-⊇ F M⟶N
  𝒪-sound-⊇ (ξ-blame {F = F}) scρ ρ∶Γ Γ⊢M∶A = ξ-blame-⊇ F
  𝒪-sound-⊇ {(ƛ A ˙ M) · N}{N'}{ρ} (β x) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-⊇' d (subst-⊇ M N ρ d d∈)
  𝒪-sound-⊇ δ scρ ρ∶Γ Γ⊢M∶A = δ-⊇
  𝒪-sound-⊇ β-if-true scρ ρ∶Γ Γ⊢M∶A = β-if-true-⊇
  𝒪-sound-⊇ β-if-false scρ ρ∶Γ Γ⊢M∶A = β-if-false-⊇
  𝒪-sound-⊇ (β-fst vM vN) scρ ρ∶Γ Γ⊢M∶A = β-fst-⊇
  𝒪-sound-⊇ (β-snd vM vN) scρ ρ∶Γ Γ⊢M∶A = β-snd-⊇
  𝒪-sound-⊇ {(case (inl L other B) of A ⇒ M ∣ B ⇒ N)}{Z}{ρ}(β-caseL vT) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-caseL-⊇ d (subst-⊇ M L ρ d d∈)
  𝒪-sound-⊇ {(case (inr R other A) of A ⇒ M ∣ B ⇒ N)}{Z}{ρ}(β-caseR vT) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-caseR-⊇ d (subst-⊇ N R ρ d d∈)
  𝒪-sound-⊇ {V ⟨ c ⟩} {ρ = ρ} (cast ⊢V v) scρ ρ∶Γ (⊢cast c ⊢M ⟨ refl , refl ⟩) = 
    coerce-sound-⊇ c V v ρ scρ (λ i d d∈ ()) ⊢V
  𝒪-sound-⊇ (wrap v) scρ ρ∶Γ Γ⊢M∶A = λ d z → z

  -}