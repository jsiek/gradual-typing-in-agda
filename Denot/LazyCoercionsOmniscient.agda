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
      proj-ok : ∀ {B ℓ D u} → u ∈ D → (nbu : ¬isBlame u) → ⟦ u ∶ B ⟧ → u ∈ Proj B ℓ D
      proj-fail : ∀ {B ℓ D u} → u ∈ D → (nbu : ¬isBlame u) → ¬ ⟦ u ∶ B ⟧ → (blame ℓ) ∈ Proj B ℓ D
      proj-blame : ∀ {B ℓ ℓ' D} → (bl∈ : blame ℓ ∈ D) → blame ℓ ∈ Proj B ℓ' D


  data Fun-cast : (A' : Type) → (Fc : 𝒫 Val → 𝒫 Val) (Fd : 𝒫 Val → 𝒫 Val)
                → (F : 𝒫 Val → 𝒫 Val) → 𝒫 Val
    FC-↦ : ∀ {A' Fc Fd F V w}
          → ⟦ V ∶ A' ⟧₊
          → (scV : scD (mem V))
          → (nbV : ¬isBlame-∈ (mem V))
          → w ∈ (Fd (F (Fc (mem V))))
          → V ↦ w ∈ Fun-cast A' Fc Fd F
    Fc-ν : ∀{A' Fc Fd F} → ν ∈ FC-↦ A' Fc Fd F
    Fc-blame-dom : ∀ {A' Fc Fd F V ℓ}
          → (nbV )
          → blame ℓ ∈ Fc (mem V)
          → blame ℓ ∈ Fun-cast A' Fc Fd F
    Fc-blame-cod : ?
    
    -blame : ∀{A f V ℓ}
        → (bl∈ : blame ℓ ∈ f (mem V))
        → (V∶A : ⟦ V ∶ A ⟧₊)
        → (nbV : ¬isBlame₊ V)
        → (neV : V ≢ [])  {- call by value -}
        → blame ℓ ∈ Λ A f
    

  𝒞_⟨_⟩ : ∀ {A B} → (D : 𝒫 Val) → (c : Cast (A ⇒ B)) → 𝒫 Val
  𝒞 D ⟨ id ⟩ = D
  𝒞 D ⟨ _!! A {j} ⟩ = D
  𝒞 D ⟨ (B ?? ℓ) {¬⋆} ⟩ = Proj B ℓ D
  𝒞_⟨_⟩ {A ⇒ B} {A' ⇒ B'} D (c ↣ d) = (Λ A' (λ X → 𝒞 (D ∗ (𝒞 X ⟨ c ⟩)) ⟨ d ⟩))
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

  β-⊇ : ∀ {A} (F : 𝒫 Val → 𝒫 Val) D
    → (D∶A : ∈⟦ D ∶ A ⟧)
    → (scD : scD D)
    → (nbD : ¬isBlame-∈ D)
    → (F-cont : ∀ D' d → d ∈ F D' → Σ[ V ∈ List Val ] (mem V) ⊆ D' × d ∈ F (mem V) × V ≢ [])
    → F D ⊆ ((Λ A F) ∗ D)
  β-⊇ {A} F D D∶A scD nbD F-cont d d∈ with F-cont D d d∈
  ... | ⟨ V , ⟨ V⊆ , ⟨ d∈' , neV ⟩ ⟩ ⟩ = {!   !}
    {- ∗-app {V = V} (Λ-↦ d∈' (∈→⟦∶⟧₊ (λ d z → D∶A d (V⊆ d z))) 
      (nb∈mem→nb₊ (λ d z → nbD d (V⊆ d z))) (λ u v z z₁ → scD u v (V⊆ u z) (V⊆ v z₁)) neV) V⊆ -}

  coerce-sound-⊇ : ∀ {A B Γ}
                 → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ∀ V → (vV : Value V) 
                 → ∀ ρ → (scρ : ∀ i → scD (ρ i)) → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) 
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) 
                 → 𝒪⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ (𝒞_⟨_⟩ (𝒪⟦ V ⟧ ρ) c)
  coerce-sound-⊇ {A}{.A}{Γ} id V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ = v∈
  coerce-sound-⊇ {.⋆}{B}{Γ} (_??_ .B x {j}) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ 
    with canonical⋆ Γ⊢V∶A vV
  ... | ⟨ A' , ⟨ M , ⟨ (_!! A' {j'}) , ⟨ i , ⟨ Γ⊢M∶A' , 𝐶⊢-blame ⟩ ⟩ ⟩ ⟩ ⟩ = {!   !}
  coerce-sound-⊇ {A ⇒ B}{A' ⇒ B'}{Γ} (c ↣ d) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈
    with V | vV | Γ⊢V∶A
  ... | (ƛ A ˙ N) | vV | (⊢ƛ A ⊢N ⟨ refl , refl ⟩) = 
    β-⊇  (λ z → Λ A' (λ z₁ → 𝒞 z ∗ 𝒞 z₁ ⟨ c ⟩ ⟨ d ⟩)) (Λ A (λ X → 𝒪⟦ N ⟧ (X • ρ))) 
          (𝒪-wt (ƛ A ˙ N) ρ {Γ = Γ} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩)) 
          (𝒪-scD (ƛ A ˙ N) ρ scρ) (¬isBlame-∈-Λ A (λ X → 𝒪⟦ N ⟧ (X • ρ))) 
       {!   !} 
       v 
       {!   !} {- (Λ-mono (λ X X' scX' X⊆ → 𝒞-mono d 
          (∗-scD (Λ-scD A (λ X scX → 𝒪-scD N (X • ρ) 
                    (λ {zero → scX ; (suc i) → scρ i}))) (𝒞-scD c scX')) 
          (∗-mono (Λ-scD A (λ X scX → 𝒪-scD  N (X • ρ) 
                    (λ {zero → scX ; (suc i) → scρ i}))) (𝒞-scD c scX') 
                  (Λ-mono (λ X X' scX' X⊆ → rebind N X⊆)) 
                  (𝒞-mono c scX' X⊆))) v v∈) -} 
  ... | ($ f # (P-Fun P)) | vV | (⊢$ f (P-Fun {ι}{τ} P) refl) = 
     β-⊇ (λ z → Λ A' (λ z₁ → 𝒞 z ∗ 𝒞 z₁ ⟨ c ⟩ ⟨ d ⟩)) (℘ (P-Fun P) f) 
         (𝒪-wt ($ f # (P-Fun P)) ρ {` ι ⇒ τ}{Γ} ρ∶Γ (⊢$ f (P-Fun P) refl)) 
         ℘-scD (¬isBlame-∈-℘ (P-Fun P) f) 
         {!   !} 
         v v∈
  ... | ⟦ M , N ⟧ | vV | (⊢cons ⊢M ⊢N ())
  ... | (inl M other B) | vV | (⊢inl B ⊢M ())
  ... | (inr M other A) | vV | (⊢inr A ⊢M ())
  ... | (M ⟨ c₁ ₍ I-inj ₎⟩) | vV | (⊢wrap c₁ I-inj ⊢M ⟨ eq₁ , () ⟩)
  coerce-sound-⊇ {(A `× B)}{(A' `× B')}{Γ} (c `× c₁) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ = v∈
  coerce-sound-⊇ {(A `⊎ B)}{(A' `⊎ B')}{Γ} (c `+ c₁) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ = v∈
  coerce-sound-⊇ {A}{B}{Γ}(⊥ .A ⟨ x ⟩ .B) V vV ρ scρ ρ∶Γ Γ⊢V∶A (blame ℓ) v∈ with neValue V ρ vV
  ... | ⟨ d , ⟨ d∈ , nbd ⟩ ⟩  = inj₂ ⟨ d , ⟨ d∈ , ⟨ nbd , v∈ ⟩ ⟩ ⟩


  postulate
    subst-⊇ : ∀ M N ρ → 𝒪⟦ _[_] M N ⟧ ρ ⊆ 𝒪⟦ M ⟧ ((𝒪⟦ N ⟧ ρ) • ρ)
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
  𝒪-sound-⊇ {M · N}{N'}{ρ} (β x) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-⊇' d (subst-⊇ {!  M !} {!   !} ρ d {!   !})
  𝒪-sound-⊇ δ scρ ρ∶Γ Γ⊢M∶A = δ-⊇
  𝒪-sound-⊇ β-if-true scρ ρ∶Γ Γ⊢M∶A = β-if-true-⊇
  𝒪-sound-⊇ β-if-false scρ ρ∶Γ Γ⊢M∶A = β-if-false-⊇
  𝒪-sound-⊇ (β-fst vM vN) scρ ρ∶Γ Γ⊢M∶A = β-fst-⊇
  𝒪-sound-⊇ (β-snd vM vN) scρ ρ∶Γ Γ⊢M∶A = β-snd-⊇
  𝒪-sound-⊇ {M}{N}{ρ}(β-caseL vT) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-caseL-⊇ d (subst-⊇ {! M !} {!   !} {!   !} d d∈)
  𝒪-sound-⊇ {M}{N}{ρ}(β-caseR vT) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-caseR-⊇ d (subst-⊇ {!   !} {!   !} {!   !} d {!   !})
  𝒪-sound-⊇ {V ⟨ c ⟩} {ρ = ρ} (cast ⊢V v) scρ ρ∶Γ (⊢cast c ⊢M ⟨ refl , refl ⟩) = 
    {!   !}
  𝒪-sound-⊇ (wrap v) scρ ρ∶Γ Γ⊢M∶A = λ d z → z