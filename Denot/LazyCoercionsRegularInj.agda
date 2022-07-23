open import Data.Nat
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app;
            inspect; [_])
open import Level using (lower)

module Denot.LazyCoercionsRegularInj where

  open import Types
  open import Labels
  open import CastStructureABT
  open import LazyCoercionsABT
  open import LazyCoercions using (I-inj; coerce-aux)
  open import Denot.ValueInj
  open import Denot.OpRegularInj
  open import Denot.ConsisRegularInj
  open import SetsAsPredicates
  open import Syntax hiding (id)

{-
  coerce : (A : Type) → (B : Type) → Label → Cast (A ⇒ B)
  coerce-aux : ∀{A B : Type} → A ⌣ B → Label → Cast (A ⇒ B)

  coerce A B ℓ
      with (A `⌣ B)
  ... | yes d = coerce-aux d ℓ
  ... | no _ = ⊥ A ⟨ ℓ ⟩ B


  coerce-aux {B = B} unk⌣L ℓ with eq-unk B
  ... | yes eq rewrite eq = id {a = A-Unk}
  ... | no neq = (B ?? ℓ) {j = neq}
  coerce-aux {A = A} unk⌣R ℓ  with eq-unk A
  ... | yes eq rewrite eq = id {a = A-Unk}
  ... | no neq = (A !!) {i = neq}
  coerce-aux base⌣ ℓ = id {a = A-Base}
  coerce-aux (fun⌣{A₁}{A₂}{B₁}{B₂}) ℓ =
    (coerce B₁ A₁ (flip ℓ)) ↣ (coerce A₂ B₂ ℓ)
  coerce-aux (pair⌣{A₁}{A₂}{B₁}{B₂}) ℓ = (coerce A₁ B₁ ℓ) `× (coerce A₂ B₂ ℓ)
  coerce-aux (sum⌣{A₁}{A₂}{B₁}{B₂}) ℓ = (coerce A₁ B₁ ℓ) `+ (coerce A₂ B₂ ℓ)
-}


  data coerce-val : ∀ (A B : Type) (ℓ : Label) → (u : Val) → (v : Val) → Set
  data coerce-val-aux : ∀ A B (ℓ : Label) (A⌣B : A ⌣ B) → (u : Val) → (v : Val) → Set
  
  data coerce-val where
    coerce-ok : ∀ {A B ℓ u v} → (A⌣B : A ⌣ B) → (nbu : ¬isBlame u) → (u↝v : coerce-val-aux A B ℓ A⌣B u v) → coerce-val A B ℓ u v
    coerce-fail : ∀ {A B ℓ u} → (¬A⌣B : ¬ (A ⌣ B)) → (nbu : ¬isBlame u) → coerce-val A B ℓ u (blame ℓ)
    coerce-pass : ∀ {A B ℓ ℓ'} → coerce-val A B ℓ (blame ℓ') (blame ℓ')

{- In the "regular" semantics:

failures or blame in the codomain coercion: 
  Proj ℓ (Int ⇒ Int) (Inj (Int ⇒ Bool) ([0] ↦ true))
  should produce [0] ↦  blame ℓ
  
  Proj ℓ (Int ⇒ Int) (Inj (⋆ ⇒ ⋆) ([0] ↦ blame ℓ'))
  should produce [0] ↦ blame ℓ'

failures in the domain coercion:
  Proj ℓ (Int ⇒ Int) (Inj (Bool ⇒ _) ([true] ↦ blame ℓ'))
  should produce [0] ↦ blame ℓ

  Proj ℓ (Int ⇒ Int) (Inj (⋆ ⇒ _) ([true] ↦ blame ℓ'))
  should produce [0] ↦ blame ℓ

failure in the codomain cast coincides with blame from the body
  Proj ℓ (Int ⇒ Int) (Inj (Int ⇒ Bool) ([0] ↦ blame ℓ'))
  should produce [0] ↦ blame ℓ'
-}

  data coerce-val-aux where
    coerce-const : ∀ {ι k ℓ}  → coerce-val-aux (` ι) (` ι) ℓ base⌣ (const {ι} k) (const k)
    coerce-ν : ∀ {A B A' B' ℓ} → coerce-val-aux (A ⇒ B) (A' ⇒ B') ℓ fun⌣ ν ν
    coerce-fun-ok : ∀ {A B A' B' ℓ V w V' w'} 
      → (∀ v → v ∈ mem V → Σ[ v' ∈ Val ] v' ∈ mem V' × coerce-val A' A (flip ℓ) v' v) -- coerce-val₊ A' A ℓ V (inj₁ V')
      → coerce-val B B' ℓ w w'
      → coerce-val-aux (A ⇒ B) (A' ⇒ B') ℓ fun⌣ (V ↦ w) (V' ↦ w')
    coerce-fun-fail-dom : ∀ {A B A' B' ℓ v V' v' ℓ'}
      → ⟦ V' ∶ A' ⟧₊ → scD (mem V')  -- might also need a "scD V'" condition 
      → v' ∈ mem V' → coerce-val A' A (flip ℓ) v' (blame ℓ') -- coerce-val₊ A' A ℓ V (inj₂ ℓ')
      → coerce-val-aux (A ⇒ B) (A' ⇒ B') ℓ fun⌣ v (V' ↦ blame ℓ')
    coerce-fun-fail-cod : ∀ {A B A' B' ℓ V w V' ℓ'}
      → (∀ v → v ∈ mem V → Σ[ v' ∈ Val ] v' ∈ mem V' × coerce-val A' A (flip ℓ) v' v) -- coerce-val₊ A' A ℓ V (inj₁ V') 
      → coerce-val B B' ℓ w (blame ℓ') 
      → coerce-val-aux (A ⇒ B) (A' ⇒ B') ℓ fun⌣ (V ↦ w) (V' ↦ blame ℓ')
    coerce-fst-ok : ∀ {A B A' B' ℓ u v}
      → coerce-val A A' ℓ u v
      → ¬isBlame v
      → coerce-val-aux (A `× B) (A' `× B') ℓ pair⌣ (fst u) (fst v)
    coerce-fst-fail : ∀ {A B A' B' ℓ u ℓ'}
      → coerce-val A A' ℓ u (blame ℓ')
      → coerce-val-aux (A `× B) (A' `× B') ℓ pair⌣ (fst u) (blame ℓ')
    coerce-snd-ok : ∀ {A B A' B' ℓ u v}
      → coerce-val B B' ℓ u v
      → ¬isBlame v
      → coerce-val-aux (A `× B) (A' `× B') ℓ pair⌣ (snd u) (snd v)
    coerce-snd-fail : ∀ {A B A' B' ℓ u ℓ'}
      → coerce-val B B' ℓ u (blame ℓ')
      → coerce-val-aux (A `× B) (A' `× B') ℓ pair⌣ (snd u) (blame ℓ')
    coerce-inl-ok : ∀ {A B A' B' ℓ U V} 
      → (∀ v → v ∈ mem V → Σ[ u ∈ Val ] u ∈ mem U × coerce-val A A' ℓ u v) -- coerce-val₊ A A' ℓ U (inj₁ V)
      → coerce-val-aux (A `⊎ B) (A' `⊎ B') ℓ sum⌣ (inl U) (inl V)
    coerce-inl-fail : ∀ {A B A' B' ℓ U u ℓ'}
      → u ∈ mem U → coerce-val A A' ℓ u (blame ℓ') -- coerce-val₊ A A' ℓ U (inj₂ ℓ')
      → coerce-val-aux (A `⊎ B) (A' `⊎ B') ℓ sum⌣ (inl U) (blame ℓ')
    coerce-inr-ok : ∀ {A B A' B' ℓ U V} 
      → (∀ v → v ∈ mem V → Σ[ u ∈ Val ] u ∈ mem U × coerce-val B B' ℓ u v) -- coerce-val₊ B B' ℓ U (inj₁ V)
      → coerce-val-aux (A `⊎ B) (A' `⊎ B') ℓ sum⌣ (inr U) (inr V)
    coerce-inr-fail : ∀ {A B A' B' ℓ U u ℓ'} 
      → u ∈ mem U → coerce-val B B' ℓ u (blame ℓ') -- coerce-val₊ B B' ℓ U (inj₂ ℓ')
      → coerce-val-aux (A `⊎ B) (A' `⊎ B') ℓ sum⌣ (inr U) (blame ℓ')

    -- probably a superfluous case
    coerce-blame : ∀ {A B ℓ A⌣B ℓ'} → coerce-val-aux A B ℓ A⌣B (blame ℓ') (blame ℓ')
    coerce-proj : ∀ {A B ℓ u v} 
                → ¬ (B ≡ ⋆) → coerce-val A B ℓ u v
                → coerce-val-aux ⋆ B ℓ unk⌣L (inj A u) v
    coerce-inj : ∀ {A ℓ v} → ¬ (A ≡ ⋆) → coerce-val-aux A ⋆ ℓ unk⌣R v (inj A v)
    coerce-dyn-L : ∀ {A ℓ v} → coerce-val-aux ⋆ ⋆ ℓ unk⌣L (inj A v) (inj A v)
    coerce-dyn-R : ∀ {A ℓ v} → coerce-val-aux ⋆ ⋆ ℓ unk⌣R (inj A v) (inj A v)


  data Proj : (B : Type) (ℓ : Label) (D : 𝒫 Val) → 𝒫 Val where
      proj-ok : ∀ {A B ℓ D u v} → (nbu : ¬isBlame u) → (inj∈ : inj A u ∈ D) → (u↝v : coerce-val A B ℓ u v) → v ∈ Proj B ℓ D
      proj-blame : ∀ {B ℓ ℓ' D} → (bl∈ : blame ℓ ∈ D) → blame ℓ ∈ Proj B ℓ' D

  Proj-mono : ∀ {B ℓ D D'} → D ⊆ D' → Proj B ℓ D ⊆ Proj B ℓ D'
  Proj-mono {B} {ℓ} {D} {D'} D⊆ d (proj-ok {A = A} {u = u} nbu inj∈ u↝v) = 
    proj-ok nbu (D⊆ (inj A u) inj∈) u↝v
  Proj-mono {B} {ℓ} {D} {D'} D⊆ (blame ℓ') (proj-blame bl∈) = proj-blame (D⊆ (blame ℓ') bl∈)

  ¬isBlame-∈-Λ : ∀ A F → ¬isBlame-∈ (Λ A F)
  ¬isBlame-∈-Λ A F .(_ ↦ _) (Λ-↦ w∈ V∶A nbV scV neV) = λ z → z
  ¬isBlame-∈-Λ A F .ν Λ-ν = λ z → z

  ¬isBlame-∈-$ : ∀ {A P f} → ¬isBlame-∈ (℘ {A} P f)
  ¬isBlame-∈-$ {P} {f} (const k) d∈ = λ z → z
  ¬isBlame-∈-$ {P} {f} (V ↦ d) d∈ = λ z → z
  ¬isBlame-∈-$ {P} {f} ν d∈ = λ z → z
  
  𝒞_⟨_⟩ : ∀ {A B} → (D : 𝒫 Val) → (c : Cast (A ⇒ B)) → 𝒫 Val
  𝒞 D ⟨ id ⟩ = D
  𝒞 D ⟨ _!! A {j} ⟩ = Inj A {¬⋆ = j} D
  𝒞 D ⟨ (B ?? ℓ) {¬⋆} ⟩ = Proj B ℓ D
  𝒞_⟨_⟩ {A ⇒ B} {A' ⇒ B'} D (c ↣ d) = (Λ (A ⇒ B) (λ D → (Λ A' (λ X → 𝒞 (D ∗ (𝒞 X ⟨ c ⟩)) ⟨ d ⟩)))) ∗ D
  𝒞 D ⟨ c `× d ⟩ = pair (𝒞 (car D) ⟨ c ⟩) (𝒞 (cdr D) ⟨ d ⟩)
  𝒞 D ⟨ c `+ d ⟩ = cond D (λ X → inleft (𝒞 X ⟨ c ⟩)) (λ Y → inright (𝒞 Y ⟨ d ⟩))
  𝒞 D ⟨ ⊥ A ⟨ ℓ ⟩ B ⟩ (blame ℓ') = blame ℓ' ∈ D ⊎ (Σ[ v ∈ Val ] v ∈ D × ¬isBlame v × ℓ' ≡ ℓ)
  𝒞 D ⟨ ⊥ A ⟨ ℓ ⟩ B ⟩ v = False

 
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

  𝒞-mono : ∀ {A B} (c : Cast (A ⇒ B)) {D D'} → scD D' → D ⊆ D' → 𝒞 D ⟨ c ⟩ ⊆ 𝒞 D' ⟨ c ⟩
  𝒞-mono {A} {.A} id {D} {D'} scD D⊆ = D⊆
  𝒞-mono {A} {.⋆} (_!! A {j}) {D} {D'} scD D⊆ = Inj-mono A {¬⋆ = j}{D}{D'} D⊆
  𝒞-mono {.⋆} {B} (.B ?? x) {D} {D'} scD D⊆ = Proj-mono D⊆
  𝒞-mono {(A ⇒ B)} {(A' ⇒ B')} (c ↣ d) {D} {D'} scDD' D⊆ = 
    ∗-mono (Λ-scD (A ⇒ B) (λ Y scY → Λ-scD A' (λ X scX → 𝒞-scD d (∗-scD scY (𝒞-scD c scX))))) 
           scDD' 
           (Λ-mono (λ Y Y' scY' Y⊆ → 
               Λ-mono (λ X X' scX' X⊆ → 𝒞-mono d (∗-scD scY' (𝒞-scD c scX')) 
                  (∗-mono scY' (𝒞-scD c scX') Y⊆ (𝒞-mono c scX' X⊆))))) 
           D⊆
    {-  -}
  𝒞-mono {(A `× B)} {(A' `× B')} (c `× d) {D} {D'} scD D⊆ = 
    pair-mono (𝒞-scD c (car-scD scD)) (𝒞-scD d (cdr-scD scD)) 
              (𝒞-mono c (car-scD scD) (car-mono scD D⊆)) 
              (𝒞-mono d (cdr-scD scD) (cdr-mono scD D⊆))
  𝒞-mono {(A `⊎ B)} {(A' `⊎ B')} (c `+ d) {D} {D'} scD D⊆ = 
    cond-mono scD D⊆ (λ X X' scX' X⊆ → inleft-mono (𝒞-scD c scX') (𝒞-mono c scX' X⊆)) 
                     (λ Y Y' scY' Y⊆ → inright-mono (𝒞-scD d scY') (𝒞-mono d scY' Y⊆))
  𝒞-mono {A} {B} (⊥ .A ⟨ ℓ ⟩ .B) {D} {D'} scD D⊆ (blame ℓ') (inj₁ x) = inj₁ (D⊆ (blame ℓ') x)
  𝒞-mono {A} {B} (⊥ .A ⟨ ℓ ⟩ .B) {D} {D'} scD D⊆ (blame ℓ') (inj₂ ⟨ v , ⟨ v∈D , ⟨ ¬blv  , refl ⟩ ⟩ ⟩) = inj₂ ⟨ v , ⟨ D⊆ v v∈D , ⟨ ¬blv , refl ⟩ ⟩ ⟩


{- this is only true of well-typed denotations... 
   it shouldn't be possible for a function denotation to contain shallow blame in this semantics. -}
  𝒞-blame : ∀ {D A B} (c : Cast (A ⇒ B)) {ℓ} → blame ℓ ∈ D → blame ℓ ∈ 𝒞 D ⟨ c ⟩
  𝒞-blame id bl∈D = bl∈D
  𝒞-blame (_!! _ {j}) bl∈D = inj-blame {¬⋆ = j} bl∈D
  𝒞-blame (_ ?? x) bl∈D = proj-blame bl∈D
  𝒞-blame {D}{A ⇒ B}{A' ⇒ B'} (c ↣ c₁) bl∈D = ∗-blame-rand (¬isBlame-∈-Λ (A ⇒ B) (λ z → Λ A' (λ z₁ → 𝒞 z ∗ 𝒞 z₁ ⟨ c ⟩ ⟨ c₁ ⟩))) bl∈D
  𝒞-blame (c `× c₁) bl∈D = pair-blame-fst (𝒞-blame c (car-blame bl∈D))
  𝒞-blame (c `+ c₁) bl∈D = cond-blame bl∈D
  𝒞-blame (⊥ _ ⟨ x ⟩ _) bl∈D = inj₁ bl∈D


  postulate
    𝒞-wt : ∀ {D A B} (c : Cast (A ⇒ B)) → ∈⟦ D ∶ A ⟧ → ∈⟦ 𝒞 D ⟨ c ⟩ ∶ B ⟧
  
  open import Denot.CastStructureRegularInj


  instance 
    dcs : DenotCastStruct
    dcs = record
            { cast = cs
            ; 𝒞 = λ c D → 𝒞 D ⟨ c ⟩ }




  open DenotCastStruct dcs using (⟦_⟧)

  _⟶_ = _—→_


  postulate
    ⟦⟧-scD : ∀ M ρ (scDρ : ∀ i → scD (ρ i)) → scD (⟦ M ⟧ ρ)
    ⟦⟧-mono : ∀ M ρ ρ' (monoρ : ∀ i → ρ i ⊆ ρ' i) → ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ'
    rebind : ∀ {X X' Y ρ} N → X ⊆ X' → ⟦ rename (ext suc) N ⟧ (X • Y • ρ) ⊆ ⟦ N ⟧ (X' • ρ)
    ⟦⟧-wt : ∀ M ρ {A Γ} → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) → (Γ⊢M∶A : Γ ⊢ M ⦂ A) → ∈⟦ ⟦ M ⟧ ρ ∶ A ⟧
    nb∈mem→nb₊ : ∀ {V} → ¬isBlame-∈ (mem V) → ¬isBlame₊ V
    ∈mem→ne : ∀ {A}{V : List A} v → v ∈ mem V → V ≢ []
    ne→∈mem : ∀ {A}{V : List A} → V ≢ [] → Σ[ a ∈ A ] a ∈ mem V
    ¬isBlame-∈-℘ : ∀ {B} (P : Prim B) f → ¬isBlame-∈ (℘ P f)
    neValue : ∀ V ρ → (vV : Value V) → Σ[ d ∈ Val ] d ∈ ⟦ V ⟧ ρ × ¬isBlame d
    car-wt : ∀ {D A B} → ∈⟦ D ∶ A `× B ⟧ → ∈⟦ car D ∶ A ⟧
    cdr-wt : ∀ {D A B} → ∈⟦ D ∶ A `× B ⟧ → ∈⟦ cdr D ∶ B ⟧

  
{- coerce-coerce-val₊   → V ⊆ D ⟨ coerce A A' ⟩ → U ⊆ D → coerce-val₊ U V -}

  coerce-coerce-val : ∀ D ℓ A A' → ∈⟦ D ∶ A ⟧
    → ∀ v → v ∈ 𝒞 D ⟨ coerce A A' ℓ ⟩ → Σ[ u ∈ Val ] u ∈ D × coerce-val A A' ℓ u v
  coerce-coerce-val D ℓ A A' D∶A v v∈coerceD
    with A `⌣ A' | v | v∈coerceD | 𝒞-wt (coerce A A' ℓ) D∶A v v∈coerceD 
  ... | yes unk⌣L | v' | v∈' | v∶A  with eq-unk A' | v' | v∈' | v∶A
  ... | yes refl | inj A v'' | v∈' | v∶A = ⟨ inj A v'' , ⟨ v∈' , coerce-ok unk⌣L (λ z → z) coerce-dyn-L ⟩ ⟩
  ... | yes refl | blame ℓ₁ | v∈' | v∶A = ⟨ blame ℓ₁ , ⟨ v∈' , coerce-pass ⟩ ⟩
  ... | no neq | v' | proj-ok {A = A''} {u = u} nbu inj∈ u↝v | v∶A = ⟨ inj A'' u , ⟨ inj∈ , coerce-ok unk⌣L (λ z → z) (coerce-proj neq u↝v) ⟩ ⟩
  ... | no neq | (blame ℓ₁) | proj-blame bl∈ | v∶A = ⟨ blame ℓ₁ , ⟨ bl∈ , coerce-pass ⟩ ⟩
  coerce-coerce-val D ℓ A A' D∶A v v∈coerceD | yes unk⌣R | v' | v∈' | v∶A  with eq-unk A | v' | v∈' | v∶A
  ... | yes 𝐶⊢-blame | inj A v'' | v∈' | v∶A = ⟨ inj A v'' , ⟨ v∈' , coerce-ok unk⌣L (λ z → z) coerce-dyn-L ⟩ ⟩
  ... | yes 𝐶⊢-blame | blame ℓ₁ | v∈' | v∶A = ⟨ blame ℓ₁ , ⟨ v∈' , coerce-pass ⟩ ⟩
  ... | no neq | (blame ℓ₁) | inj-blame x | v∶A = ⟨ blame ℓ₁ , ⟨ x , coerce-pass ⟩ ⟩
  ... | no neq | (inj A v'') | inj-ok nbv x x₁ | v∶A = ⟨ v'' , ⟨ x , coerce-ok unk⌣R nbv (coerce-inj neq) ⟩ ⟩
  coerce-coerce-val D ℓ A A' D∶A v v∈coerceD | yes (base⌣ {ι}) | const {B} k | v∈ | v∶A with base-eq? ι B | v∶A
  ... | yes refl | v∶A = ⟨ const k , ⟨ v∈ , coerce-ok base⌣ (λ z → z) coerce-const ⟩ ⟩
  ... | no neq | v∶A = ⊥-elim v∶A
  coerce-coerce-val D ℓ A A' D∶A v v∈coerceD | yes base⌣ | blame ℓ₁ | v∈' | v∶A = ⟨ blame ℓ₁ , ⟨ v∈' , coerce-pass ⟩ ⟩
  coerce-coerce-val D ℓ (A ⇒ B) (A' ⇒ B') D∶A v v∈coerceD | yes fun⌣ | V ↦ w 
     | ∗-app nbrator nbrand (Λ-↦ {V = V'} (Λ-↦ {V = V} w∈ V∶A' nbV₁ scV₁ neV₁) V'∶A⇒B nbV scV neV) V⊆ | V∶A'→w∶B' 
     with coerce-coerce-val (mem V' ∗ 𝒞 (mem V) ⟨ coerce A' A (flip ℓ) ⟩) ℓ B B' {!   !} w w∈
  ... | ⟨ (blame ℓ') , ⟨ ∗-blame-rator bl∈ , w'↝w ⟩ ⟩ = ⊥-elim (nbrand (blame ℓ') (V⊆ (blame ℓ') bl∈) tt)
  ... | ⟨ blame ℓ' , ⟨ ∗-blame-rand nbrator₁ bl∈ , coerce-ok A⌣B nbu u↝v ⟩ ⟩ = ⊥-elim (nbu tt)
  ... | ⟨ blame ℓ' , ⟨ ∗-blame-rand nbrator₁ bl∈ , coerce-fail ¬A⌣B nbu ⟩ ⟩ = ⊥-elim (nbu tt)
  ... | ⟨ w' , ⟨ ∗-app {V = V''} nbrator₁ nbrand₁ V↦w∈ V⊆₁ , w'↝w ⟩ ⟩ = 
    ⟨ V'' ↦ w' , ⟨ V⊆  (V'' ↦ w') V↦w∈ 
    , coerce-ok fun⌣ (λ z → z) (coerce-fun-ok (λ d d∈ → coerce-coerce-val (mem V) (flip ℓ) A' A (⟦∶⟧₊→∈ V∶A') d (V⊆₁ d d∈)) w'↝w) ⟩ ⟩
  ... | ⟨ blame ℓ' , ⟨ ∗-blame-rand nbrator₁ bl∈ , coerce-pass ⟩ ⟩ 
    with coerce-coerce-val (mem V) (flip ℓ) A' A (⟦∶⟧₊→∈ V∶A') (blame ℓ') bl∈
  ... | ⟨ u , ⟨ u∈ , u↝bl ⟩ ⟩ = 
    ⟨ proj₁ H , ⟨ proj₁ (proj₂ H) , coerce-ok fun⌣ (proj₂ (proj₂ H)) (coerce-fun-fail-dom V∶A' scV₁ u∈ u↝bl) ⟩ ⟩
      where
      H : Σ[ d ∈ Val ] D d × ¬isBlame d
      H with ne→∈mem neV 
      ... | ⟨ a , a∈V' ⟩ = ⟨ a , ⟨ V⊆ a a∈V' , nbrator₁ a a∈V' ⟩ ⟩
  coerce-coerce-val D ℓ .(_ ⇒ _) .(_ ⇒ _) D∶A v v∈coerceD | yes fun⌣ | ν | ∗-app nbrator nbrand (Λ-↦ Λ-ν V∶A nbV scV neV) V⊆ | v∶A = 
    ⟨ ν , ⟨ {!   !}  , coerce-ok fun⌣ (λ z → z) coerce-ν ⟩ ⟩
  -- do we have to go back to syntax in order to get this function denotation to be nonempty?
  -- do we have to carry a nonemptiness property of function denotations through to this proof?
  coerce-coerce-val D ℓ .(_ ⇒ _) .(_ ⇒ _) D∶A v v∈coerceD | yes fun⌣ | blame ℓ₁ | ∗-blame-rand nbrator bl∈ | v∶A = ⟨ blame ℓ₁ , ⟨ bl∈ , coerce-pass ⟩ ⟩
  coerce-coerce-val D ℓ .(_ ⇒ _) .(_ ⇒ _) D∶A v v∈coerceD | yes fun⌣ | blame ℓ₁ | ∗-app nbrator nbrand (Λ-↦ () V∶A nbV scV neV) V⊆ | v∶A
  coerce-coerce-val D ℓ (A `× B) (A' `× B') D∶A v' v∈coerceD | yes pair⌣ | fst u | pair-fst {v = v} nbfst nbsnd u∈ v∈ | v∶A
    with coerce-coerce-val (car D) ℓ A A' (car-wt D∶A) u u∈ | nbfst u u∈
  ... | ⟨ .(blame _) , ⟨ car-blame bl∈ , coerce-ok A⌣B nbu u↝v ⟩ ⟩ | q = ⊥-elim (nbu tt)
  ... | ⟨ .(blame _) , ⟨ car-blame bl∈ , coerce-fail ¬A⌣B nbu ⟩ ⟩ | q = ⊥-elim (q tt)
  ... | ⟨ .(blame _) , ⟨ car-blame bl∈ , coerce-pass ⟩ ⟩ | q = ⊥-elim (q tt)
  ... | ⟨ u' , ⟨ car-fst nbD fstu∈ , u'↝u ⟩ ⟩ | _ = 
    ⟨ fst u' , ⟨ fstu∈ , coerce-ok pair⌣ (λ z → z) (coerce-fst-ok u'↝u (λ z → nbD (fst u') fstu∈ (nbfst u u∈ z))) ⟩ ⟩
  coerce-coerce-val D ℓ (A `× B) (A' `× B') D∶A v' v∈coerceD | yes pair⌣ | snd v | pair-snd {u = u} nbfst nbsnd u∈ v∈ | v∶A 
    with coerce-coerce-val (cdr D) ℓ B B' (cdr-wt D∶A) v v∈ | nbsnd v v∈
  ... | ⟨ .(blame _) , ⟨ cdr-blame bl∈ , coerce-ok A⌣B nbu u↝v ⟩ ⟩ | _ = ⊥-elim (nbu tt)
  ... | ⟨ .(blame _) , ⟨ cdr-blame bl∈ , coerce-fail ¬A⌣B nbu ⟩ ⟩ | q = ⊥-elim (q tt)
  ... | ⟨ .(blame _) , ⟨ cdr-blame bl∈ , coerce-pass ⟩ ⟩ | q = ⊥-elim (q tt)
  ... | ⟨ v' , ⟨ cdr-snd nbD sndv∈ , v'↝v ⟩ ⟩ | q = 
    ⟨ snd v' , ⟨ sndv∈ , coerce-ok pair⌣ (λ z → z) (coerce-snd-ok v'↝v q) ⟩ ⟩
  coerce-coerce-val D ℓ (A `× B) (A' `× B') D∶A v v∈coerceD | yes pair⌣ | blame ℓ₁ | pair-blame-fst bl∈ | v∶A 
     with coerce-coerce-val (car D) ℓ A A' (car-wt D∶A) (blame ℓ₁) bl∈
  ... | ⟨ .(blame _) , ⟨ car-blame bl∈₁ , coerce-ok A⌣B nbu u↝v ⟩ ⟩ = ⊥-elim (nbu tt)
  ... | ⟨ .(blame _) , ⟨ car-blame bl∈₁ , coerce-fail ¬A⌣B nbu ⟩ ⟩ = ⊥-elim (nbu tt)
  ... | ⟨ .(blame ℓ₁) , ⟨ car-blame bl∈₁ , coerce-pass ⟩ ⟩ = ⟨ blame ℓ₁ , ⟨ bl∈₁ , coerce-pass ⟩ ⟩
  ... | ⟨ u , ⟨ car-fst nbD fstu∈ , u↝v ⟩ ⟩ = ⟨ fst u , ⟨ fstu∈ , coerce-ok pair⌣ (λ z → z) (coerce-fst-fail u↝v) ⟩ ⟩
  coerce-coerce-val D ℓ (A `× B) (A' `× B') D∶A v v∈coerceD | yes pair⌣ | blame ℓ₁ | pair-blame-snd nbfst bl∈ | v∶A
    with coerce-coerce-val (cdr D) ℓ B B' (cdr-wt D∶A) (blame ℓ₁) bl∈
  ... | ⟨ .(blame _) , ⟨ cdr-blame bl∈₁ , coerce-ok A⌣B nbu u↝v ⟩ ⟩ = ⊥-elim (nbu tt)
  ... | ⟨ .(blame _) , ⟨ cdr-blame bl∈₁ , coerce-fail ¬A⌣B nbu ⟩ ⟩ = ⊥-elim (nbu tt)
  ... | ⟨ .(blame ℓ₁) , ⟨ cdr-blame bl∈₁ , coerce-pass ⟩ ⟩ = ⟨ blame ℓ₁ , ⟨ bl∈₁ , coerce-pass ⟩ ⟩
  ... | ⟨ u , ⟨ cdr-snd nbD sndv∈ , u↝v ⟩ ⟩ = ⟨ snd u , ⟨ sndv∈ , coerce-ok pair⌣ (λ z → z) (coerce-snd-fail u↝v) ⟩ ⟩
  coerce-coerce-val D ℓ (A `⊎ B) (A' `⊎ B') D∶A v v∈coerceD | yes sum⌣ | inl V | cond-inl {V = V'} nbD LV∈ (inleft-inl nbD₁ V⊆) | v∶A = 
    ⟨ inl V' , ⟨ LV∈ , coerce-ok sum⌣ (λ z → z) (coerce-inl-ok (λ d d∈ → coerce-coerce-val (mem V') ℓ A A' (⟦∶⟧₊→∈ (D∶A (inl V') LV∈)) d (V⊆ d d∈))) ⟩ ⟩
  coerce-coerce-val D ℓ (A `⊎ B) (A' `⊎ B') D∶A v v∈coerceD | yes sum⌣ | inr V | cond-inr {V = V'} nbD RV∈ (inright-inr nbD₁ V⊆) | v∶A = 
    ⟨ inr V' , ⟨ RV∈ , coerce-ok sum⌣ (λ z → z) (coerce-inr-ok (λ d d∈ → coerce-coerce-val (mem V') ℓ B B' (⟦∶⟧₊→∈ (D∶A (inr V') RV∈)) d (V⊆ d d∈))) ⟩ ⟩
  coerce-coerce-val D ℓ (A `⊎ B) (A' `⊎ B') D∶A v v∈coerceD | yes sum⌣ | blame ℓ₁ | cond-blame x | v∶A = ⟨ blame ℓ₁ , ⟨ x , coerce-pass ⟩ ⟩
  coerce-coerce-val D ℓ (A `⊎ B) (A' `⊎ B') D∶A v v∈coerceD | yes sum⌣ | blame ℓ₁ | cond-inl {V = V} nbD LV∈ (inleft-blame bl∈) | v∶A 
     with coerce-coerce-val (mem V) ℓ A A' (⟦∶⟧₊→∈ (D∶A (inl V) LV∈)) (blame ℓ₁) bl∈
  ... | ⟨ u , ⟨ u∈ , u↝v ⟩ ⟩ = ⟨ inl V , ⟨ LV∈ , coerce-ok sum⌣ (λ z → z) (coerce-inl-fail u∈ u↝v) ⟩ ⟩
  coerce-coerce-val D ℓ (A `⊎ B) (A' `⊎ B') D∶A v v∈coerceD | yes sum⌣ | blame ℓ₁ | cond-inr {V = V} nbD RV∈ (inright-blame bl∈) | v∶A 
     with coerce-coerce-val (mem V) ℓ B B' (⟦∶⟧₊→∈ (D∶A (inr V) RV∈)) (blame ℓ₁) bl∈
  ... | ⟨ u , ⟨ u∈ , u↝v ⟩ ⟩ = ⟨ inr V , ⟨ RV∈ , coerce-ok sum⌣ (λ z → z) (coerce-inr-fail u∈ u↝v) ⟩ ⟩
  coerce-coerce-val D ℓ A A' D∶A v v∈coerceD | no ¬A⌣A' | blame ℓ₁ | inj₁ x | v∶A = ⟨ blame ℓ₁ , ⟨ x , coerce-pass ⟩ ⟩
  coerce-coerce-val D ℓ A A' D∶A v v∈coerceD | no ¬A⌣A' | blame ℓ₁ | inj₂ ⟨ u , ⟨ u∈ , ⟨ ¬blu , refl ⟩ ⟩ ⟩ | v∶A = ⟨ u , ⟨ u∈ , coerce-fail ¬A⌣A' ¬blu ⟩ ⟩


  coerce-⊆-proj-inj : ∀ {D A B}
     → (¬⋆A : ¬ (A ≡ ⋆)) → (¬⋆B : ¬ (B ≡ ⋆)) → (D∶A : ∈⟦ D ∶ A ⟧)
     → ∀ {ℓ} → 𝒞 D ⟨ coerce A B ℓ ⟩ ⊆ Proj B ℓ (Inj A D)
  coerce-⊆-proj-inj {D}{A}{B} ¬⋆A ¬⋆B D∶A {ℓ} d d∈
    with A `⌣ B | d | d∈ | coerce-coerce-val D ℓ A B D∶A d d∈
  ... | no ¬A⌣B | blame ℓ | inj₁ bl∈D | _ = proj-blame (inj-blame {¬⋆ = ¬⋆A} bl∈D)
  ... | no ¬A⌣B | blame ℓ | inj₂ ⟨ v , ⟨ v∈D , ⟨ ¬blv , refl ⟩ ⟩ ⟩ | _ = 
    proj-ok ¬blv (inj-ok {¬⋆ = ¬⋆A} ¬blv v∈D (D∶A v v∈D)) (coerce-fail ¬A⌣B ¬blv)
  ... | yes A⌣B | d' | d∈' |  ⟨ u , ⟨ u∈ , u↝v ⟩ ⟩ with blame? u
  ... | no nbu = proj-ok nbu (inj-ok nbu u∈ (D∶A u u∈)) u↝v
  ... | yes blu with u | u∈ | u↝v
  ... | blame ℓ' | u∈ | coerce-ok A⌣B₁ nbu u↝v₁ = ⊥-elim (nbu tt)
  ... | blame ℓ' | u∈ | coerce-fail ¬A⌣B nbu = ⊥-elim (nbu tt)
  ... | blame ℓ' | u∈ | coerce-pass = proj-blame (inj-blame u∈)
   -- coerce-aux-⊆-proj-inj ¬⋆A ¬⋆B A⌣B D∶A d d∈
  {-
  coerce-aux-⊆-proj-inj {D}{A}{B} ¬⋆A ¬⋆B A⌣B D∶A {ℓ} d d∈ with coerce A B ℓ
  ... | q with coerce-coerce-val D ℓ A B D∶A d {! q !}
  ... | ⟨ u , ⟨ u∈ , u↝v ⟩ ⟩ = proj-ok {!   !} (inj-ok {!   !} u∈ (D∶A u u∈)) u↝v
    where
    H : {!   !}
    H = {!   !}
  coerce-aux-⊆-proj-inj {D}{A}{B} ¬⋆A ¬⋆B unk⌣L D∶A d d∈ = ⊥-elim (¬⋆A refl)
  coerce-aux-⊆-proj-inj {D}{A}{B} ¬⋆A ¬⋆B unk⌣R D∶A d d∈ = ⊥-elim (¬⋆B refl)
  coerce-aux-⊆-proj-inj {D}{A}{B} ¬⋆A ¬⋆B (base⌣ {ι}) D∶A d d∈ with d | d∈ | D∶A d d∈
  ... | blame ℓ | bl∈ | bl∶A = proj-blame (inj-blame {¬⋆ = ¬⋆A} bl∈)
  ... | const {B} k | k∈ | k∶A  with base-eq? ι B
  ... | yes refl = proj-ok (λ z → z) (inj-ok {¬⋆ = ¬⋆A} (λ z → z) k∈ k∶A') (coerce-ok base⌣ (λ z → z) coerce-const)
          where
          k∶A' : ⟦ const k ∶ ` B ⟧
          k∶A' with base-eq? B B
          ... | no neq = ⊥-elim (neq refl)
          ... | yes refl = tt
  ... | no neq = ⊥-elim k∶A
  coerce-aux-⊆-proj-inj {D}{A}{B} ¬⋆A ¬⋆B fun⌣ D∶A d d∈ = {!  !}
  coerce-aux-⊆-proj-inj {D} {(A `× B)} {(A' `× B')} ¬⋆A ¬⋆B pair⌣ D∶A {ℓ} (blame ℓ') (pair-blame-fst bl∈) = {!  !}
  coerce-aux-⊆-proj-inj {D} {(A `× B)} {(A' `× B')} ¬⋆A ¬⋆B pair⌣ D∶A {ℓ} (blame ℓ') (pair-blame-snd nbfst bl∈) = {!  !}
  coerce-aux-⊆-proj-inj {D} {(A `× B)} {(A' `× B')} ¬⋆A ¬⋆B pair⌣ D∶A {ℓ} (fst u) (pair-fst {v = v} nbfst nbsnd u∈ v∈) = {!  !}
  coerce-aux-⊆-proj-inj {D} {(A `× B)} {(A' `× B')} ¬⋆A ¬⋆B pair⌣ D∶A {ℓ} (snd v) (pair-snd {u = u} nbfst nbsnd u∈ v∈) = {!   !}
  coerce-aux-⊆-proj-inj {D}{A}{B} ¬⋆A ¬⋆B sum⌣ D∶A .(blame _) (cond-blame x) = proj-blame (inj-blame {¬⋆ = ¬⋆A} x)
  coerce-aux-⊆-proj-inj {D}{A `⊎ B}{A' `⊎ B'} ¬⋆A ¬⋆B sum⌣ D∶A {ℓ} (blame ℓ') (cond-inl {V = V} nbD LV∈ (inleft-blame bl∈)) 
    with coerce-coerce-val (mem V) ℓ A A' (⟦∶⟧₊→∈ (D∶A (inl V) LV∈)) (blame ℓ') bl∈
  ... | ⟨ u , ⟨ u∈ , u↝bl ⟩ ⟩ = proj-ok (λ z → z) (inj-ok (λ z → z) LV∈ (D∶A (inl V) LV∈)) (coerce-ok sum⌣ (λ z → z) (coerce-inl-fail u∈ u↝bl))
  coerce-aux-⊆-proj-inj {D}{A `⊎ B}{A' `⊎ B'} ¬⋆A ¬⋆B sum⌣ D∶A {ℓ} (inl V) (cond-inl {V = V'} nbD LV∈ (inleft-inl nbD₁ V⊆)) = 
    proj-ok (λ z → z) (inj-ok {¬⋆ = ¬⋆A} (λ z → z) LV∈ (∈→⟦∶⟧₊ λ d d∈ → ⟦∶⟧₊→∈ (D∶A (inl V') LV∈) d d∈)) 
            (coerce-ok sum⌣ (λ z → z) (coerce-inl-ok λ d d∈ → coerce-coerce-val (mem V') ℓ A A' (⟦∶⟧₊→∈ (D∶A (inl V') LV∈)) d (V⊆ d d∈)))
  coerce-aux-⊆-proj-inj {D}{A `⊎ B}{A' `⊎ B'} ¬⋆A ¬⋆B sum⌣ D∶A {ℓ} (blame ℓ') (cond-inr {V = V} nbD RV∈ (inright-blame bl∈)) 
    with coerce-coerce-val (mem V) ℓ B B' (⟦∶⟧₊→∈ (D∶A (inr V) RV∈)) (blame ℓ') bl∈
  ... | ⟨ u , ⟨ u∈ , u↝bl ⟩ ⟩ = proj-ok (λ z → z) (inj-ok (λ z → z) RV∈ (D∶A (inr V) RV∈)) (coerce-ok sum⌣ (λ z → z) (coerce-inr-fail u∈ u↝bl))
  coerce-aux-⊆-proj-inj {D}{A `⊎ B}{A' `⊎ B'} ¬⋆A ¬⋆B sum⌣ D∶A {ℓ} (inr V) (cond-inr {V = V'} nbD RV∈ (inright-inr nbD₁ V⊆)) = 
    proj-ok (λ z → z) (inj-ok {¬⋆ = ¬⋆A} (λ z → z) RV∈ (∈→⟦∶⟧₊ λ d d∈ → ⟦∶⟧₊→∈ (D∶A (inr V') RV∈) d d∈))
            (coerce-ok sum⌣ (λ z → z) (coerce-inr-ok λ d d∈ → coerce-coerce-val (mem V') ℓ B B' (⟦∶⟧₊→∈ (D∶A (inr V') RV∈)) d (V⊆ d d∈))) 
-}

{- 

V ⊆ 𝒞 V' ⟨ coerce B B' ℓ ⟩
==>
V ⊆ `map (coerce-val B B' ℓ) V'


-}

{-
  coerce-⊆-proj-inj : ∀ {D A B} → (D∶A : ∈⟦ D ∶ A ⟧)
     → ∀ {ℓ} → 𝒞 D ⟨ coerce A B ℓ ⟩ ⊆ Proj B ℓ (Inj A D)
  coerce-aux-⊆-proj-inj : ∀ {D A B} → (A⌣B : A ⌣ B) → (D∶A : ∈⟦ D ∶ A ⟧)
     → ∀ {ℓ} → 𝒞 D ⟨ coerce-aux A⌣B ℓ ⟩ ⊆ Proj B ℓ (Inj A D)
  coerce-⊆-proj-inj {D}{A}{B} D∶A d d∈
    with A `⌣ B | d | d∈
  ... | yes A⌣B | d | d∈ = coerce-aux-⊆-proj-inj A⌣B D∶A d d∈
  ... | no ¬A⌣B | blame ℓ | inj₁ bl∈D = proj-blame (inj-blame bl∈D)
  ... | no ¬A⌣B | blame ℓ | inj₂ ⟨ v , ⟨ v∈D , ⟨ ¬blv , refl ⟩ ⟩ ⟩ = proj-ok ¬blv (inj-ok v∈D (D∶A v v∈D)) (coerce-fail ¬A⌣B)
  coerce-aux-⊆-proj-inj unk⌣L D∶A d d∈ = {!   !}
  coerce-aux-⊆-proj-inj unk⌣R D∶A d d∈ = {!   !}
  coerce-aux-⊆-proj-inj (base⌣ {ι}) D∶A d d∈ with d | d∈ | D∶A d d∈
  ... | blame ℓ | bl∈ | bl∶A = proj-blame (inj-blame bl∈)
  ... | const {B} k | k∈ | k∶A  with base-eq? ι B
  ... | yes refl = proj-ok {!   !} (inj-ok k∈ k∶A') (coerce-ok base⌣ coerce-const)
          where
          k∶A' : ⟦ const k ∶ ` B ⟧
          k∶A' with base-eq? B B
          ... | no neq = ⊥-elim (neq refl)
          ... | yes refl = tt
  ... | no neq = ⊥-elim k∶A
  coerce-aux-⊆-proj-inj fun⌣ D∶A d d∈ = {!   !}
  coerce-aux-⊆-proj-inj pair⌣ D∶A d d∈ = {!   !}
  coerce-aux-⊆-proj-inj sum⌣ D∶A .(blame _) (cond-blame x) = proj-blame (inj-blame x)
  coerce-aux-⊆-proj-inj sum⌣ D∶A .(blame _) (cond-inl nbD LV∈ (inleft-blame bl∈)) = {!   !}
  coerce-aux-⊆-proj-inj sum⌣ D∶A (inl V) (cond-inl {V = V'} nbD LV∈ (inleft-inl nbD₁ V⊆)) = 
    proj-ok (λ z → z) (inj-ok LV∈ (∈→⟦∶⟧₊ λ d d∈ → ⟦∶⟧₊→∈ (D∶A (inl V') LV∈) d d∈)) 
            (coerce-ok sum⌣ (coerce-inl-ok {!  LV∈ !}))
  coerce-aux-⊆-proj-inj sum⌣ D∶A .(blame _) (cond-inr nbD RV∈ (inright-blame bl∈)) = 
    {!   !}
  coerce-aux-⊆-proj-inj sum⌣ D∶A (inr V) (cond-inr {V = V'} nbD RV∈ (inright-inr nbD₁ V⊆)) = 
    proj-ok (λ z → z) (inj-ok RV∈ (∈→⟦∶⟧₊ λ d d∈ → ⟦∶⟧₊→∈ (D∶A (inr V') RV∈) d d∈))
            (coerce-ok sum⌣ (coerce-inr-ok {!   !})) 

-}
   

  β-⊇ : ∀ {A} (F : 𝒫 Val → 𝒫 Val) D
    → (D∶A : ∈⟦ D ∶ A ⟧)
    → (scD : scD D)
    → (nbD : ¬isBlame-∈ D)
    → (F-cont : ∀ D' d → d ∈ F D' → Σ[ V ∈ List Val ] (mem V) ⊆ D' × d ∈ F (mem V) × V ≢ [])
    → F D ⊆ ((Λ A F) ∗ D)
  β-⊇ {A} F D D∶A scD nbD F-cont d d∈ with F-cont D d d∈
  ... | ⟨ V , ⟨ V⊆ , ⟨ d∈' , neV ⟩ ⟩ ⟩ = 
    ∗-app {V = V} (¬isBlame-∈-Λ A F) nbD (Λ-↦ d∈' (∈→⟦∶⟧₊ (λ d z → D∶A d (V⊆ d z))) 
      (nb∈mem→nb₊ (λ d z → nbD d (V⊆ d z))) (λ u v z z₁ → scD u v (V⊆ u z) (V⊆ v z₁)) neV) V⊆

  coerce-sound-⊇ : ∀ {A B Γ}
                 → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ∀ V → (vV : Value V) 
                 → ∀ ρ → (scρ : ∀ i → scD (ρ i)) → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) 
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) 
                 → ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ 𝒞 (⟦ V ⟧ ρ) ⟨ c ⟩
  coerce-sound-⊇ {A}{.A}{Γ} id V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ = v∈
  coerce-sound-⊇ {.⋆}{B}{Γ} (_??_ .B x {j}) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈ 
    with canonical⋆ Γ⊢V∶A vV
  ... | ⟨ A' , ⟨ M , ⟨ (_!! A' {j'}) , ⟨ i , ⟨ Γ⊢M∶A' , 𝐶⊢-blame ⟩ ⟩ ⟩ ⟩ ⟩ = 
    coerce-⊆-proj-inj {⟦ M ⟧ ρ}{A'}{B} j' j (⟦⟧-wt M ρ ρ∶Γ Γ⊢M∶A') v v∈
  coerce-sound-⊇ {A ⇒ B}{A' ⇒ B'}{Γ} (c ↣ d) V vV ρ scρ ρ∶Γ Γ⊢V∶A v v∈
    with V | vV | Γ⊢V∶A
  ... | (ƛ A ˙ N) | vV | (⊢ƛ A ⊢N ⟨ refl , refl ⟩) = 
    β-⊇  (λ z → Λ A' (λ z₁ → 𝒞 z ∗ 𝒞 z₁ ⟨ c ⟩ ⟨ d ⟩)) (Λ A (λ X → ⟦ N ⟧ (X • ρ))) 
          (⟦⟧-wt (ƛ A ˙ N) ρ {Γ = Γ} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩)) 
          (⟦⟧-scD (ƛ A ˙ N) ρ scρ) (¬isBlame-∈-Λ A (λ X → ⟦ N ⟧ (X • ρ))) 
       {!   !} 
       v 
       (Λ-mono (λ X X' scX' X⊆ → 𝒞-mono d 
          (∗-scD (Λ-scD A (λ X scX → ⟦⟧-scD N (X • ρ) 
                    (λ {zero → scX ; (suc i) → scρ i}))) (𝒞-scD c scX')) 
          (∗-mono (Λ-scD A (λ X scX → ⟦⟧-scD  N (X • ρ) 
                    (λ {zero → scX ; (suc i) → scρ i}))) (𝒞-scD c scX') 
                  (Λ-mono (λ X X' scX' X⊆ → rebind N X⊆)) 
                  (𝒞-mono c scX' X⊆))) v v∈)
  ... | ($ f # (P-Fun P)) | vV | (⊢$ f (P-Fun {ι}{τ} P) refl) = 
     β-⊇ (λ z → Λ A' (λ z₁ → 𝒞 z ∗ 𝒞 z₁ ⟨ c ⟩ ⟨ d ⟩)) (℘ (P-Fun P) f) 
         (⟦⟧-wt ($ f # (P-Fun P)) ρ {` ι ⇒ τ}{Γ} ρ∶Γ (⊢$ f (P-Fun P) refl)) 
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
    subst-⊇ : ∀ M N ρ → ⟦ _[_] M N ⟧ ρ ⊆ ⟦ M ⟧ ((⟦ N ⟧ ρ) • ρ)
    ξ-⊇ : ∀ {A B M N ρ} (F : Frame A B) → M ⟶ N → ⟦ plug N F ⟧ ρ ⊆ ⟦ plug M F ⟧ ρ
    ξ-blame-⊇ : ∀ {A B} (F : Frame A B) {ℓ ρ} → ℬ ℓ ⊆ ⟦ plug (mkblame A ℓ) F ⟧ ρ
    β-⊇' : ∀ {A F D} → F D ⊆ ((Λ A F) ∗ D)
    δ-⊇ : ∀ {A B} {a : Prim A} {b : Prim B} {ab : Prim (A ⇒ B)}{f k} → ℘ b (f k) ⊆ (℘ ab f  ∗ ℘ a k)
    β-if-true-⊇ : ∀ {P D E} → D ⊆ If (℘ P true) D E
    β-if-false-⊇ : ∀ {P D E} → E ⊆ If (℘ P false) D E
    β-fst-⊇ : ∀ {D E} → D ⊆ car (pair D E)
    β-snd-⊇ : ∀ {D E} → E ⊆ cdr (pair D E)
    β-caseL-⊇ : ∀ {D F G} → F D ⊆ cond (inleft D) F G
    β-caseR-⊇ : ∀ {D F G} → G D ⊆ cond (inright D) F G

 1. M ⟶ N   𝒪⟦ N ⟧ ρ ⊆ 𝒪⟦ M ⟧ ρ
 2. "⟦ N ⟧ ⊆ 𝒪⟦ N ⟧"  this applies to everything
 3. "𝒪 ⊆ ⟦⟧" for non-blame

  ⟦⟧-sound-⊇ : ∀ {M N ρ} → M ⟶ N
     → ∀ {Γ A} 
     → (scρ : ∀ i → scD (ρ i))
     → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) 
     → (Γ⊢M∶A : Γ ⊢ M ⦂ A)
     → ⟦ N ⟧ ρ ⊆ ⟦ M ⟧ ρ
  ⟦⟧-sound-⊇ (ξ {F = F} ⊢M M⟶N) scρ ρ∶Γ Γ⊢M∶A = ξ-⊇ F M⟶N
  ⟦⟧-sound-⊇ (ξ-blame {F = F}) scρ ρ∶Γ Γ⊢M∶A = ξ-blame-⊇ F
  ⟦⟧-sound-⊇ {M · N}{N'}{ρ} (β x) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-⊇' d (subst-⊇ {!   !} {!   !} ρ d d∈)
  ⟦⟧-sound-⊇ δ scρ ρ∶Γ Γ⊢M∶A = δ-⊇
  ⟦⟧-sound-⊇ β-if-true scρ ρ∶Γ Γ⊢M∶A = β-if-true-⊇
  ⟦⟧-sound-⊇ β-if-false scρ ρ∶Γ Γ⊢M∶A = β-if-false-⊇
  ⟦⟧-sound-⊇ (β-fst vM vN) scρ ρ∶Γ Γ⊢M∶A = β-fst-⊇
  ⟦⟧-sound-⊇ (β-snd vM vN) scρ ρ∶Γ Γ⊢M∶A = β-snd-⊇
  ⟦⟧-sound-⊇ {M}{N}{ρ}(β-caseL vT) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-caseL-⊇ d (subst-⊇ {!   !} {!   !} {!   !} d d∈)
  ⟦⟧-sound-⊇ {M}{N}{ρ}(β-caseR vT) scρ ρ∶Γ Γ⊢M∶A d d∈ = β-caseR-⊇ d (subst-⊇ {!   !} {!   !} {!   !} d d∈)
  ⟦⟧-sound-⊇ {V ⟨ c ⟩} {ρ = ρ} (cast ⊢V v) scρ ρ∶Γ (⊢cast c ⊢M ⟨ refl , refl ⟩) = 
    coerce-sound-⊇ c V v ρ scρ (λ i d d∈ρi bot → ⊥-elim (lower bot)) ⊢V
  ⟦⟧-sound-⊇ (wrap v) scρ ρ∶Γ Γ⊢M∶A = λ d z → z
