open import Data.Nat
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app;
            inspect; [_])

module Denot.LazyCoercionsRegularInj where

  open import Types
  open import Labels
  open import CastStructureABT
  open import LazyCoercionsABT
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

  postulate
    ∗-mono : ∀ {D E D' E'} → scD D' → scD E' → D ⊆ D' → E ⊆ E' → (D ∗ E) ⊆ (D' ∗ E')
    pair-mono : ∀ {D E D' E'} → scD D' → scD E' → D ⊆ D' → E ⊆ E' → (pair D E) ⊆ (pair D' E')
    car-mono : ∀ {D D'} → scD D' → D ⊆ D' → car D ⊆ car D'
    cdr-mono : ∀ {D D'} → scD D' → D ⊆ D' → cdr D ⊆ cdr D'
    inleft-mono : ∀ {D D'} → scD D' → D ⊆ D' → inleft D ⊆ inleft D'
    inright-mono : ∀ {D D'} → scD D' → D ⊆ D' → inright D ⊆ inright D'
    cond-mono : ∀ {T D E T' D' E'} → scD T' → T ⊆ T' 
      → (∀ a a' → a ⊆ a' → D a ⊆ D' a') → (∀ b b' → b ⊆ b' → E b ⊆ E' b') → cond T D E ⊆ cond T' D' E'
    If-mono : ∀ {T D E T' D' E'} → scD T' → T ⊆ T' → D ⊆ D' → E ⊆ E' → If T D E ⊆ If T' D' E'
  
  
  data coerce-val : ∀ (A B : Type) (ℓ : Label) → (u : Val) → (v : Val) → Set
  data coerce-val₊ : ∀ (A B : Type) (ℓ : Label) → (U : List Val) → (V⊎ℓ : List Val ⊎ Label) → Set
  data coerce-val-aux : ∀ A B (ℓ : Label) (A⌣B : A ⌣ B) → (u : Val) → (v : Val) → Set
  
  data coerce-val where
    coerce-ok : ∀ {A B ℓ u v} → (A⌣B : A ⌣ B) → coerce-val-aux A B ℓ A⌣B u v → coerce-val A B ℓ u v
    coerce-fail : ∀ {A B ℓ u} → ¬ (A ⌣ B) → coerce-val A B ℓ u (blame ℓ)
  
  data coerce-val₊ where
    [] : ∀ {A B ℓ} → coerce-val₊ A B ℓ [] (inj₁ [])
    _∷_ : ∀ {A B ℓ u U v V} 
        → coerce-val A B ℓ u v → coerce-val₊ A B ℓ U (inj₁ V) 
        → coerce-val₊ A B ℓ (u ∷ U) (inj₁ (v ∷ V))
    fail-car : ∀ {A B ℓ u U ℓ'}
        → coerce-val A B ℓ u (blame ℓ') 
        → coerce-val₊ A B ℓ (u ∷ U) (inj₂ ℓ')
    fail-cdr : ∀ {A B ℓ u U ℓ'}
        → coerce-val₊ A B ℓ U (inj₂ ℓ')
        → coerce-val₊ A B ℓ (u ∷ U) (inj₂ ℓ')

  data coerce-val-aux where
    coerce-const : ∀ {ι k ℓ}  → coerce-val-aux (` ι) (` ι) ℓ base⌣ (const {ι} k) (const k)
    coerce-ν : ∀ {A B A' B' ℓ} → coerce-val-aux (A ⇒ B) (A' ⇒ B') ℓ fun⌣ ν ν
    coerce-fun-ok : ∀ {A B A' B' ℓ V w V' w'} 
      → coerce-val₊ A' A ℓ V (inj₁ V') → coerce-val B B' ℓ w w'
      → coerce-val-aux (A ⇒ B) (A' ⇒ B') ℓ fun⌣ (V ↦ w) (V' ↦ w')
    coerce-fun-fail-dom : ∀ {A B A' B' ℓ V w V' ℓ'} 
      → coerce-val₊ A' A ℓ V (inj₂ ℓ') → ⟦ V' ∶ A' ⟧₊
      → coerce-val-aux (A ⇒ B) (A' ⇒ B') ℓ fun⌣ (V ↦ w) (V' ↦ blame ℓ')
    coerce-fun-fail-cod : ∀ {A B A' B' ℓ V w V' ℓ'}
      → coerce-val₊ A' A ℓ V (inj₁ V') → coerce-val B B' ℓ w (blame ℓ') 
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
      → coerce-val₊ A A' ℓ U (inj₁ V)
      → coerce-val-aux (A `⊎ B) (A' `⊎ B') ℓ sum⌣ (inl U) (inl V)
    coerce-inl-fail : ∀ {A B A' B' ℓ U ℓ'} 
      → coerce-val₊ A A' ℓ U (inj₂ ℓ')
      → coerce-val-aux (A `⊎ B) (A' `⊎ B') ℓ sum⌣ (inl U) (blame ℓ')
    coerce-inr-ok : ∀ {A B A' B' ℓ U V} 
      → coerce-val₊ B B' ℓ U (inj₁ V)
      → coerce-val-aux (A `⊎ B) (A' `⊎ B') ℓ sum⌣ (inr U) (inr V)
    coerce-inr-fail : ∀ {A B A' B' ℓ U ℓ'} 
      → coerce-val₊ B B' ℓ U (inj₂ ℓ')
      → coerce-val-aux (A `⊎ B) (A' `⊎ B') ℓ sum⌣ (inr U) (blame ℓ')
    coerce-blame : ∀ {A B ℓ A⌣B ℓ'} → coerce-val-aux A B ℓ A⌣B (blame ℓ') (blame ℓ')


  data Proj : (B : Type) (ℓ : Label) (D : 𝒫 Val) → 𝒫 Val where
      proj-ok : ∀ {A B ℓ D u v} → inj A u ∈ D → coerce-val A B ℓ u v → v ∈ Proj B ℓ D
      proj-blame : ∀ {B ℓ D} → blame ℓ ∈ D → blame ℓ ∈ Proj B ℓ D




  𝒞_⟨_⟩ : ∀ {A B} → (D : 𝒫 Val) → (c : Cast (A ⇒ B)) → 𝒫 Val
  𝒞 D ⟨ id ⟩ = D
  𝒞 D ⟨ A !! ⟩ = Inj A D
  𝒞 D ⟨ (B ?? ℓ) {¬⋆} ⟩ = Proj B ℓ D
  𝒞_⟨_⟩ {A ⇒ B} {A' ⇒ B'} D (c ↣ d) = Λ A' (λ X → 𝒞 (D ∗ (𝒞 X ⟨ c ⟩)) ⟨ d ⟩)
  𝒞 D ⟨ c `× d ⟩ = pair (𝒞 (car D) ⟨ c ⟩) (𝒞 (cdr D) ⟨ d ⟩)
  𝒞 D ⟨ c `+ d ⟩ = cond D (λ X → inleft (𝒞 X ⟨ c ⟩)) (λ Y → inright (𝒞 Y ⟨ d ⟩))
  𝒞 D ⟨ ⊥ A ⟨ ℓ ⟩ B ⟩ (blame ℓ') = blame ℓ' ∈ D ⊎ ℓ' ≡ ℓ
  𝒞 D ⟨ ⊥ A ⟨ ℓ ⟩ B ⟩ v = False


  𝒞-mono : ∀ {A B} (c : Cast (A ⇒ B)) {D D'} → scD D' → D ⊆ D' → 𝒞 D ⟨ c ⟩ ⊆ 𝒞 D' ⟨ c ⟩
  𝒞-mono {A} {.A} id {D} {D'} scD D⊆ = D⊆
  𝒞-mono {A} {.⋆} (.A !!) {D} {D'} scD D⊆ = Inj-mono A D⊆
  𝒞-mono {.⋆} {B} (.B ?? x) {D} {D'} scD D⊆ = {!   !}
  𝒞-mono {.(_ ⇒ _)} {.(_ ⇒ _)} (c ↣ d) {D} {D'} scD D⊆ = 
    Λ-mono (λ X X' X⊆ → 𝒞-mono d {!   !} (∗-mono {!   !} {!   !} D⊆ (𝒞-mono c {!   !} X⊆)))
  𝒞-mono {.(_ `× _)} {.(_ `× _)} (c `× c₁) {D} {D'} scD D⊆ = {!  !}
  𝒞-mono {.(_ `⊎ _)} {.(_ `⊎ _)} (c `+ c₁) {D} {D'} scD D⊆ = {!   !}
  𝒞-mono {A} {B} (⊥ .A ⟨ x ⟩ .B) {D} {D'} scD D⊆ = {!   !}

  open import Denot.CastStructureRegularInj


  instance 
    dcs : DenotCastStruct
    dcs = record
            { cast = cs
            ; 𝒞 = λ c D → 𝒞 D ⟨ c ⟩ }




  open DenotCastStruct dcs using (⟦_⟧)

  postulate
    ⟦⟧-scD : ∀ M ρ (scDρ : ∀ i → scD (ρ i)) → scD (⟦ M ⟧ ρ)
    ⟦⟧-mono : ∀ M ρ ρ' (monoρ : ∀ i → ρ i ⊆ ρ' i) → ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ'

  _⟶_ = _—→_
  
  ⟦_`∶_⟧ : (ℕ → 𝒫 Val) → List Type → Set
  ⟦ ρ `∶ Γ ⟧ = ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧

  
  coerce-sound-⊇ : ∀ V → (vV : Value V) → ∀ ρ {Γ A B}
                 → (ρ∶Γ : ⟦ ρ `∶ Γ ⟧) → (Γ⊢V∶A : Γ ⊢ V ⦂ A) 
                 → (c : Cast (A ⇒ B)) → {a : Active c}
                 → ⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ 𝒞 (⟦ V ⟧ ρ) ⟨ c ⟩
  coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} = 
    Λ-mono (λ X X' X⊆ → 𝒞-mono d {!   !} (∗-mono {!   !} {!   !} {!   !} (𝒞-mono c {!   !} X⊆)))
  coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (⊥ ._ ⟨ ℓ ⟩ ._) {a} (blame ℓ) refl = inj₂ refl
  coerce-sound-⊇ ($ f # P) V-const ρ ρ∶Γ (⊢$ f P refl) id {a} = λ d z → z
  coerce-sound-⊇ ($ f # P) V-const ρ ρ∶Γ (⊢$ f P refl) (c ↣ d) {a} = λ d z → z
  coerce-sound-⊇ ($ f # P) V-const ρ ρ∶Γ (⊢$ f P refl) (⊥ A ⟨ ℓ ⟩ B) {a} = {!   !}
  coerce-sound-⊇ (⟦ M , N ⟧) (V-pair vV vV₁) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) c {a} = {!   !}
  coerce-sound-⊇ (inl M other B) (V-inl vV) ρ ρ∶Γ (⊢inl B ⊢M refl) c {a} = {!   !}
  coerce-sound-⊇ (inr M other A) (V-inr vV) ρ ρ∶Γ (⊢inr  A ⊢M refl) c {a} = {!   !}
  coerce-sound-⊇ (M ⟨ c₁ ₍ .i ₎⟩) (V-wrap vV i) ρ ρ∶Γ (⊢wrap c₁ i ⊢M ⟨ refl , refl ⟩) c {a} = {!   !}

{-

  {- this is not true...  I have to wonder if we want related values, or 
     blameless values or what... -}

  coerce-sound-⊇ : ∀ V → (vV : Value V) → ∀ ρ {Γ A B}
                 → (ρ∶Γ : ∀ i d {A} → d ∈ ρ i → Γ ∋ i ⦂ A → ⟦ d ∶ A ⟧)
                 → (Γ⊢V∶A : Γ ⊢ V ⦂ A) → (c : Cast (A ⇒ B)) → {a : Active c}
                 → 𝒪⟦ applyCast V Γ⊢V∶A vV c {a} ⟧ ρ ⊆ 𝒞⟦ c ⟧ (𝒪⟦ V ⟧ ρ)
  coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} ν Λ-ν = 
    ⟨ ν , ⟨ Λ-ν , coerce-ok tt ⟩ ⟩
  coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ {Γ} {A ⇒ B} {A' ⇒ B'} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} (V ↦ w) 
    (Λ-↦ ⟨ u , ⟨ u∈'ΛN⟨c⟩' , coerce-fail q y z ⟩ ⟩ Vne) = 
    ⟨ V ↦ w , ⟨ Λ-↦ {!  !} Vne , coerce-ok (λ V∶A' → {!   !}) ⟩ ⟩ 
  coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ {Γ} {A ⇒ B} {A' ⇒ B'} ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (c ↣ d) {a} (V ↦ w) 
    (Λ-↦ ⟨ .w , ⟨ w∈'ΛN⟨c⟩' , coerce-ok u∶B' ⟩ ⟩ Vne) = 
    ⟨ V ↦ w , ⟨ Λ-↦ {!  w∈'ΛN⟨c⟩' !} Vne , coerce-ok (λ V∶A' → {! typesound N (mem V • ρ) ? ⊢N w ? !}) ⟩ ⟩
  coerce-sound-⊇ (ƛ A ˙ N) V-ƛ ρ ρ∶Γ (⊢ƛ A ⊢N ⟨ refl , refl ⟩) (⊥ ._ ⟨ ℓ ⟩ ._) {a} v v∈ = {! u↝v !}
  coerce-sound-⊇ ($ f # P) V-const ρ ρ∶Γ (⊢$ f P refl) c {a} d d∈ = {!   !}
  coerce-sound-⊇ (⟦ M , N ⟧) (V-pair vV vV₁) ρ ρ∶Γ (⊢cons ⊢M ⊢N refl) c {a} d d∈ = {!   !}
  coerce-sound-⊇ (inl M other B) (V-inl vV) ρ ρ∶Γ (⊢inl B ⊢M refl) c {a} d d∈ = {!   !}
  coerce-sound-⊇ (inr M other A) (V-inr vV) ρ ρ∶Γ (⊢inr  A ⊢M refl) c {a} d d∈ = {!   !}
  coerce-sound-⊇ (M ⟨ c₁ ₍ .i ₎⟩) (V-wrap vV i) ρ ρ∶Γ (⊢wrap c₁ i ⊢M ⟨ refl , refl ⟩) c {a} d d∈ = {!   !}

-}
-- TODO
  -- most of data def for coercion meaning
  -- shallow-typechecking; coerce-val
  -- finish data def for coercion meaning
  -- define value consistency
  -- prove consistency lemma
  -- prove blame results that repackage the consitency lemma
  -- prove soundness wrt operational semantics
