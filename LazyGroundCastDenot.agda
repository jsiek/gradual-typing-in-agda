module LazyGroundCastDenot where

open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Int using (pos)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import LazyGroundCast
open import Variables
open import PrimitiveTypes using (Base)
open import Types hiding (_⊑_; _⊔_)
{-open import Val Base rep-base -}
open import DenotValue
open import SetsAsPredicates
open import Labels

Env : Context → Set₁
Env Γ = ∀{A} → Γ ∋ A → 𝒫 Val

_∷_ : ∀{Γ B} → 𝒫 Val → (∀{A} → Γ ∋ A → 𝒫 Val) → (∀{A} → Γ , B ∋ A → 𝒫 Val)
(D ∷ ρ) Z = D
(D ∷ ρ) (S x) = ρ x

data ℬ⟦_⟧ : Base → 𝒫 Val where
  ℬ-const : ∀{ι k}
    → const {ι} k ∈ ℬ⟦ ι ⟧
  ℬ-blame : ∀{ι ℓ} → blame ℓ ∈ ℬ⟦ ι ⟧
  
data 𝒯⟦_⟧ : Type → 𝒫 Val where
  𝒯-⋆ : ∀{w} → w ∈ 𝒯⟦ ⋆ ⟧
  𝒯-ι : ∀{w ι} → w ∈ ℬ⟦ ι ⟧ → 𝒯⟦ ` ι ⟧ w
  𝒯-⇒ν : ∀{A B} → ν ∈ 𝒯⟦ A ⇒ B ⟧
  𝒯-⇒↦ : ∀{A B V w} → mem V ⊆ 𝒯⟦ A ⟧ → w ∈ 𝒯⟦ B ⟧
      → (V ↦ w) ∈ 𝒯⟦ A ⇒ B ⟧
  𝒯-×-fst : ∀{A B u} → u ∈ 𝒯⟦ A ⟧ → fst u ∈ 𝒯⟦ A `× B ⟧
  𝒯-×-snd : ∀{A B v} → v ∈ 𝒯⟦ B ⟧ → snd v ∈ 𝒯⟦ A `× B ⟧
  𝒯-⊎-inl : ∀{A B U} → mem U ⊆ 𝒯⟦ A ⟧ → inl U ∈ 𝒯⟦ A `⊎ B ⟧
  𝒯-⊎-inr : ∀{A B V} → mem V ⊆ 𝒯⟦ B ⟧ → inr V ∈ 𝒯⟦ A `⊎ B ⟧
  𝒯-blame : ∀{A ℓ} → blame ℓ ∈ 𝒯⟦ A ⟧

-- coerce : ∀ {A B : Type} → (c : A ~ B) → Label → 𝒫 Val → 𝒫 Val
-- coerce {⋆} {B} unk~L ℓ D v = v ∈ D × v ∈ 𝒯⟦ B ⟧
-- coerce {A} {⋆} unk~R ℓ D = D
-- coerce {` ι} {` ι} base~ ℓ D = D
-- coerce {.(_ ⇒ _)} {.(_ ⇒ _)} (fun~ c d) ℓ D =
--     Λ λ X → coerce d ℓ (D • (coerce c ℓ X))
-- coerce {.(_ `× _)} {.(_ `× _)} (pair~ c d) ℓ D = {!!}
-- coerce {.(_ `⊎ _)} {.(_ `⊎ _)} (sum~ c d) ℓ D = {!!}

-- ⟦_⟧ : ∀{Γ A} → Γ ⊢ A → (Env Γ) → 𝒫 Val
-- ⟦ ` x ⟧ ρ = ρ x
-- ⟦ ƛ M ⟧ ρ = Λ λ D → ⟦ M ⟧ (D ∷ ρ)
-- ⟦ L · M ⟧ ρ = ⟦ L ⟧ ρ  •  ⟦ M ⟧ ρ
-- ⟦ $_ {Γ}{A} k {p} ⟧ ρ = ℘ {A}{p} k
-- ⟦ if L M N ⟧ ρ w = (const true ∈ ⟦ L ⟧ ρ  ×  w ∈ ⟦ M ⟧ ρ)
--                  ⊎ (const false ∈ ⟦ L ⟧ ρ  ×  w ∈ ⟦ N ⟧ ρ)
-- ⟦ cons M N ⟧ ρ = pair (⟦ M ⟧ ρ) (⟦ N ⟧ ρ)
-- ⟦ fst M ⟧ ρ = car (⟦ M ⟧ ρ)
-- ⟦ snd M ⟧ ρ = cdr (⟦ M ⟧ ρ)
-- ⟦ inl M ⟧ ρ = pair (℘ {P = P-Base} true) (⟦ M ⟧ ρ)
-- ⟦ inr M ⟧ ρ = pair (℘ {P = P-Base} false) (⟦ M ⟧ ρ)
-- ⟦ case L M N ⟧ ρ = cond (⟦ L ⟧ ρ) (λ D → ⟦ M ⟧ (D ∷ ρ)) λ D → ⟦ N ⟧ (D ∷ ρ)
-- ⟦ M ⟨ cast A B ℓ c ⟩ ⟧ ρ = coerce {A}{B} c ℓ (⟦ M ⟧ ρ) 
-- ⟦ M ⟪ inert {A} g c ⟫ ⟧ ρ = coerce {A}{⋆} unk~R (pos 0) (⟦ M ⟧ ρ)
-- ⟦ blame ℓ ⟧ ρ = ↓ (blame! ℓ)

-- base-non-empty : ∀{ι : Base}{k : rep-base ι}
--   → const k ∈ ℘ {` ι}{P-Base} k
-- base-non-empty {ι}{k}
--     with base-eq? ι ι 
-- ... | yes refl = refl
-- ... | no neq = neq refl

-- rep-base-inhabit : ∀{ι : Base} → rep-base ι
-- rep-base-inhabit {Nat} = zero
-- rep-base-inhabit {Int} = pos zero
-- rep-base-inhabit {𝔹} = false
-- rep-base-inhabit {Unit} = tt
-- rep-base-inhabit {Blame} = pos zero

-- prim-non-empty : ∀{A}{P : Prim A}{k : rep A}
--   → Σ[ v ∈ Val ] v ∈ ℘ {A}{P} k
-- prim-non-empty {` ι} {P-Base} {k} = ⟨ (const k) , base-non-empty ⟩
-- prim-non-empty {` ι ⇒ B} {P-Fun P} {f}
--     with prim-non-empty {B} {P} {f rep-base-inhabit}
-- ... | ⟨ w , w∈ ⟩ =    
--       ⟨ const rep-base-inhabit ↦ w , ⟨ rep-base-inhabit , ⟨ ⊑-const , w∈ ⟩ ⟩ ⟩

-- coerce-inj-id : ∀ {D : 𝒫 Val}{ℓ} A → coerce{A}{⋆} unk~R ℓ D ≡ D
-- coerce-inj-id ⋆ = refl
-- coerce-inj-id (` ι) = refl
-- coerce-inj-id (A ⇒ B) = refl
-- coerce-inj-id (A `× B) = refl
-- coerce-inj-id (A `⊎ B) = refl

-- values-non-empty : ∀{Γ A} (V : Γ ⊢ A) (v : Value V) (ρ : Env Γ)
--   → Σ[ v ∈ Val ] v ∈ ⟦ V ⟧ ρ
-- values-non-empty {Γ} {.(_ ⇒ _)} (ƛ M) V-ƛ ρ = ⟨ ν , {!!} ⟩
-- values-non-empty {Γ} {A} .($ _) (V-const{k = k}) ρ = prim-non-empty {A}
-- values-non-empty {Γ} {.(_ `× _)} .(cons _ _) (V-pair v w) ρ = {!!}
-- values-non-empty {Γ} {.(_ `⊎ _)} .(inl _) (V-inl v) ρ = {!!}
-- values-non-empty {Γ} {.(_ `⊎ _)} .(inr _) (V-inr v) ρ = {!!}
-- values-non-empty {Γ} {_} (V ⟪ inert {A} g c ⟫) (V-wrap v _) ρ
--     with values-non-empty V v ρ
-- ... | ⟨ v , v∈V ⟩ rewrite coerce-inj-id {⟦ V ⟧ ρ}{pos 0} A = ⟨ v , v∈V ⟩

-- _⊧_ : (Γ : Context) → Env Γ → Set
-- Γ ⊧ ρ = (∀ {A} (x : Γ ∋ A) → ρ x ⊆ 𝒯⟦ A ⟧)

-- down-pres : ∀ v A → v ∈ 𝒯⟦ A ⟧ → ↓ v ⊆ 𝒯⟦ A ⟧
-- down-pres v A v∈A = {!!}

-- ext-pres : ∀{Γ A}{ρ : Env Γ}{D}
--   → Γ ⊧ ρ → D ⊆ 𝒯⟦ A ⟧
--   → (Γ , A) ⊧ (D ∷ ρ)
-- ext-pres Γρ DA = {!!}

-- •-sound : ∀{A B}{D E : 𝒫 Val}
--   → D ⊆ 𝒯⟦ A ⇒ B ⟧
--   → E ⊆ 𝒯⟦ A ⟧
--   → (D • E) ⊆ 𝒯⟦ B ⟧
-- •-sound D⊆A⇒B E⊆A w ⟨ v , ⟨ vw∈D , v∈E ⟩ ⟩ =
--   let vw∈A⇒B = D⊆A⇒B (v ↦ w) vw∈D in
--   let v∈A = E⊆A v v∈E in
--   vw∈A⇒B v∈A

-- prim-sound : ∀ {A}{P : Prim A}{k : rep A}
--   → ℘ {A}{P} k ⊆ 𝒯⟦ A ⟧
-- prim-sound = {!!}

-- coerce-sound : ∀{A B ℓ}{D} (c : A ~ B)
--   → D ⊆ 𝒯⟦ A ⟧
--   → coerce c ℓ D ⊆ 𝒯⟦ B ⟧
-- coerce-sound c D⊆A = {!!}

-- sem-sound : ∀{Γ A}{ρ : Env Γ} (M : Γ ⊢ A)
--   → Γ ⊧ ρ
--   → ⟦ M ⟧ ρ ⊆ 𝒯⟦ A ⟧
-- sem-sound (` x) Γ⊧ρ = Γ⊧ρ x
-- sem-sound (ƛ M) Γ⊧ρ ν vw∈Λ = tt
-- sem-sound {Γ}{A ⇒ B}{ρ} (ƛ M) Γ⊧ρ (v ↦ w) vw∈Λ v∈A =
--    let w∈M : w ∈ ⟦ M ⟧ (↓ v ∷ ρ)
--        w∈M = {!!} in
--    let IH : ⟦ M ⟧ (↓ v ∷ ρ) ⊆ 𝒯⟦ B ⟧
--        IH = sem-sound {Γ , A}{B}{↓ v ∷ ρ} M (ext-pres Γ⊧ρ (down-pres v A v∈A)) in
--    IH w w∈M
-- sem-sound {A = A ⇒ B} (ƛ M) Γ⊧ρ (u ⊔ v) (Λ-⊔ u∈Λ v∈Λ) =
--   let IH1 : u ∈ 𝒯⟦ A ⇒ B ⟧
--       IH1 = sem-sound (ƛ M) Γ⊧ρ u u∈Λ in
--   let IH2 : v ∈ 𝒯⟦ A ⇒ B ⟧
--       IH2 = sem-sound (ƛ M) Γ⊧ρ v v∈Λ in
--   ⟨ IH1 , IH2 ⟩
-- sem-sound {Γ}{ρ = ρ} (_·_ {A = A}{B} L M) Γ⊧ρ =
--   let IH1 : ⟦ L ⟧ ρ ⊆ 𝒯⟦ A ⇒ B ⟧
--       IH1 = sem-sound L Γ⊧ρ in
--   let IH2 : ⟦ M ⟧ ρ ⊆ 𝒯⟦ A ⟧
--       IH2 = sem-sound M Γ⊧ρ in
--   •-sound IH1 IH2
-- sem-sound ($ k) Γ⊧ρ = prim-sound
-- sem-sound (if L M N) Γ⊧ρ = {!!}
-- sem-sound (cons M N) Γ⊧ρ = {!!}
-- sem-sound (fst M) Γ⊧ρ = {!!}
-- sem-sound (snd M) Γ⊧ρ = {!!}
-- sem-sound (inl M) Γ⊧ρ = {!!}
-- sem-sound (inr M) Γ⊧ρ = {!!}
-- sem-sound (case L M N) Γ⊧ρ = {!!}
-- sem-sound {ρ = ρ}(M ⟨ cast A B ℓ c ⟩) Γ⊧ρ =
--   let IH  : ⟦ M ⟧ ρ ⊆ 𝒯⟦ A ⟧
--       IH = sem-sound M Γ⊧ρ in
--   coerce-sound c IH
-- sem-sound {ρ = ρ} (M ⟪ inert {A} g c ⟫) Γ⊧ρ =
--   let IH  : ⟦ M ⟧ ρ ⊆ 𝒯⟦ A ⟧
--       IH = sem-sound M Γ⊧ρ in
--   coerce-sound {A = A}{ℓ = pos 0} unk~R IH
-- sem-sound {A = A} (blame ℓ) Γ⊧ρ v v∈ = {!!} 


-- abstract
--   infix 2 _≅_
--   _≅_ : 𝒫 Val → 𝒫 Val → Set
--   D₁ ≅ D₂ = D₁ ⊆ D₂ × D₂ ⊆ D₁

--   ≅-intro : ∀{D₁ D₂} → D₁ ⊆ D₂ → D₂ ⊆ D₁ → D₁ ≅ D₂
--   ≅-intro d12 d21 = ⟨ d12 , d21 ⟩

--   ≅-refl : ∀ {D} → D ≅ D
--   ≅-refl {D} = ⟨ (λ x x₁ → x₁) , (λ x x₁ → x₁) ⟩

--   ≅-sym : ∀ {D E} → D ≅ E → E ≅ D
--   ≅-sym ⟨ fst₁ , snd₁ ⟩ = ⟨ snd₁ , fst₁ ⟩

--   ≅-trans : ∀ {D E F : 𝒫 Val} → D ≅ E → E ≅ F → D ≅ F
--   ≅-trans ⟨ de , ed ⟩ ⟨ ef , fe ⟩ =
--       ⟨ (λ x z → ef x (de x z)) , (λ x z → ed x (fe x z)) ⟩

-- infix  3 _■
-- _■ : ∀ (D : 𝒫 Val) → D ≅ D
-- (D ■) =  ≅-refl{D}

-- infixr 2 _≅⟨_⟩_
-- _≅⟨_⟩_ : ∀ {E F : 𝒫 Val} (D : 𝒫 Val) → D ≅ E → E ≅ F → D ≅ F
-- D ≅⟨ D≅E ⟩ E≅F = ≅-trans D≅E E≅F

-- coerce-atomic-id : ∀{A ℓ} (D : 𝒫 Val) → (A~A : A ~ A) → (a : Atomic A)
--   → coerce {A}{A} A~A ℓ D ≅ D
-- coerce-atomic-id D unk~L A-Unk = ≅-intro (λ { x ⟨ fst₁ , snd₁ ⟩ → fst₁}) λ { x x₁ → ⟨ x₁ , tt ⟩}
-- coerce-atomic-id D unk~R A-Unk = ≅-refl {D}
-- coerce-atomic-id D base~ A-Base = ≅-refl {D}

-- shift⟦⟧ : ∀{Γ A B} (V : Γ ⊢ A) (D : 𝒫 Val) (ρ : ∀{A} → Γ ∋ A → 𝒫 Val)
--   → ⟦ rename (S_{B = B}) V ⟧ (D ∷ ρ) ≅ ⟦ V ⟧ ρ
-- shift⟦⟧ V D ρ = {!!}

-- Λ-cong : ∀{F G}
--   → (∀{X} → F X ≅ G X)
--   → Λ F ≅ Λ G
-- Λ-cong eq = {!!}

-- •-cong : ∀{D₁ D₂ E₁ E₂}
--   → D₁ ≅ E₁
--   → D₂ ≅ E₂
--   → D₁ • D₂ ≅ E₁ • E₂
-- •-cong de1 de2 = {!!}

-- coerce-cong : ∀{D E ℓ A B} (c : A ~ B)
--   → D ≅ E
--   → coerce c ℓ D ≅ coerce c ℓ E
-- coerce-cong de = {!!}

-- coerce-retract : ∀{G B ℓ ℓ'}{D : 𝒫 Val}{g : Ground G}
--   → (c : G ~ ⋆) → (d : ⋆ ~ B) → (e : G ~ B)
--   → coerce d ℓ (coerce c ℓ' D) ≅ coerce e ℓ D
-- coerce-retract {G}{B}{ℓ}{ℓ'}{D}{g} c d e = {!!}

-- 𝒯-ground : ∀ A G
--   → Ground G
--   → A ~ G
--   → .(A ≢ ⋆)
--   → 𝒯⟦ A ⟧ ⊆ 𝒯⟦ G ⟧
-- 𝒯-ground .⋆ G g unk~L nd = ⊥-elimi (nd refl)
-- 𝒯-ground .(` _) .(` _) g base~ nd v v∈ = v∈
-- 𝒯-ground .(_ ⇒ _) .(⋆ ⇒ ⋆) G-Fun (fun~ A~G A~G₁) nd ν u∈ = tt
-- 𝒯-ground .(_ ⇒ _) .(⋆ ⇒ ⋆) G-Fun (fun~ A~G A~G₁) nd (const {Blame} ℓ) u∈ = blame∈𝒯 {⋆ ⇒ ⋆}{ℓ}
-- 𝒯-ground .(_ ⇒ _) .(⋆ ⇒ ⋆) G-Fun (fun~ A~G A~G₁) nd (v ↦ w) u∈ v∈⋆ = tt
-- 𝒯-ground (A ⇒ B) (⋆ ⇒ ⋆) G-Fun (fun~ A~G A~G₁) nd (u ⊔ v) ⟨ u∈A⇒B , v∈A⇒B ⟩ =
--    let u∈⋆⇒⋆ = 𝒯-ground (A ⇒ B) (⋆ ⇒ ⋆) G-Fun (fun~ A~G A~G₁) nd u u∈A⇒B in
--    let v∈⋆⇒⋆ = 𝒯-ground (A ⇒ B) (⋆ ⇒ ⋆) G-Fun (fun~ A~G A~G₁) nd v v∈A⇒B in
--    ⟨ u∈⋆⇒⋆ , v∈⋆⇒⋆ ⟩
-- 𝒯-ground .(_ `× _) .(⋆ `× ⋆) G-Pair (pair~ A~G A~G₁) nd = {!!}
-- 𝒯-ground .(_ `⊎ _) .(⋆ `⊎ ⋆) G-Sum (sum~ A~G A~G₁) nd = {!!}

-- ℬ-inverse : ∀{v ι}
--   → v ∈ ℬ⟦ ι ⟧
--   → (Σ[ k ∈ rep-base ι ] v ⊑ const k) ⊎ (Σ[ ℓ ∈ Label ] v ⊑ blame! ℓ)
-- ℬ-inverse {const {B} k} {ι} v∈
--     with base-eq? ι B
-- ... | yes refl = inj₁ (⟨ k , ⊑-const ⟩)
-- ... | no neq
--     with v∈
-- ... | refl = inj₂ (⟨ k , ⊑-const ⟩)
-- ℬ-inverse {u ⊔ v} {ι} ⟨ u∈ , v∈ ⟩
--     with ℬ-inverse {u} {ι} u∈ | ℬ-inverse {v} {ι} v∈
-- ... | inj₁ (⟨ k , u⊑k ⟩) | inj₁ (⟨ k' , v⊑k' ⟩) = {!!}
-- ... | inj₂ xx | _ = {!!}    

-- 𝒯-conflict : ∀ G H v
--   → Ground G
--   → Ground H
--   → .(G ≢ H)
--   → v ∈ 𝒯⟦ G ⟧ → v ∈ 𝒯⟦ H ⟧ → Σ[ ℓ ∈ Label ] v ≡ blame! ℓ
-- 𝒯-conflict (` ι) (` ι′) v G-Base G-Base neq v∈G v∈H = {!!}

-- 𝒯-conflict .(` _) .(⋆ ⇒ ⋆) v G-Base G-Fun neq = {!!}
-- 𝒯-conflict .(` _) .(⋆ `× ⋆) v G-Base G-Pair neq = {!!}
-- 𝒯-conflict .(` _) .(⋆ `⊎ ⋆) v G-Base G-Sum neq = {!!}
-- 𝒯-conflict .(⋆ ⇒ ⋆) H v G-Fun h neq = {!!}
-- 𝒯-conflict .(⋆ `× ⋆) H v G-Pair h neq = {!!}
-- 𝒯-conflict .(⋆ `⊎ ⋆) H v G-Sum h neq = {!!}

-- coerce-blame : ∀{G B H ℓ ℓ'}{D : 𝒫 Val}{g : Ground G}{h : Ground H}
--   → D ⊆ 𝒯⟦ G ⟧
--   → (c : G ~ ⋆) → (d : ⋆ ~ B) → (bh : B ~ H) → (G ≢ H) → .(B ≢ ⋆)
--   → coerce d ℓ (coerce c ℓ' D) ≅ ↓ (blame! ℓ)
-- coerce-blame {G} {.⋆} {H} {ℓ} {ℓ'} {D} {g} D⊆G unk~R unk~R bh G≢H nd = ⊥-elimi (nd refl)
-- coerce-blame {G} {B} {H} {ℓ} {ℓ'} {D} {g} D⊆G unk~R unk~L bh G≢H nd = {!!}
-- {-
--   ≅-intro G1 G2
--   where
--   G1 : coerce d ℓ (coerce c ℓ' D) ⊆ (λ w → w ≡ blame! ℓ)
--   G1 v v∈dcD =
-- {-     let v∈ι = D⊆G  -}
--      {!!}
  
--   G2 : (λ w → w ≡ blame! ℓ) ⊆ coerce d ℓ (coerce c ℓ' D)
--   G2 = {!!}
-- -}

-- ⟦⟧-cast : ∀{Γ A B} (V : Γ ⊢ A) (c : Cast (A ⇒ B)) (a : Active c)
--    {v : Value V}{ρ : ∀{A} → Γ ∋ A → 𝒫 Val}
--   → Γ ⊧ ρ
--   → ⟦ V ⟨ c ⟩ ⟧ ρ ≅ ⟦ applyCast V v c {a} ⟧ ρ
-- ⟦⟧-cast V (cast A .A ℓ A~B) (activeId {a = a} .(cast A A ℓ _)) {v}{ρ} Γ⊧ρ =
--     coerce-atomic-id (⟦ V ⟧ ρ) A~B a 
-- ⟦⟧-cast V (cast A .⋆ ℓ A~B) (activeInj .(cast A ⋆ ℓ _) ng nd) {v}{ρ} Γ⊧ρ = {!!}
-- ⟦⟧-cast (V ⟪ inert {G} g c ⟫) (cast .⋆ B ℓ ⋆~B) (activeProj _ nd)
--         {V-wrap v _} {ρ} Γ⊧ρ
--     with ground B {nd}
-- ... | ⟨ H , ⟨ h , B~H ⟩ ⟩
--     with gnd-eq? G H {g}{h}
-- ... | yes refl = coerce-retract {g = g} unk~R ⋆~B (Sym~ B~H)
-- ... | no neq =
--       let xx = {!!} in
--       coerce-blame{g = g}{h = h} (sem-sound V Γ⊧ρ) unk~R ⋆~B B~H neq {!nd!} 
-- ⟦⟧-cast V (cast (A ⇒ B) (A' ⇒ B') ℓ (fun~ c d)) (activeFun .(cast (A ⇒ B) (A' ⇒ B') ℓ (fun~ c d))) {v}{ρ} Γ⊧ρ =
--     Λ-cong G 
--     where
--     G : ∀ {X : 𝒫 Val} →
--          coerce d ℓ (⟦ V ⟧ ρ • coerce c ℓ X)
--        ≅ coerce d ℓ (⟦ rename S_ V ⟧ (X ∷ ρ) • coerce c ℓ X)
--     G {X} =
--             coerce d ℓ (⟦ V ⟧ ρ • coerce c ℓ X)
--           ≅⟨ coerce-cong d (•-cong (≅-sym (shift⟦⟧{B = A'} V X ρ)) ≅-refl) ⟩
--             coerce d ℓ (⟦ rename S_ V ⟧ (X ∷ ρ) • coerce c ℓ X)
--           ■
-- ⟦⟧-cast V (cast .(_ `× _) .(_ `× _) ℓ A~B) (activePair .(cast (_ `× _) (_ `× _) ℓ _)) Γ⊧ρ = {!!}
-- ⟦⟧-cast V (cast .(_ `⊎ _) .(_ `⊎ _) ℓ A~B) (activeSum .(cast (_ `⊎ _) (_ `⊎ _) ℓ _)) Γ⊧ρ = {!!}
-- ⟦⟧-cast V (cast A B ℓ A~B) (activeErr .(cast A B ℓ _) nsc) Γ⊧ρ = {!!}

-- ⟦⟧—→ : ∀{Γ A}{M N : Γ ⊢ A}{ρ : ∀{A} → Γ ∋ A → 𝒫 Val}
--   → M —→ N → Γ ⊧ ρ → ⟦ M ⟧ ρ ≅ ⟦ N ⟧ ρ
-- ⟦⟧—→ {M} {N} (ξ red) Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} ξ-blame Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} (β x) Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} δ Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} β-if-true Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} β-if-false Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} (β-fst x x₁) Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} (β-snd x x₁) Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} (β-caseL x) Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} (β-caseR x) Γ⊧ρ = {!!}
-- ⟦⟧—→ {M} {N} (cast{V = V}{c} v {a}) Γ⊧ρ = ⟦⟧-cast V c a Γ⊧ρ
-- ⟦⟧—→ {M} {N} (wrap v) Γ⊧ρ = {!!}
