module DenotCoercions where

open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Types hiding (_⊔_)
open import GroundCoercions renaming (Value to SValue)

open import ValueConst hiding (dom; cod)
open import GraphModel
open import Primitives hiding  (_⇒_)
import Labels

blame! : Label → Value
blame! ℓ = const {Blame} ℓ

cvt-label : Labels.Label → Label
cvt-label (Labels.pos n) = label n
cvt-label (Labels.neg n) = label n

cvt-base : Types.Base → Primitives.Base
cvt-base Nat = Nat
cvt-base Int = Int
cvt-base 𝔹 = 𝔹
cvt-base Unit = Unit
cvt-base ⊥ = Void
cvt-base Blame = Blame

𝐵? : Types.Base → Value → Set
𝐵? b ⊥ = True
𝐵? b (const {b'} k)
    with Primitives.base-eq? (cvt-base b) b'
... | yes eq = True
... | no neq = False
𝐵? b (v ↦ w) = False
𝐵? b (u ⊔ v) = 𝐵? b u × 𝐵? b v

𝐹? : Value → Set
𝐹? ⊥ = True
𝐹? (const k) = False
𝐹? (v ↦ w) = True
𝐹? (u ⊔ v) = 𝐹? u × 𝐹? v

𝐺? : (G : Type) → (g : Ground G) → Value → Set
𝐺? (` b) G-Base v = 𝐵? b v
𝐺? (⋆ ⇒ ⋆) G-Fun v = 𝐹? v
𝐺? (⋆ `× ⋆) G-Pair v = False
𝐺? (⋆ `⊎ ⋆) G-Sum v = False

𝒢? : (G : Type) → (g : Ground G) → 𝒫 Value → Set
𝒢? G g D = ∀ u → D u → 𝐺? G g u

𝐶-base : Types.Base → Value → Labels.Label → Value
𝐶-base b ⊥ ℓ = ⊥
𝐶-base b (const {b'} k) ℓ
    with Primitives.base-eq? (cvt-base b) b'
... | yes eq = const {b'} k
... | no neq = blame! (cvt-label ℓ)
𝐶-base b (v ↦ w) ℓ = blame! (cvt-label ℓ)
𝐶-base b (u ⊔ v) ℓ = (𝐶-base b u ℓ) ⊔ (𝐶-base b v ℓ)

𝐶-fun : Value → Labels.Label → Value
𝐶-fun ⊥ ℓ = ⊥
𝐶-fun (const k) ℓ = blame! (cvt-label ℓ)
𝐶-fun (v ↦ w) ℓ = v ↦ w
𝐶-fun (u ⊔ v) ℓ = 𝐶-fun u ℓ ⊔ 𝐶-fun v ℓ

𝐶 : ∀ {A B} → Cast (A ⇒ B) → Value → Value
𝐶 id v = v
𝐶 (inj _) v = v
𝐶 (proj (` b) ℓ {G-Base}) v = 𝐶-base b v ℓ
𝐶 (proj (⋆ ⇒ ⋆) ℓ {G-Fun}) v = 𝐶-fun v ℓ
𝐶 (proj (⋆ `× ⋆) ℓ {G-Pair}) v = ⊥ {- ignoring pairs for now -}
𝐶 (proj (⋆ `⊎ ⋆) ℓ {G-Sum}) v = ⊥ {- ignoring sums for now -}
𝐶 (cfun c₁ c₂) ⊥ = ⊥
𝐶 (cfun c₁ c₂) (const k) = ⊥ {- Can't happen... -}
𝐶 (cfun c₁ c₂) (v ↦ w) = (𝐶 c₁ v) ↦ (𝐶 c₂ w)
𝐶 (cfun c₁ c₂) (u ⊔ v) = (𝐶 (cfun c₁ c₂) u) ⊔ (𝐶 (cfun c₁ c₂) v)
𝐶 (cpair c₁ c₂) v = ⊥  {- ignoring pairs for now -}
𝐶 (csum c₁ c₂) v = ⊥ {- ignoring sums for now -}
𝐶 (cseq c₁ c₂) v = 𝐶 c₂ (𝐶 c₁ v)

{- Semantics of Coercions,  𝒞 = \McC -}

𝒞 : ∀ {A B} → Cast (A ⇒ B) → 𝒫 Value → 𝒫 Value
𝒞 c D v = Σ[ u ∈ Value ] D u × v ≡ 𝐶 c u


{- Properties of the Semantics of Coercions -}

𝒞-cong-≲ : ∀{D₁ D₂ : 𝒫 Value}{A B : Type} (c : Cast (A ⇒ B))
  → D₁ ≲ D₂
  → 𝒞 c D₁ ≲ 𝒞 c D₂
𝒞-cong-≲ {D₁} {D₂} {A} {B} c lt v ⟨ u , ⟨ Du , refl ⟩ ⟩ =
    ⟨ u , ⟨ (lt u Du) , refl ⟩ ⟩

𝒞-cong : ∀{D₁ D₂ : 𝒫 Value}{A B : Type} (c : Cast (A ⇒ B))
  → D₁ ≃ D₂
  → 𝒞 c D₁ ≃ 𝒞 c D₂
𝒞-cong {D₁} {D₂} {A} {B} c (equal to from) = equal (𝒞-cong-≲ c to) (𝒞-cong-≲ c from)


𝒞-id-≃ : ∀ {A a} (D : 𝒫 Value)
  → 𝒞 (id{A}{a}) D ≃ D
𝒞-id-≃{A}{a} D = equal (𝒞-id-≲-1 D) (𝒞-id-≲-2 D)
  where
  𝒞-id-≲-1 : ∀ (D : 𝒫 Value)
    → 𝒞 (id{A}{a}) D ≲ D
  𝒞-id-≲-1 D v ⟨ u , ⟨ Du , refl ⟩ ⟩ = Du

  𝒞-id-≲-2 : ∀ (D : 𝒫 Value)
    → D ≲ 𝒞 (id{A}{a}) D
  𝒞-id-≲-2 D v Dv = ⟨ v , ⟨ Dv , refl ⟩ ⟩

𝒞-inj-≃ : ∀ {A g} (D : 𝒫 Value)
  → 𝒞 (inj A {g}) D ≃ D
𝒞-inj-≃ {A}{g} D = equal (𝒞-inj-≲-1 D) (𝒞-inj-≲-2 D)  
  where
  𝒞-inj-≲-1 : ∀ (D : 𝒫 Value)
    → 𝒞 (inj A {g}) D ≲ D
  𝒞-inj-≲-1 D v ⟨ u , ⟨ Dv , refl ⟩ ⟩ = Dv

  𝒞-inj-≲-2 : ∀ (D : 𝒫 Value)
    → D ≲ 𝒞 (inj A {g}) D
  𝒞-inj-≲-2 D v Dv = ⟨ v , ⟨ Dv , refl ⟩ ⟩
  

𝒞-cseq-≃ : ∀ {A B C : Type} (c₁ : Cast (A ⇒ B)) (c₂ : Cast (B ⇒ C)) (D : 𝒫 Value)
  → 𝒞 (cseq c₁ c₂) D ≃ 𝒞 c₂ (𝒞 c₁ D)
𝒞-cseq-≃ c₁ c₂ D = equal (𝒞-cseq-≲-1 c₁ c₂ D) (𝒞-cseq-≲-2 c₁ c₂ D)
  where
  𝒞-cseq-≲-1 : ∀ {A B C : Type} (c₁ : Cast (A ⇒ B)) (c₂ : Cast (B ⇒ C)) (D : 𝒫 Value)
    → 𝒞 (cseq c₁ c₂) D ≲ 𝒞 c₂ (𝒞 c₁ D)
  𝒞-cseq-≲-1 c₁ c₂ D v ⟨ w , ⟨ Dw , refl ⟩ ⟩ = ⟨ (𝐶 c₁ w) , ⟨ ⟨ w , ⟨ Dw , refl ⟩ ⟩ , refl ⟩ ⟩

  𝒞-cseq-≲-2 : ∀ {A B C : Type} (c₁ : Cast (A ⇒ B)) (c₂ : Cast (B ⇒ C)) (D : 𝒫 Value)
    → 𝒞 c₂ (𝒞 c₁ D) ≲ 𝒞 (cseq c₁ c₂) D 
  𝒞-cseq-≲-2 c₁ c₂ D .(𝐶 c₂ w) ⟨ w , ⟨ ⟨ u , ⟨ Du , refl ⟩ ⟩ , refl ⟩ ⟩ = ⟨ u , ⟨ Du , refl ⟩ ⟩

proj-base-ok : ∀ {ι : Types.Base}{v : Value}{ℓ}
  → 𝐵? ι v
  → 𝐶-base ι v ℓ ≡ v
proj-base-ok {b} {⊥} {ℓ} Bv = refl
proj-base-ok {ι} {const {b} k} {ℓ} Bv
    with Primitives.base-eq? (cvt-base ι) b
... | yes eq = refl
... | no neq = ⊥-elim Bv
proj-base-ok {ι} {u ⊔ v} {ℓ} ⟨ Bu , Bv ⟩
    rewrite proj-base-ok{ι}{u}{ℓ} Bu | proj-base-ok{ι}{v}{ℓ} Bv = refl

proj-fun-ok : ∀{v : Value}{ℓ}
  → 𝐹? v
  → 𝐶-fun v ℓ ≡ v
proj-fun-ok {⊥} {ℓ} Fv = refl
proj-fun-ok {v ↦ w} {ℓ} Fv = refl
proj-fun-ok {u ⊔ v} {ℓ} ⟨ Fu , Fv ⟩
    rewrite proj-fun-ok{u}{ℓ} Fu | proj-fun-ok{v}{ℓ} Fv = refl

proj-ok : ∀ {G : Type}{g : Ground G}{v : Value}{ℓ}
  → 𝐺? G g v
  → 𝐶 (proj G ℓ {g}) v ≡ v
proj-ok {` ι} {G-Base} {ℓ} Gv = proj-base-ok Gv
proj-ok {⋆ ⇒ ⋆} {G-Fun} {v} {ℓ} Gv = proj-fun-ok Gv

𝒞-inj-proj-≃ : ∀ {G : Type}{g : Ground G}{ℓ}{D : 𝒫 Value}
  → 𝒢? G g D
  → 𝒞 (proj G ℓ {g}) (𝒞 (inj G {g}) D) ≃ D
𝒞-inj-proj-≃{G}{g}{ℓ}{D} 𝒢G = equal (𝒞-inj-proj-≲-1 G g 𝒢G ) (𝒞-inj-proj-≲-2 G g 𝒢G)
  where
  𝒞-inj-proj-≲-1 : ∀ G g → 𝒢? G g D →   𝒞 (proj G ℓ {g}) (𝒞 (inj G {g}) D) ≲ D
  𝒞-inj-proj-≲-1 G g GD .(𝐶 (proj G ℓ) v) ⟨ v , ⟨ ⟨ w , ⟨ Dv , refl ⟩ ⟩ , refl ⟩ ⟩
      rewrite proj-ok {G}{g}{v}{ℓ} (GD v Dv) = Dv
  𝒞-inj-proj-≲-2 : ∀ G g → 𝒢? G g D →   D ≲ 𝒞 (proj G ℓ {g}) (𝒞 (inj G {g}) D)
  𝒞-inj-proj-≲-2 G g GD v Dv rewrite sym (proj-ok {G}{g}{v}{ℓ} (GD v Dv)) =
      ⟨ v , ⟨ ⟨ v , ⟨ Dv , refl ⟩ ⟩ , refl ⟩ ⟩

{-
   (V ⟪ c ⟫) · W —→ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩

  D₁ = ⟦ V ⟧ρ
  D₂ = ⟦ W ⟧ρ
   𝐹 (𝒞 c D₁) D₂  ≃ 𝒞 (cod c x) (𝐹 D₁ (𝒞 (dom c x) D₂))
-}

𝒞-fun-cast : ∀{A B C D}(c : Cast((A ⇒ B) ⇒ (C ⇒ D)))(x : Cross c)(D₁ D₂ : 𝒫 Value)
  → 𝐹 (𝒞 c D₁) D₂  ≃  𝒞 (cod c x) (𝐹 D₁ (𝒞 (dom c x) D₂))
𝒞-fun-cast {A}{B}{C}{D} c x D₁ D₂ = equal {!!} {!!}
  where 
  𝒞-fun-cast-1 : ∀ (c : Cast((A ⇒ B) ⇒ (C ⇒ D))) (x : Cross c)
    → 𝐹 (𝒞 c D₁) D₂  ≲ 𝒞 (cod c x) (𝐹 D₁ (𝒞 (dom c x) D₂))
  𝒞-fun-cast-1 (cfun c d) x v ⟨ w , ⟨ wfw , ⟨ ⟨ u₁ ↦ u₂ , ⟨ D₁u , refl ⟩ ⟩ , D2w ⟩ ⟩ ⟩ =
    ⟨ {!!} , ⟨ ⟨ {!!} , ⟨ {!!} , ⟨ {!!} , ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩ ⟩ ⟩ ⟩ , refl ⟩ ⟩
