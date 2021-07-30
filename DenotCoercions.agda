module DenotCoercions where

open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Types hiding (_⊔_; _⊑_)
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

𝐺⟦_⟧ : (G : Type) → (g : Ground G) → Value → Set
𝐺⟦ ` b ⟧ G-Base v = 𝐵? b v
𝐺⟦ ⋆ ⇒ ⋆ ⟧ G-Fun v = 𝐹? v
𝐺⟦ ⋆ `× ⋆ ⟧ G-Pair v = False
𝐺⟦ ⋆ `⊎ ⋆ ⟧ G-Sum v = False

𝒢? : (G : Type) → (g : Ground G) → 𝒫 Value → Set
𝒢? G g D = ∀ u → D u → 𝐺⟦ G ⟧ g u

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

data _↝⟦_⟧↝_ : ∀ {A B} → Value → Cast (A ⇒ B) → Value → Set where
  ⟦id⟧ : ∀{v : Value}{A : Type}{a : Atomic A}
    → v ↝⟦ id{A}{a} ⟧↝ v
  ⟦inj⟧ : ∀{v : Value}{G : Type}{g : Ground G}
    → v ↝⟦ inj G {g} ⟧↝ v
  ⟦proj⟧-ok : ∀{v : Value}{G : Type}{g : Ground G}{ℓ : Labels.Label}
    → 𝐺⟦ G ⟧ g v
    → v ↝⟦ proj G ℓ {g} ⟧↝ v
  ⟦proj⟧-fail : ∀{v : Value}{G : Type}{g : Ground G}{ℓ : Labels.Label}
    → ¬ 𝐺⟦ G ⟧ g v
    → v ↝⟦ proj G ℓ {g} ⟧↝ blame! (cvt-label ℓ)
  ⟦cfun⟧ : ∀{v w v′ w′ : Value}{A B A′ B′ : Type}{c : Cast (B ⇒ A)}{d : Cast (A′ ⇒ B′)}
    → v′ ↝⟦ c ⟧↝ v   →   w ↝⟦ d ⟧↝ w′
    → (v ↦ w) ↝⟦ cfun c d ⟧↝ (v′ ↦ w′)
  ⟦cseq⟧ : ∀{u v w : Value}{A B C : Type}{c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}
    → wf v   →   u ↝⟦ c ⟧↝ v    →   v ↝⟦ d ⟧↝ w
    → u ↝⟦ cseq c d ⟧↝ w
{-
  cpair-⟦⟧-l : ∀{v v′ w w′ : Value}{A B A′ B′ : Type}{c : Cast (A ⇒ B)}{d : Cast (A′ ⇒ B′)}
    → const 0 ⊑ v  →  const 0 ⊑ v′  →   w ↝⟦ c ⟧↝ w′
    → (v ↦ w) ↝⟦ cpair c d ⟧↝ (v ↦ w′)
  cpair-⟦⟧-r : ∀{v v′ w w′ : Value}{A B A′ B′ : Type}{c : Cast (A ⇒ B)}{d : Cast (A′ ⇒ B′)}
    → const 1 ⊑ v  →  const 1 ⊑ v′  →   w ↝⟦ d ⟧↝ w′
    → (v ↦ w) ↝⟦ cpair c d ⟧↝ (v ↦ w′)
-}

𝒞 : ∀ {A B} → Cast (A ⇒ B) → 𝒫 Value → 𝒫 Value
𝒞 c D v = Σ[ u ∈ Value ] wf u × D u × u ↝⟦ c ⟧↝ v

𝒞-cong-≲ : ∀{D₁ D₂ : 𝒫 Value}{A B : Type} (c : Cast (A ⇒ B))
  → D₁ ≲ D₂
  → 𝒞 c D₁ ≲ 𝒞 c D₂
𝒞-cong-≲ {D₁} {D₂} {A} {B} c lt v wfv ⟨ u , ⟨ wfu , ⟨ D₁u , cst ⟩ ⟩ ⟩ =
    ⟨ u , ⟨ wfu , ⟨ (lt u wfu D₁u) , cst ⟩ ⟩ ⟩

𝒞-cong : ∀{D₁ D₂ : 𝒫 Value}{A B : Type} (c : Cast (A ⇒ B))
  → D₁ ≃ D₂
  → 𝒞 c D₁ ≃ 𝒞 c D₂
𝒞-cong {D₁} {D₂} {A} {B} c (equal to from) =
    equal (𝒞-cong-≲ c to) (𝒞-cong-≲ c from)

𝒞-id-≃ : ∀ {A a} (D : 𝒫 Value)
  → 𝒞 (id{A}{a}) D ≃ D
𝒞-id-≃{A}{a} D = equal (𝒞-id-≲-1 D) (𝒞-id-≲-2 D)
  where
  𝒞-id-≲-1 : ∀ (D : 𝒫 Value)
    → 𝒞 (id{A}{a}) D ≲ D
  𝒞-id-≲-1 D v wfv ⟨ .v , ⟨ _ , ⟨ Du , ⟦id⟧ ⟩ ⟩ ⟩ = Du

  𝒞-id-≲-2 : ∀ (D : 𝒫 Value)
    → D ≲ 𝒞 (id{A}{a}) D
  𝒞-id-≲-2 D v wfv Dv = ⟨ v , ⟨ wfv , ⟨ Dv , ⟦id⟧ ⟩ ⟩ ⟩

𝒞-cseq-≃ : ∀ {A B C : Type} (c₁ : Cast (A ⇒ B)) (c₂ : Cast (B ⇒ C)) (D : 𝒫 Value)
  → 𝒞 (cseq c₁ c₂) D ≃ 𝒞 c₂ (𝒞 c₁ D)
𝒞-cseq-≃ c₁ c₂ D = equal (𝒞-cseq-≲-1 c₁ c₂ D) (𝒞-cseq-≲-2 c₁ c₂ D)
  where
  𝒞-cseq-≲-1 : ∀ {A B C : Type} (c₁ : Cast (A ⇒ B)) (c₂ : Cast (B ⇒ C)) (D : 𝒫 Value)
    → 𝒞 (cseq c₁ c₂) D ≲ 𝒞 c₂ (𝒞 c₁ D)
  𝒞-cseq-≲-1 c₁ c₂ D v wfv ⟨ w , ⟨ wfw , ⟨ Dw , ⟦cseq⟧ {v = v₁} wfv₁ cst₁ cst₂ ⟩ ⟩ ⟩ =
      ⟨ v₁ , ⟨ wfv₁ , ⟨ ⟨ w , ⟨ wfw , ⟨ Dw , cst₁ ⟩ ⟩ ⟩ , cst₂ ⟩ ⟩ ⟩

  𝒞-cseq-≲-2 : ∀ {A B C : Type} (c₁ : Cast (A ⇒ B)) (c₂ : Cast (B ⇒ C)) (D : 𝒫 Value)
    → 𝒞 c₂ (𝒞 c₁ D) ≲ 𝒞 (cseq c₁ c₂) D 
  𝒞-cseq-≲-2 c₁ c₂ D v wfv ⟨ w , ⟨ wfw , ⟨ ⟨ u , ⟨ wfu , ⟨ Du , cst1 ⟩ ⟩ ⟩ , cst2 ⟩ ⟩ ⟩ =
      ⟨ u , ⟨ wfu , ⟨ Du , ⟦cseq⟧ wfw cst1 cst2 ⟩ ⟩ ⟩

𝒞-assoc-≃ : ∀ {A B C D : Type} (c : Cast (A ⇒ B)) (d : Cast (B ⇒ C)) (e : Cast (C ⇒ D))
   (V : 𝒫 Value)
  → 𝒞 (cseq (cseq c d) e) V ≃ 𝒞 (cseq c (cseq d e)) V
𝒞-assoc-≃ {A}{B}{C}{D} c d e V =
  let b : 𝒞 (cseq (cseq c d) e) V ≃ 𝒞 e (𝒞 (cseq c d) V)
      b = 𝒞-cseq-≃ (cseq c d) e V  in
  let x : 𝒞 e (𝒞 (cseq c d) V) ≃ 𝒞 e (𝒞 d (𝒞 c V))
      x = 𝒞-cong e (𝒞-cseq-≃ c d V) in
  let w : 𝒞 (cseq d e) (𝒞 c V) ≃ 𝒞 (cseq c (cseq d e)) V
      w = ≃-sym (𝒞-cseq-≃ c (cseq d e) V) in
  let v : 𝒞 e (𝒞 d (𝒞 c V)) ≃ 𝒞 (cseq d e) (𝒞 c V)
      v = ≃-sym (𝒞-cseq-≃ d e (𝒞 c V)) in
  ≃-trans (≃-trans b x) (≃-trans v w)


𝒞-fun-cast : ∀{A B C D}(c : Cast((A ⇒ B) ⇒ (C ⇒ D)))(x : Cross c)(D₁ D₂ : 𝒫 Value)
  → (𝒞 c D₁) ▪ D₂  ≃  𝒞 (cod c x) (D₁ ▪ (𝒞 (dom c x) D₂))
𝒞-fun-cast {A}{B}{C}{D} c x D₁ D₂ = equal (𝒞-fun-cast-1 c x) (𝒞-fun-cast-2 c x)
  where 
  𝒞-fun-cast-1 : ∀ (c : Cast((A ⇒ B) ⇒ (C ⇒ D))) (x : Cross c)
    → (𝒞 c D₁) ▪ D₂  ≲ 𝒞 (cod c x) (D₁ ▪ (𝒞 (dom c x) D₂))
  𝒞-fun-cast-1 (cfun c d) x w wfw ⟨ u , ⟨ wfu , ⟨ ⟨ v′ ↦ w′ , ⟨ wf-fun wfv′ wfw′ , ⟨ v∈D₁ , ⟦cfun⟧ cst₁ cst₂ ⟩ ⟩ ⟩ , u∈D₂ ⟩ ⟩ ⟩ =
      ⟨ w′ , ⟨ wfw′ , ⟨ ⟨ v′ , ⟨ wfv′ , ⟨ v∈D₁ , ⟨ u , ⟨ wfu , ⟨ u∈D₂ , cst₁ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ , cst₂ ⟩ ⟩ ⟩

  𝒞-fun-cast-2 : ∀ (c : Cast((A ⇒ B) ⇒ (C ⇒ D))) (x : Cross c)
    → 𝒞 (cod c x) (D₁ ▪ (𝒞 (dom c x) D₂))  ≲  (𝒞 c D₁) ▪ D₂
  𝒞-fun-cast-2 (cfun c d) xcd w wfw ⟨ u , ⟨ wfu , ⟨ ⟨ v , ⟨ wfv , ⟨ v↦u∈D₁ , ⟨ v′ , ⟨ wfv′ , ⟨ v′∈D₂ , vcv ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ , udw ⟩ ⟩ ⟩ =
      ⟨ v′ , ⟨ wfv′ , ⟨ ⟨ (v ↦ u) , ⟨ (wf-fun wfv wfu) , ⟨ v↦u∈D₁ , (⟦cfun⟧ vcv udw) ⟩ ⟩ ⟩ , v′∈D₂ ⟩ ⟩ ⟩

{-
with a precondition:
𝐶 : ∀ {A B} → Cast (A ⇒ B) → (v : Value) → (wt : v types-at A) → Value
-}
{-
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

{-
  M : A
  c : Cast (A ⇒ B)
  ----------------
  M ⟨ c ⟩ : B

  ⟦ M ⟨ c ⟩ ⟧ = 𝒞 c ⟦ M ⟧

-}

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
   (𝒞 c D₁) ▪ D₂  ≃ 𝒞 (cod c x) (D₁ ▪ (𝒞 (dom c x) D₂))


-}

𝒞-fun-cast : ∀{A B C D}(c : Cast((A ⇒ B) ⇒ (C ⇒ D)))(x : Cross c)(D₁ D₂ : 𝒫 Value)
  → (𝒞 c D₁) ▪ D₂  ≃  𝒞 (cod c x) (D₁ ▪ (𝒞 (dom c x) D₂))
𝒞-fun-cast {A}{B}{C}{D} c x D₁ D₂ = equal {!!} {!!}
  where 
  𝒞-fun-cast-1 : ∀ (c : Cast((A ⇒ B) ⇒ (C ⇒ D))) (x : Cross c)
    → (𝒞 c D₁) ▪ D₂  ≲ 𝒞 (cod c x) (D₁ ▪ (𝒞 (dom c x) D₂))
  𝒞-fun-cast-1 (cfun c d) x w ⟨ v , ⟨ wfv , ⟨ ⟨ u₁ ↦ u₂ , ⟨ D₁u , refl ⟩ ⟩ , D2v ⟩ ⟩ ⟩ =
    ⟨ {!!} , ⟨ ⟨ {!!} , ⟨ {!!} , ⟨ {!!} , ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩ ⟩ ⟩ ⟩ , {!!} ⟩ ⟩
-}
