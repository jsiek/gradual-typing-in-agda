module EagerCoercions where
  
  open import Data.Nat
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

  infix 7 _↣_
  infix 5 _!!
  infix 5 _??_
  infix 5 ⊥_⟨_⟩_

  data Cast : Type → Set where
    id : ∀ {A : Type} {a : Atomic A} → Cast (A ⇒ A)
    seq : ∀ {A B C : Type} → Cast (A ⇒ B) → Cast (B ⇒ C) → Cast (A ⇒ C)
    _!! : (A : Type) → ∀ {i : A ≢ ⋆} → Cast (A ⇒ ⋆)
    _??_ : (B : Type) → Label → ∀ {j : B ≢ ⋆} → Cast (⋆ ⇒ B)
    _↣_ : ∀ {A B A' B'}
      → (c : Cast (B ⇒ A)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A ⇒ A') ⇒ (B ⇒ B'))
    _`×_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A `× A') ⇒ (B `× B'))
    _`+_ : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → Cast ((A `⊎ A') ⇒ (B `⊎ B'))
    ⊥_⟨_⟩_ : 
        (A : Type) → Label → (B : Type)
      → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  coerce : (A : Type) → (B : Type) → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)
  coerce .⋆ B {unk~L} ℓ with eq-unk B
  ... | yes eq rewrite eq = id {⋆} {A-Unk}
  ... | no neq = (B ?? ℓ) {neq}
  coerce A .⋆ {unk~R} ℓ with eq-unk A
  ... | yes eq rewrite eq = id {⋆} {A-Unk}
  ... | no neq = (A !!) {neq}
  coerce (` ι) (` ι) {base~} ℓ = id {` ι} {A-Base}
  coerce (A ⇒ B) (A' ⇒ B') {fun~ c c₁} ℓ =
    (coerce A' A {Sym~ c} (flip ℓ)) ↣ (coerce B B' {c₁} ℓ)
  coerce (A `× B) (A' `× B') {pair~ c c₁} ℓ =
    (coerce A A' {c} ℓ ) `× (coerce B B' {c₁} ℓ)
  coerce (A `⊎ B) (A' `⊎ B') {sum~ c c₁} ℓ =
    (coerce A A' {c} ℓ ) `+ (coerce B B' {c₁} ℓ)  

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A i} → Inert ((A !!) {i})
    I-fun : ∀{A B A' B'}{c : Cast (A' ⇒ A)}{d : Cast (B ⇒ B')} → Inert (c ↣ d)
    I-seq : ∀{A B C}{c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}
          → Inert c → Inert d → Inert (seq c d)

  data Active : ∀ {A} → Cast A → Set where
    A-proj : ∀{ B ℓ j} → Active ((B ?? ℓ) {j})
    A-pair : ∀{A B A' B'}{c : Cast(A ⇒ A')}{d : Cast(B ⇒ B')} → Active (c `× d)
    A-sum : ∀{A B A' B'}{c : Cast(A ⇒ A')}{d : Cast (B ⇒ B')} → Active (c `+ d)
    A-id : ∀{A a} → Active (id {A}{a})
    A-fail : ∀{A B ℓ} → Active (⊥ A ⟨ ℓ ⟩ B)
    A-seq1 : ∀{A B C}{c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}
           → Active c → Active (seq c d)
    A-seq2 : ∀{A B C}{c : Cast (A ⇒ B)}{d : Cast (B ⇒ C)}
           → Active d → Active (seq c d)

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id = inj₁ A-id
  ActiveOrInert (seq c d)
      with ActiveOrInert c | ActiveOrInert d
  ... | inj₁ a | _ = inj₁ (A-seq1 a)
  ... | inj₂ i | inj₁ a = inj₁ (A-seq2 a)
  ... | inj₂ i | inj₂ i' = inj₂ (I-seq i i')
  ActiveOrInert (A !!) = inj₂ I-inj
  ActiveOrInert (B ?? x) = inj₁ A-proj
  ActiveOrInert (c ↣ c₁) = inj₂ I-fun
  ActiveOrInert (c `× c₁) = inj₁ A-pair
  ActiveOrInert (c `+ c₁) = inj₁ A-sum
  ActiveOrInert (⊥ A ⟨ ℓ ⟩ B) = inj₁ A-fail

  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR

  
