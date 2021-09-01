module Types where

  open import Data.Bool using (Bool; true; false)
  open import Data.Empty using () renaming (⊥ to Bot)
  open import Data.Empty.Irrelevant using (⊥-elim)
  open import Data.Integer using (ℤ)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_) renaming (_⊔_ to _∨_)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit renaming (⊤ to Top)
  open import PrimitiveTypes
     renaming (Prim to PrimD; Void to ⊥; rep to prim-rep; Label to DenotLabel)
     public
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Utils using (case_of_; case_return_of_)

  infix  7 _⇒_
  infix  9 _`×_
  infix  8 _`⊎_
  infix 10 `_
  infix 10 Ref_

{-
  data Base : Set where
    Nat : Base
    Int : Base
    𝔹 : Base
    Unit : Base
    ⊥ : Base
-}

  data Type : Set where
    ⋆ : Type
    `_ : Base → Type
    _⇒_ : Type → Type → Type
    _`×_ : Type → Type → Type
    _`⊎_ : Type → Type → Type
    Ref_ : Type → Type


  height-t : Type → ℕ
  height-t ⋆ = 0
  height-t (` B) = 0
  height-t (A ⇒ B) = suc (height-t A ∨ height-t B)
  height-t (A `× B) = suc (height-t A ∨ height-t B)
  height-t (A `⊎ B) = suc (height-t A ∨ height-t B)
  height-t (Ref A)  = suc (height-t A)

  size-t : Type → ℕ
  size-t ⋆ = 0
  size-t (` ι) = 0
  size-t (A ⇒ B) = 1 + size-t A + size-t B
  size-t (A `× B) = 1 + size-t A + size-t B
  size-t (A `⊎ B) = 1 + size-t A + size-t B
  size-t (Ref A)  = 1 + size-t A

  data Atomic : Type → Set where
    A-Unk : Atomic ⋆
    A-Base : ∀{ι} → Atomic (` ι)

  AtomicNotRel : ∀{A} (a1 : Atomic A) (a2 : Atomic A) → a1 ≡ a2
  AtomicNotRel {.⋆} A-Unk A-Unk = refl
  AtomicNotRel {.(` _)} A-Base A-Base = refl

  base? : (A : Type) → Dec (∃[ ι ] A ≡ ` ι)
  base? (` ι) = yes ⟨ ι , refl ⟩
  base? ⋆ = no G
    where G : ¬ (∃[ ι ] ⋆ ≡ ` ι)
          G ()
  base? (A ⇒ B) =  no G
    where G : ¬ (∃[ ι ] A ⇒ B ≡ ` ι)
          G ()
  base? (A `× B) =  no G
    where G : ¬ (∃[ ι ] A `× B ≡ ` ι)
          G ()
  base? (A `⊎ B) =  no G
    where G : ¬ (∃[ ι ] A `⊎ B ≡ ` ι)
          G ()
  base? (Ref A) = no G
    where G : ¬ (∃[ ι ] Ref A ≡ ` ι)
          G ()

  rep-base : Base → Set
  rep-base = base-rep
{-
  rep-base Nat = ℕ
  rep-base Int = ℤ
  rep-base 𝔹 = Bool
  rep-base Unit = Top
  rep-base ⊥ = Bot
-}

  rep : Type → Set
  rep ⋆ = Bot
  rep (` ι) = rep-base ι
  rep (A ⇒ B) = (rep A) → (rep B)
  rep (A `× B) = Bot
  rep (A `⊎ B) = Bot
  rep (Ref A)  = Bot

  data Prim : Type → Set where
    P-Base : ∀{ι} → Prim (` ι)
    P-Fun : ∀ {ι B}
      → Prim B
        ------------------
      → Prim ((` ι) ⇒ B)

  prim→primd : ∀{A} → Prim A → PrimD
  prim→primd {` ι} P-Base = base ι
  prim→primd {` ι ⇒ B} (P-Fun P) = ι ⇒ prim→primd P

  rep→prim-rep : ∀{A} → (P : Prim A) → (k : rep A) → prim-rep (prim→primd P)
  rep→prim-rep {` ι} P-Base k = k
  rep→prim-rep {` ι ⇒ B} (P-Fun P) k x = rep→prim-rep P (k x)

  {- TODO: replace rep with the following repp -}

  repp : ∀{A} → Prim A → Set
  repp {(` ι)} P-Base = rep-base ι
  repp {(` ι ⇒ _)} (P-Fun p) = (rep-base ι) → repp p

  P-Fun1 : ∀ {A B}
    → Prim (A ⇒ B)
    → Σ[ ι ∈ Base ] A ≡ ` ι
  P-Fun1 (P-Fun{ι = ι} b) = ⟨ ι , refl ⟩

  P-Fun2 : ∀ {A B}
    → Prim (A ⇒ B)
    → Prim B
  P-Fun2 (P-Fun b) = b

  prim? : (A : Type) → Dec (Prim A)
  prim? (` x) = yes P-Base
  prim? (A ⇒ B) =
    case prim? B of λ where
      (yes pb) →
        case A return (λ A → Dec (Prim (A ⇒ B))) of λ where
          (` ι) → yes (P-Fun pb)
          ⋆ → no λ ()
          (A₁ ⇒ A₂) → no λ ()
          (A₁ `× A₂) → no λ ()
          (A₁ `⊎ A₂) → no λ ()
          (Ref A) → no λ ()
      (no ¬pb) → no λ pab → contradiction (P-Fun2 pab) ¬pb
  prim? ⋆ = no (λ ())
  prim? (A `× A₁) = no λ ()
  prim? (A `⊎ A₁) = no λ ()
  prim? (Ref A) = no λ ()

  ¬P-Fun : ∀{A B C} → ¬ Prim ((A ⇒ B) ⇒ C)
  ¬P-Fun ()

  ¬P-Pair : ∀{A B C} → ¬ Prim ((A `× B) ⇒ C)
  ¬P-Pair ()

  ¬P-Sum : ∀{A B C} → ¬ Prim ((A `⊎ B) ⇒ C)
  ¬P-Sum ()

  ¬P-Unk : ∀{C} → ¬ Prim (⋆ ⇒ C)
  ¬P-Unk ()

  infix 6 _⊑_

  data _⊑_ : Type → Type → Set where
    unk⊑ : ∀{A} → ⋆ ⊑ A

    base⊑ : ∀{ι} → ` ι ⊑ ` ι

    fun⊑ : ∀ {A B A' B'}
      → A ⊑ A' → B ⊑ B'
        ---------------
      → A ⇒ B ⊑ A' ⇒ B'

    pair⊑ : ∀ {A B A' B'}
      → A ⊑ A' → B ⊑ B'
        ---------------
      → A `× B ⊑ A' `× B'

    sum⊑ : ∀ {A B A' B'}
      → A ⊑ A' → B ⊑ B'
        ---------------
      → A `⊎ B ⊑ A' `⊎ B'

    ref⊑ : ∀ {A A'}
      → A ⊑ A'
        ---------------
      → Ref A ⊑ Ref A'

  Refl⊑ : ∀{A} → A ⊑ A
  Refl⊑ {⋆} = unk⊑
  Refl⊑ {` ι} = base⊑
  Refl⊑ {A ⇒ A₁} = fun⊑ Refl⊑ Refl⊑
  Refl⊑ {A `× A₁} = pair⊑ Refl⊑ Refl⊑
  Refl⊑ {A `⊎ A₁} = sum⊑ Refl⊑ Refl⊑
  Refl⊑ {Ref A} = ref⊑ Refl⊑

  Trans⊑ : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
  Trans⊑ unk⊑ b = unk⊑
  Trans⊑ base⊑ b = b
  Trans⊑ (fun⊑ a a₁) (fun⊑ b b₁) = fun⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)
  Trans⊑ (pair⊑ a a₁) (pair⊑ b b₁) = pair⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)
  Trans⊑ (sum⊑ a a₁) (sum⊑ b b₁) = sum⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)
  Trans⊑ (ref⊑ a) (ref⊑ b) = ref⊑ (Trans⊑ a b)

  AntiSym⊑ : ∀ {A B} → A ⊑ B → B ⊑ A → A ≡ B
  AntiSym⊑ unk⊑ unk⊑ = refl
  AntiSym⊑ base⊑ base⊑ = refl
  AntiSym⊑ {A ⇒ B}{A' ⇒ B'} (fun⊑ a a₁) (fun⊑ b b₁) =
    cong₂ (_⇒_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)
  AntiSym⊑ (pair⊑ a a₁) (pair⊑ b b₁) =
    cong₂ (_`×_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)
  AntiSym⊑ (sum⊑ a a₁) (sum⊑ b b₁) =
    cong₂ (_`⊎_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)
  AntiSym⊑ (ref⊑ a) (ref⊑ b) = cong Ref_ (AntiSym⊑ a b)

  ⊑L⋆ : ∀{A} → A ⊑ ⋆ → A ≡ ⋆
  ⊑L⋆ {⋆} unk⊑ = refl

  ⊑RBase : ∀{C ι} → ` ι ⊑ C → C ≡ ` ι
  ⊑RBase {ι} base⊑ = refl

  ⊑LBase : ∀{A ι} → A ⊑ ` ι →  A ≡ (` ι) ⊎ A ≡ ⋆
  ⊑LBase {⋆} {ι} unk⊑ = inj₂ refl
  ⊑LBase {` ι₁} {ι₂} base⊑ = inj₁ refl

  ⊑L⇒ : ∀{A B₁ B₂} → A ⊑ (B₁ ⇒ B₂)
        → A ≡ ⋆ ⊎ Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ]
                   (A ≡ A₁ ⇒ A₂) × (A₁ ⊑ B₁) × (A₂ ⊑ B₂)
  ⊑L⇒ {.⋆} {B₁} {B₂} unk⊑ = inj₁ refl
  ⊑L⇒ {A ⇒ B} {B₁} {B₂} (fun⊑ d d₁) =
    inj₂ ⟨ A , ⟨ B , ⟨ refl , ⟨ d , d₁ ⟩ ⟩ ⟩ ⟩

  ⊑L× : ∀{A B₁ B₂} → A ⊑ (B₁ `× B₂)
        → A ≡ ⋆ ⊎ Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ]
                   (A ≡ A₁ `× A₂) × (A₁ ⊑ B₁) × (A₂ ⊑ B₂)
  ⊑L× {.⋆} {B₁} {B₂} unk⊑ = inj₁ refl
  ⊑L× {A `× B} {B₁} {B₂} (pair⊑ d d₁) =
    inj₂ ⟨ A , ⟨ B , ⟨ refl , ⟨ d , d₁ ⟩ ⟩ ⟩ ⟩

  ⊑L⊎ : ∀{A B₁ B₂} → A ⊑ (B₁ `⊎ B₂)
        → A ≡ ⋆ ⊎ Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ]
                   (A ≡ A₁ `⊎ A₂) × (A₁ ⊑ B₁) × (A₂ ⊑ B₂)
  ⊑L⊎ {.⋆} {B₁} {B₂} unk⊑ = inj₁ refl
  ⊑L⊎ {A `⊎ B} {B₁} {B₂} (sum⊑ d d₁) =
    inj₂ ⟨ A , ⟨ B , ⟨ refl , ⟨ d , d₁ ⟩ ⟩ ⟩ ⟩

  ⊑R⇒ : ∀{A₁ A₂ B} → (A₁ ⇒ A₂) ⊑ B →
      Σ[ B₁ ∈ Type ] Σ[ B₂ ∈ Type ] B ≡ B₁ ⇒ B₂ × A₁ ⊑ B₁ × A₂ ⊑ B₂
  ⊑R⇒ (fun⊑{A' = A'}{B' = B'} c₁ c₂) =
    ⟨ A' , ⟨ B' , ⟨ refl , ⟨ c₁ , c₂ ⟩ ⟩ ⟩ ⟩

  ⊑R× : ∀{A₁ A₂ B} → (A₁ `× A₂) ⊑ B →
      Σ[ B₁ ∈ Type ] Σ[ B₂ ∈ Type ] B ≡ B₁ `× B₂ × A₁ ⊑ B₁ × A₂ ⊑ B₂
  ⊑R× (pair⊑{A' = A'}{B' = B'} c₁ c₂) =
    ⟨ A' , ⟨ B' , ⟨ refl , ⟨ c₁ , c₂ ⟩ ⟩ ⟩ ⟩

  ⊑R⊎ : ∀{A₁ A₂ B} → (A₁ `⊎ A₂) ⊑ B →
      Σ[ B₁ ∈ Type ] Σ[ B₂ ∈ Type ] B ≡ B₁ `⊎ B₂ × A₁ ⊑ B₁ × A₂ ⊑ B₂
  ⊑R⊎ (sum⊑{A' = A'}{B' = B'} c₁ c₂) =
    ⟨ A' , ⟨ B' , ⟨ refl , ⟨ c₁ , c₂ ⟩ ⟩ ⟩ ⟩

  infix  5  _~_

  data _~_ : Type → Type → Set where
    unk~L : ∀ {A} → ⋆ ~ A

    unk~R : ∀ {A} → A ~ ⋆

    base~ : ∀ {ι} → ` ι ~ ` ι

    fun~ : ∀ {A B A' B'}
      → A' ~ A  →  B ~ B'
        -------------------
      → (A ⇒ B) ~ (A' ⇒ B')

    pair~ : ∀ {A B A' B'}
      → A ~ A'  →  B ~ B'
        -------------------
      → (A `× B) ~ (A' `× B')

    sum~ : ∀ {A B A' B'}
      → A ~ A'  →  B ~ B'
        -------------------
      → (A `⊎ B) ~ (A' `⊎ B')

    ref~ : ∀ {A A'}
      → A ~ A'
        ---------------
      → Ref A ~ Ref A'


  Sym~ : ∀ {A B} → A ~ B → B ~ A
  Sym~ unk~L = unk~R
  Sym~ unk~R = unk~L
  Sym~ base~ = base~
  Sym~ (fun~ c c₁) = fun~ (Sym~ c) (Sym~ c₁)
  Sym~ (pair~ c c₁) = pair~ (Sym~ c) (Sym~ c₁)
  Sym~ (sum~ c c₁) = sum~ (Sym~ c) (Sym~ c₁)
  Sym~ (ref~ c) = ref~ (Sym~ c)

  consis : ∀{C A B}
      → A ⊑ C → B ⊑ C
        -------------
      → A ~ B
  consis unk⊑ bc = unk~L
  consis base⊑ unk⊑ = unk~R
  consis base⊑ base⊑ = base~
  consis (fun⊑ ac ac₁) unk⊑ = unk~R
  consis (fun⊑ ac ac₁) (fun⊑ bc bc₁) = fun~ (consis bc ac) (consis ac₁ bc₁)
  consis (pair⊑ ac ac₁) unk⊑ = unk~R
  consis (pair⊑ ac ac₁) (pair⊑ bc bc₁) = pair~ (consis ac bc) (consis ac₁ bc₁)
  consis (sum⊑ ac ac₁) unk⊑ = unk~R
  consis (sum⊑ ac ac₁) (sum⊑ bc bc₁) = sum~ (consis ac bc) (consis ac₁ bc₁)
  consis (ref⊑ ac) unk⊑ = unk~R
  consis (ref⊑ ac) (ref⊑ bc) = ref~ (consis ac bc)

  Refl~ : ∀ {A} → A ~ A
  Refl~ {A} = consis Refl⊑ Refl⊑

  consis-ub : ∀{A B} → A ~ B → Σ[ C ∈ Type ] A ⊑ C × B ⊑ C
  consis-ub{B = B} unk~L = ⟨ B , ⟨ unk⊑ , Refl⊑ ⟩ ⟩
  consis-ub{A = A} unk~R = ⟨ A , ⟨ Refl⊑ , unk⊑ ⟩ ⟩
  consis-ub (base~ {ι = ι}) = ⟨ ` ι , ⟨ base⊑ , base⊑ ⟩ ⟩
  consis-ub (fun~ ab₁ ab₂)
      with consis-ub ab₁ | consis-ub ab₂
  ... | ⟨ C₁ , ⟨ ac1 , bc1 ⟩ ⟩ | ⟨ C₂ , ⟨ ac2 , bc2 ⟩ ⟩ =
        ⟨ C₁ ⇒ C₂ , ⟨ (fun⊑ bc1 ac2) , fun⊑ ac1 bc2 ⟩ ⟩
  consis-ub (pair~ ab₁ ab₂)
      with consis-ub ab₁ | consis-ub ab₂
  ... | ⟨ C₁ , ⟨ ac1 , bc1 ⟩ ⟩ | ⟨ C₂ , ⟨ ac2 , bc2 ⟩ ⟩ =
        ⟨ C₁ `× C₂ , ⟨ (pair⊑ ac1 ac2) , pair⊑ bc1 bc2 ⟩ ⟩
  consis-ub (sum~ ab₁ ab₂)
      with consis-ub ab₁ | consis-ub ab₂
  ... | ⟨ C₁ , ⟨ ac1 , bc1 ⟩ ⟩ | ⟨ C₂ , ⟨ ac2 , bc2 ⟩ ⟩ =
        ⟨ C₁ `⊎ C₂ , ⟨ (sum⊑ ac1 ac2) , sum⊑ bc1 bc2 ⟩ ⟩
  consis-ub (ref~ ab) =
    case consis-ub ab of λ where
      ⟨ C , ⟨ ac , bc ⟩ ⟩ → ⟨ Ref C , ⟨ ref⊑ ac , ref⊑ bc ⟩ ⟩

  ub : (C : Type) → (A : Type) → (B : Type) → Set
  ub C A B = (A ⊑ C) × (B ⊑ C)

  lub : (C : Type) → (A : Type) → (B : Type) → Set
  lub C A B = (ub C A B) × (∀{C'} → ub C' A B → C ⊑ C')

  infix 6 _`⊔_
  _`⊔_ : (A : Type) → (B : Type) → ∀ { c : A ~ B } → Σ[ C ∈ Type ] (lub C A B)
  (.⋆ `⊔ B) {unk~L} = ⟨ B , ⟨ ⟨ unk⊑ , Refl⊑ ⟩ , (λ x → proj₂ x) ⟩ ⟩
  (A `⊔ .⋆) {unk~R} = ⟨ A , ⟨ ⟨ Refl⊑ , unk⊑ ⟩ , (λ {C'} → proj₁) ⟩ ⟩
  (` ι `⊔ ` ι) {base~} = ⟨ ` ι , ⟨ ⟨ base⊑ , base⊑ ⟩ , (λ {x} → proj₁) ⟩ ⟩
  ((A ⇒ B) `⊔ (A' ⇒ B')) {fun~ c c₁} with (A' `⊔ A) {c} | (B `⊔ B') {c₁}
  ... | ⟨ C , lub1 ⟩ | ⟨ D , lub2 ⟩ =
    let x = fun⊑ (proj₁ (proj₁ lub1)) (proj₁ (proj₁ lub2)) in
    let y = fun⊑ (proj₂ (proj₁ lub1)) (proj₂ (proj₁ lub2))in
    ⟨ (C ⇒ D) ,
    ⟨ ⟨ fun⊑ (proj₂ (proj₁ lub1)) (proj₁ (proj₁ lub2)) ,
        fun⊑ (proj₁ (proj₁ lub1)) (proj₂ (proj₁ lub2)) ⟩ ,
      G ⟩ ⟩
    where
    G : {C' : Type} →
        Σ (A ⇒ B ⊑ C') (λ x₁ → A' ⇒ B' ⊑ C') → C ⇒ D ⊑ C'
    G {.(_ ⇒ _)} ⟨ fun⊑ a-b-cp a-b-cp₁ , fun⊑ ap-bp-cp ap-bp-cp₁ ⟩ =
      fun⊑ (proj₂ lub1 ⟨ ap-bp-cp , a-b-cp ⟩)
           (proj₂ lub2 ⟨ a-b-cp₁ , ap-bp-cp₁ ⟩)

  ((A `× B) `⊔ (A' `× B')) {pair~ c c₁} with (A `⊔ A') {c} | (B `⊔ B') {c₁}
  ... | ⟨ C , lub1 ⟩ | ⟨ D , lub2 ⟩ =
    let x = pair⊑ (proj₁ (proj₁ lub1)) (proj₁ (proj₁ lub2)) in
    let y = pair⊑ (proj₂ (proj₁ lub1)) (proj₂ (proj₁ lub2)) in
    ⟨ (C `× D) , ⟨ ⟨ x , y ⟩ , G ⟩ ⟩
    where
    G : {C' : Type} →
        Σ (A `× B ⊑ C') (λ x₁ → A' `× B' ⊑ C') → C `× D ⊑ C'
    G {.(_ `× _)} ⟨ pair⊑ fst fst₁ , pair⊑ snd snd₁ ⟩ =
      pair⊑ (proj₂ lub1 ⟨ fst , snd ⟩) (proj₂ lub2 ⟨ fst₁ , snd₁ ⟩)
  ((A `⊎ B) `⊔ (A' `⊎ B')) {sum~ c c₁} with (A `⊔ A') {c} | (B `⊔ B') {c₁}
  ... | ⟨ C , lub1 ⟩ | ⟨ D , lub2 ⟩ =
    let x = sum⊑ (proj₁ (proj₁ lub1)) (proj₁ (proj₁ lub2)) in
    let y = sum⊑ (proj₂ (proj₁ lub1)) (proj₂ (proj₁ lub2)) in
    ⟨ (C `⊎ D) , ⟨ ⟨ x , y ⟩ , G ⟩ ⟩
    where
    G : {C' : Type} →
        Σ (A `⊎ B ⊑ C') (λ x₁ → A' `⊎ B' ⊑ C') → C `⊎ D ⊑ C'
    G {.(_ `⊎ _)} ⟨ sum⊑ fst fst₁ , sum⊑ snd snd₁ ⟩ =
      sum⊑ (proj₂ lub1 ⟨ fst , snd ⟩) (proj₂ lub2 ⟨ fst₁ , snd₁ ⟩)
  (Ref A `⊔ Ref A') {ref~ c} =
    case (A `⊔ A') {c} of λ where
      ⟨ C , ⟨ ⟨ ac , a'c ⟩ , f ⟩ ⟩ →
        ⟨ Ref C , ⟨ ⟨ ref⊑ ac , ref⊑ a'c ⟩ ,
                    (λ { ⟨ ref⊑ aa'' , ref⊑ a'a'' ⟩ →
                         ref⊑ (f ⟨ aa'' , a'a'' ⟩) }) ⟩ ⟩

  _⊔_ : (A : Type) → (B : Type) → ∀ { c : A ~ B } → Type
  (A ⊔ B) {c} = proj₁ ((A `⊔ B) {c})

  ⋆⊔B=B : ∀{B} → (⋆ ⊔ B) {unk~L} ≡ B
  ⋆⊔B=B {B} = refl

  A⊔⋆=A : ∀{A} → (A ⊔ ⋆) {unk~R} ≡ A
  A⊔⋆=A {A} = refl

  ⊔L : ∀ {A A'} {c : A ~ A'} → A ~ ((A ⊔ A') {c})
  ⊔L {A}{A'}{c} with (A `⊔ A') {c}
  ...    | ⟨ B , ⟨ q1 , q2 ⟩ ⟩ = consis {B} (proj₁ q1) (q2 q1)

  ⊔R : ∀ {A A'} {c : A ~ A'} → A' ~ ((A ⊔ A') {c})
  ⊔R {A}{A'}{c} with (A `⊔ A') {c}
  ...    | ⟨ B , ⟨ q1 , q2 ⟩ ⟩ = consis {B} (proj₂ q1) (q2 q1)

  ¬~nb : ¬ (` Nat ~ ` 𝔹)
  ¬~nb ()

  ¬~nf : ∀{A B} → ¬ (` Nat ~ (A ⇒ B))
  ¬~nf ()

  ¬~np : ∀{A B} → ¬ (` Nat ~ (A `× B))
  ¬~np ()

  ¬~ns : ∀{A B} → ¬ (` Nat ~ (A `⊎ B))
  ¬~ns ()

  ¬~bn : ¬ (` 𝔹 ~ ` Nat)
  ¬~bn ()

  ¬~bf : ∀{A B} → ¬ (` 𝔹 ~ (A ⇒ B))
  ¬~bf ()

  ¬~bp : ∀{A B} → ¬ (` 𝔹 ~ (A `× B))
  ¬~bp ()


  ¬~bs : ∀{A B} → ¬ (` 𝔹 ~ (A `⊎ B))
  ¬~bs ()

  ¬~fn : ∀{A B} → ¬ ((A ⇒ B) ~ ` Nat)
  ¬~fn ()

  ¬~fb : ∀{A B} → ¬ ((A ⇒ B) ~ ` 𝔹)
  ¬~fb ()

  ¬~fp : ∀{A B A' B'} → ¬ ((A ⇒ B) ~ (A' `× B'))
  ¬~fp ()

  ¬~fs : ∀{A B A' B'} → ¬ ((A ⇒ B) ~ (A' `⊎ B'))
  ¬~fs ()

  ¬~pn : ∀{A B} → ¬ ((A `× B) ~ ` Nat)
  ¬~pn ()

  ¬~pb : ∀{A B} → ¬ ((A `× B) ~ ` 𝔹)
  ¬~pb ()

  ¬~pf : ∀{A B A' B'} → ¬ ((A `× B) ~ (A' ⇒ B'))
  ¬~pf ()

  ¬~ps : ∀{A B A' B'} → ¬ ((A `× B) ~ (A' `⊎ B'))
  ¬~ps ()

  ¬~sn : ∀{A B} → ¬ ((A `⊎ B) ~ ` Nat)
  ¬~sn ()

  ¬~sb : ∀{A B} → ¬ ((A `⊎ B) ~ ` 𝔹)
  ¬~sb ()

  ¬~sf : ∀{A B A' B'} → ¬ ((A `⊎ B) ~ (A' ⇒ B'))
  ¬~sf ()

  ¬~sp : ∀{A B A' B'} → ¬ ((A `⊎ B) ~ (A' `× B'))
  ¬~sp ()

  ¬~if : ∀{ι A B} → ¬ (` ι ~ (A ⇒ B))
  ¬~if ()

  ¬~ip : ∀{ι A B} → ¬ (` ι ~ (A `× B))
  ¬~ip ()

  ¬~is : ∀{ι A B} → ¬ (` ι ~ (A `⊎ B))
  ¬~is ()

  ¬~fi : ∀{ι A B} → ¬ ((A ⇒ B) ~ ` ι)
  ¬~fi ()

  ¬~pi : ∀{ι A B} → ¬ ((A `× B) ~ ` ι)
  ¬~pi ()

  ¬~si : ∀{ι A B} → ¬ ((A `⊎ B) ~ ` ι)
  ¬~si ()

  ¬~ii : ∀{ι ι'} → ¬ ι ≡ ι' → ¬ (` ι ~ ` ι')
  ¬~ii neq base~ = neq refl

  ¬~fL : ∀ {A B A' B'}
    → ¬ (A ~ B)
      ------------------------
    →  ¬ ((A ⇒ A') ~ (B ⇒ B'))
  ¬~fL {A} {B} {A'} {B'} d1 (fun~ c c₁) = d1 (Sym~ c)

  ¬~fR : ∀ {A B A' B'}
    → ¬ (A' ~ B')
      ------------------------
    →  ¬ ((A ⇒ A') ~ (B ⇒ B'))
  ¬~fR {A} {B} {A'} {B'} d1 (fun~ c c₁) = d1 c₁


  ¬~pL : ∀ {A B A' B'}
    → ¬ (A ~ B)
      ------------------------
    →  ¬ ((A `× A') ~ (B `× B'))
  ¬~pL {A} {B} {A'} {B'} d1 (pair~ c c₁) = d1 c


  ¬~pR : ∀ {A B A' B'}
    → ¬ (A' ~ B')
      ------------------------
    →  ¬ ((A `× A') ~ (B `× B'))
  ¬~pR {A} {B} {A'} {B'} d1 (pair~ c c₁) = d1 c₁

  ¬~sL : ∀ {A B A' B'}
    → ¬ (A ~ B)
      ------------------------
    →  ¬ ((A `⊎ A') ~ (B `⊎ B'))
  ¬~sL {A} {B} {A'} {B'} d1 (sum~ c c₁) = d1 c

  ¬~sR : ∀ {A B A' B'}
    → ¬ (A' ~ B')
      ------------------------
    →  ¬ ((A `⊎ A') ~ (B `⊎ B'))
  ¬~sR {A} {B} {A'} {B'} d1 (sum~ c c₁) = d1 c₁

  ¬~r : ∀ {A B}
    → ¬ (A ~ B)
      -------------------
    → ¬ (Ref A ~ Ref B)
  ¬~r d (ref~ c) = d c

  ⊑Base→~Base : ∀{A ι} → A ⊑ ` ι → A ~ ` ι
  ⊑Base→~Base unk⊑ = unk~L
  ⊑Base→~Base base⊑ = base~

  _`~_ : (A : Type) → (B : Type) → Dec (A ~ B)
  ⋆ `~ B = yes unk~L
  (` ι) `~ ⋆ = yes unk~R
  (` ι) `~ (` ι') with base-eq? ι ι'
  ... | yes eq rewrite eq = yes base~
  ... | no neq = no G
     where G : ¬ ` ι ~ ` ι'
           G base~ = neq refl
  (` ι) `~ (B ⇒ B₁) = no (λ ())
  (` ι) `~ (B `× B₁) = no (λ ())
  (` ι) `~ (B `⊎ B₁) = no (λ ())
  (` ι) `~ (Ref B) = no (λ ())
  (A ⇒ A₁) `~ ⋆ = yes unk~R
  (A ⇒ A₁) `~ (B ⇒ B₁)
      with A `~ B | A₁ `~ B₁
  ... | yes ab | yes a1b1 = yes (fun~ (Sym~ ab) a1b1)
  ... | yes ab | no a1b1 = no (¬~fR a1b1)
  ... | no ab  | _ = no (¬~fL ab)
  (A ⇒ A₁) `~ (` ι) = no (λ ())
  (A ⇒ A₁) `~ (B `× B₁) = no (λ ())
  (A ⇒ A₁) `~ (B `⊎ B₁) = no (λ ())
  (A ⇒ A₁) `~ (Ref B) = no (λ ())
  (A `× A₁) `~ ⋆ = yes unk~R
  (A `× A₁) `~ (B `× B₁)
      with A `~ B | A₁ `~ B₁
  ... | yes ab | yes a1b1 = yes (pair~ ab a1b1)
  ... | yes ab | no a1b1 = no (¬~pR a1b1)
  ... | no ab  | _ = no (¬~pL ab)
  (A `× A₁) `~ (` ι) = no (λ ())
  (A `× A₁) `~ (B ⇒ B₁) = no (λ ())
  (A `× A₁) `~ (B `⊎ B₁) = no (λ ())
  (A `× A₁) `~ (Ref B) = no (λ ())
  (A `⊎ A₁) `~ ⋆ = yes unk~R
  (A `⊎ A₁) `~ (B `⊎ B₁)
      with A `~ B | A₁ `~ B₁
  ... | yes ab | yes a1b1 = yes (sum~ ab a1b1)
  ... | yes ab | no a1b1 = no (¬~sR a1b1)
  ... | no ab  | _ = no (¬~sL ab)
  (A `⊎ A₁) `~ (` ι) = no (λ ())
  (A `⊎ A₁) `~ (B ⇒ B₁) = no (λ ())
  (A `⊎ A₁) `~ (B `× B₁) = no (λ ())
  (A `⊎ A₁) `~ (Ref B) = no (λ ())
  (Ref A) `~ ⋆ = yes unk~R
  (Ref A) `~ (Ref B)
    with A `~ B
  ... | yes ab = yes (ref~ ab)
  ... | no nab = no (¬~r nab)
  (Ref A) `~ (` ι) = no (λ ())
  (Ref A) `~ (B ⇒ B₁) = no (λ ())
  (Ref A) `~ (B `× B₁) = no (λ ())
  (Ref A) `~ (B `⊎ B₁) = no (λ ())



  ~-relevant : ∀{A B} → .(A ~ B) → A ~ B
  ~-relevant {A}{B} A~B
      with A `~ B
  ... | yes A~B' = A~B'
  ... | no A~̸B = ⊥-elim (A~̸B A~B)

  eq-unk : (A : Type) → Dec (A ≡ ⋆)
  eq-unk ⋆ = yes refl
  eq-unk (` ι) = no (λ ())
  eq-unk (A ⇒ A₁) = no (λ ())
  eq-unk (A `× A₁) = no (λ ())
  eq-unk (A `⊎ A₁) = no (λ ())
  eq-unk (Ref A) = no λ ()

  eq-unk-relevant : ∀{A} → .(A ≢ ⋆) → (A ≢ ⋆)
  eq-unk-relevant {A} A≢⋆
      with eq-unk A
  ... | yes A≡⋆ = ⊥-elim (A≢⋆ A≡⋆)
  ... | no neq = neq


{-
  ~⇒L : ∀{A B A' B'} → .((A ⇒ B) ~ (A' ⇒ B')) → A ~ A'
  ~⇒L {A}{B}{A'}{B'} c
      with A `~ A'
  ... | yes A~A' = A~A'
  ... | no ¬A~A' = ⊥-elim (¬~fL ¬A~A' c)

  ~⇒R : ∀{A B A' B'} → .((A ⇒ B) ~ (A' ⇒ B')) → B ~ B'
  ~⇒R {A}{B}{A'}{B'} c
      with B `~ B'
  ... | yes B~B' = B~B'
  ... | no ¬B~B' = ⊥-elim (¬~fR ¬B~B' c)

  ~×L : ∀{A B A' B'} → .((A `× B) ~ (A' `× B')) → A ~ A'
  ~×L {A}{B}{A'}{B'} c
      with A `~ A'
  ... | yes A~A' = A~A'
  ... | no ¬A~A' = ⊥-elim (¬~pL ¬A~A' c)

  ~×R : ∀{A B A' B'} → .((A `× B) ~ (A' `× B')) → B ~ B'
  ~×R {A}{B}{A'}{B'} c
      with B `~ B'
  ... | yes B~B' = B~B'
  ... | no ¬B~B' = ⊥-elim (¬~pR ¬B~B' c)

  ~⊎L : ∀{A B A' B'} → .((A `⊎ B) ~ (A' `⊎ B')) → A ~ A'
  ~⊎L {A}{B}{A'}{B'} c
      with A `~ A'
  ... | yes A~A' = A~A'
  ... | no ¬A~A' = ⊥-elim (¬~sL ¬A~A' c)

  ~⊎R : ∀{A B A' B'} → .((A `⊎ B) ~ (A' `⊎ B')) → B ~ B'
  ~⊎R {A}{B}{A'}{B'} c
      with B `~ B'
  ... | yes B~B' = B~B'
  ... | no ¬B~B' = ⊥-elim (¬~sR ¬B~B' c)
-}

  {- Shallow Consistency, used in Lazy Casts -}

  infix 6 _⌣_
  data _⌣_ : Type → Type → Set where
    unk⌣L : ∀ {A} → ⋆ ⌣ A

    unk⌣R : ∀ {A} → A ⌣ ⋆

    base⌣ : ∀{ι} → ` ι ⌣ ` ι

    fun⌣ : ∀ {A B A' B'}
        -------------------
      → (A ⇒ B) ⌣ (A' ⇒ B')

    pair⌣ : ∀ {A B A' B'}
        -------------------
      → (A `× B) ⌣ (A' `× B')

    sum⌣ : ∀ {A B A' B'}
        -------------------
      → (A `⊎ B) ⌣ (A' `⊎ B')

    ref⌣ : ∀ {A A'}
         -------------------
      → (Ref A) ⌣ (Ref A')


  _`⌣_ : (A : Type) → (B : Type) → Dec (A ⌣ B)
  ⋆ `⌣ B = yes unk⌣L
  (` ι) `⌣ ⋆ = yes unk⌣R
  (` ι) `⌣ (` ι')
      with base-eq? ι ι'
  ... | yes eq rewrite eq = yes base⌣
  ... | no neq = no G
        where G : ¬ ` ι ⌣ ` ι'
              G base⌣ = neq refl
  (` ι) `⌣ (B ⇒ B₁) = no (λ ())
  (` ι) `⌣ (B `× B₁) = no (λ ())
  (` ι) `⌣ (B `⊎ B₁) = no (λ ())
  (` ι) `⌣ (Ref B) = no λ ()
  (A ⇒ A₁) `⌣ ⋆ = yes unk⌣R
  (A ⇒ A₁) `⌣ (` x) = no (λ ())
  (A ⇒ A₁) `⌣ (B ⇒ B₁) = yes fun⌣
  (A ⇒ A₁) `⌣ (B `× B₁) = no (λ ())
  (A ⇒ A₁) `⌣ (B `⊎ B₁) = no (λ ())
  (A ⇒ A₁) `⌣ (Ref B) = no λ ()
  (A `× A₁) `⌣ ⋆ = yes unk⌣R
  (A `× A₁) `⌣ (` x) = no (λ ())
  (A `× A₁) `⌣ (B ⇒ B₁) = no (λ ())
  (A `× A₁) `⌣ (B `× B₁) = yes pair⌣
  (A `× A₁) `⌣ (B `⊎ B₁) = no (λ ())
  (A `× A₁) `⌣ (Ref B) = no λ ()
  (A `⊎ A₁) `⌣ ⋆ = yes unk⌣R
  (A `⊎ A₁) `⌣ (` x) = no (λ ())
  (A `⊎ A₁) `⌣ (B ⇒ B₁) = no (λ ())
  (A `⊎ A₁) `⌣ (B `× B₁) = no (λ ())
  (A `⊎ A₁) `⌣ (B `⊎ B₁) = yes sum⌣
  (A `⊎ A₁) `⌣ (Ref B) = no λ ()
  (Ref A) `⌣ ⋆ = yes unk⌣R
  (Ref A) `⌣ (` x) = no λ ()
  (Ref A) `⌣ (B ⇒ B₁) = no λ ()
  (Ref A) `⌣ (B `× B₁) = no λ ()
  (Ref A) `⌣ (B `⊎ B₁) = no λ ()
  (Ref A) `⌣ (Ref B) = yes ref⌣

  data Ground : Type → Set where
    G-Base : ∀{ι} → Ground (` ι)
    G-Fun : Ground (⋆ ⇒ ⋆)
    G-Pair : Ground (⋆ `× ⋆)
    G-Sum : Ground (⋆ `⊎ ⋆)
    G-Ref : Ground (Ref ⋆)

  GroundNotRel : ∀ {A} → (g1 g2 : Ground A) → g1 ≡ g2
  GroundNotRel {.(` _)} G-Base G-Base = refl
  GroundNotRel {.(⋆ ⇒ ⋆)} G-Fun G-Fun = refl
  GroundNotRel {.(⋆ `× ⋆)} G-Pair G-Pair = refl
  GroundNotRel {.(⋆ `⊎ ⋆)} G-Sum G-Sum = refl
  GroundNotRel {.(Ref ⋆)} G-Ref G-Ref = refl

  not-ground⋆ : ¬ Ground ⋆
  not-ground⋆ ()

  ground⇒1 : ∀{A}{B} → Ground (A ⇒ B) → A ≢ ⋆ → Bot
  ground⇒1 G-Fun nd = nd refl

  ground⇒2 : ∀{A}{B} → Ground (A ⇒ B) → B ≢ ⋆ → Bot
  ground⇒2 G-Fun nd = nd refl

  ground×1 : ∀{A}{B} → Ground (A `× B) → A ≢ ⋆ → Bot
  ground×1 G-Pair nd = nd refl

  ground×2 : ∀{A}{B} → Ground (A `× B) → B ≢ ⋆ → Bot
  ground×2 G-Pair nd = nd refl

  ground⊎1 : ∀{A}{B} → Ground (A `⊎ B) → A ≢ ⋆ → Bot
  ground⊎1 G-Sum nd = nd refl

  ground⊎2 : ∀{A}{B} → Ground (A `⊎ B) → B ≢ ⋆ → Bot
  ground⊎2 G-Sum nd = nd refl

  ground : (A : Type) → .{nd : A ≢ ⋆} → Σ[ B ∈ Type ] Ground B × (A ~ B)
  ground ⋆ {nd} = ⊥-elim (nd refl)
  ground (` ι) {nd} = ⟨ ` ι , ⟨ G-Base , base~ ⟩ ⟩
  ground (A ⇒ A₁) {nd} = ⟨ ⋆ ⇒ ⋆ , ⟨ G-Fun , fun~ unk~L unk~R ⟩ ⟩
  ground (A `× A₁) {nd} = ⟨ ⋆ `× ⋆ , ⟨ G-Pair , pair~ unk~R unk~R ⟩ ⟩
  ground (A `⊎ A₁) {nd} = ⟨ ⋆ `⊎ ⋆ , ⟨ G-Sum , sum~ unk~R unk~R ⟩ ⟩
  ground (Ref A) {nd} = ⟨ Ref ⋆ , ⟨ G-Ref , ref~ unk~R ⟩ ⟩

  ground? : (A : Type) → Dec (Ground A)
  ground? ⋆ = no λ x → contradiction x not-ground⋆
  ground? (` ι) = yes (G-Base)
  ground? (A₁ `× A₂) with eq-unk A₁ | eq-unk A₂
  ... | yes eq1 | yes eq2 rewrite eq1 | eq2 = yes G-Pair
  ... | yes eq1 | no eq2 rewrite eq1 = no λ x → ground×2 x eq2
  ... | no eq1 | _ = no λ x → ground×1 x eq1
  ground? (A₁ `⊎ A₂) with eq-unk A₁ | eq-unk A₂
  ... | yes eq1 | yes eq2 rewrite eq1 | eq2 = yes G-Sum
  ... | yes eq1 | no eq2 rewrite eq1 = no λ x → ground⊎2 x eq2
  ... | no eq1 | _ = no λ x → ground⊎1 x eq1
  ground? (A₁ ⇒ A₂) with eq-unk A₁ | eq-unk A₂
  ... | yes eq1 | yes eq2 rewrite eq1 | eq2 = yes G-Fun
  ... | yes eq1 | no eq2 rewrite eq1 = no λ x → ground⇒2 x eq2
  ... | no eq1 | _ = no λ x → ground⇒1 x eq1
  ground? (Ref A) with eq-unk A
  ... | yes eq rewrite eq = yes G-Ref
  ... | no neq = no λ { G-Ref → contradiction refl neq }

  gnd-eq? : (A : Type) → (B : Type) → {a : Ground A} → {b : Ground B}
          → Dec (A ≡ B)
  gnd-eq? A B {G-Base {ι = ι}} {G-Base {ι = ι'}}
      with base-eq? ι ι'
  ... | yes eq rewrite eq = yes refl
  ... | no neq = no G
        where G : ¬ ` ι ≡ ` ι'
              G refl = neq refl
  gnd-eq? (` ι) .(⋆ ⇒ ⋆) {G-Base} {G-Fun} = no λ ()
  gnd-eq? (` ι) .(⋆ `× ⋆) {G-Base} {G-Pair} = no (λ ())
  gnd-eq? (` ι) .(⋆ `⊎ ⋆) {G-Base} {G-Sum} = no (λ ())
  gnd-eq? .(⋆ ⇒ ⋆) (` ι) {G-Fun} {G-Base} = no λ ()
  gnd-eq? .(⋆ ⇒ ⋆) .(⋆ ⇒ ⋆) {G-Fun} {G-Fun} = yes refl
  gnd-eq? .(⋆ ⇒ ⋆) .(⋆ `× ⋆) {G-Fun} {G-Pair} = no (λ ())
  gnd-eq? .(⋆ ⇒ ⋆) .(⋆ `⊎ ⋆) {G-Fun} {G-Sum} = no (λ ())
  gnd-eq? .(⋆ `× ⋆) (` ι) {G-Pair} {G-Base} = no (λ ())
  gnd-eq? .(⋆ `× ⋆) .(⋆ ⇒ ⋆) {G-Pair} {G-Fun} = no (λ ())
  gnd-eq? .(⋆ `× ⋆) .(⋆ `× ⋆) {G-Pair} {G-Pair} = yes refl
  gnd-eq? .(⋆ `× ⋆) .(⋆ `⊎ ⋆) {G-Pair} {G-Sum} = no (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) (` ι) {G-Sum} {G-Base} = no (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) .(⋆ ⇒ ⋆) {G-Sum} {G-Fun} = no (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) .(⋆ `× ⋆) {G-Sum} {G-Pair} = no (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) .(⋆ `⊎ ⋆) {G-Sum} {G-Sum} = yes refl

  consis-ground-eq : ∀{A B : Type} → (c : A ⌣ B) →
      (gA : Ground A) → (gB : Ground B)
      → A ≡ B
  consis-ground-eq {(` _)} {(` _)} base⌣ gA gB = refl
  consis-ground-eq {(⋆ ⇒ ⋆)} {(_ ⇒ _)} fun⌣ G-Fun G-Fun = refl
  consis-ground-eq {(_ `× _)} {(_ `× _)} pair⌣ G-Pair G-Pair = refl
  consis-ground-eq {(_ `⊎ _)} {(_ `⊎ _)} sum⌣ G-Sum G-Sum = refl

  ¬⌣if : ∀{ι A B} → ¬ (` ι ⌣ (A ⇒ B))
  ¬⌣if ()

  ¬⌣ip : ∀{ι A B} → ¬ (` ι ⌣ (A `× B))
  ¬⌣ip ()

  ¬⌣is : ∀{ι A B} → ¬ (` ι ⌣ (A `⊎ B))
  ¬⌣is ()

  ¬⌣fi : ∀{ι A B} → ¬ ((A ⇒ B) ⌣ ` ι)
  ¬⌣fi ()

  ¬⌣pi : ∀{ι A B} → ¬ ((A `× B) ⌣ ` ι)
  ¬⌣pi ()

  ¬⌣si : ∀{ι A B} → ¬ ((A `⊎ B) ⌣ ` ι)
  ¬⌣si ()

  ¬⌣ii : ∀{ι ι'} → ¬ ι ≡ ι' → ¬ (` ι ⌣ ` ι')
  ¬⌣ii neq base⌣ = neq refl

  ⨆ : ∀{A B : Type} → (c : A ~ B) → Type
  ⨆ {.⋆} {B} unk~L = B
  ⨆ {A} {.⋆} unk~R = A
  ⨆ {(` ι)} {.(` _)} base~ = ` ι
  ⨆ {.(_ ⇒ _)} {.(_ ⇒ _)} (fun~ c d) = (⨆ c) ⇒ (⨆ d)
  ⨆ {.(_ `× _)} {.(_ `× _)} (pair~ c d) = (⨆ c) `× (⨆ d)
  ⨆ {.(_ `⊎ _)} {.(_ `⊎ _)} (sum~ c d) = (⨆ c) `⊎ (⨆ d)


  ⨆~ : ∀{B C}
      → (bc : B ~ C)
      → C ~ ⨆ bc

  ~⨆ : ∀{B C}
      → (bc : B ~ C)
      → B ~ ⨆ bc
  ~⨆ unk~L = unk~L
  ~⨆ unk~R = Refl~
  ~⨆ base~ = Refl~
  ~⨆ (fun~ aa bb) = fun~ (Sym~ (⨆~ aa)) (~⨆ bb)
  ~⨆ (pair~ aa bb) = pair~ (~⨆ aa) (~⨆ bb)
  ~⨆ (sum~ aa bb) = sum~ (~⨆ aa) (~⨆ bb)

  ⨆~ unk~L = Refl~
  ⨆~ unk~R = unk~L
  ⨆~ base~ = Refl~
  ⨆~ (fun~ aa bb) = fun~ (Sym~ (~⨆ aa)) (⨆~ bb)
  ⨆~ (pair~ aa bb) = pair~ (⨆~ aa) (⨆~ bb)
  ⨆~ (sum~ aa bb) = sum~ (⨆~ aa) (⨆~ bb)

  {- Type matching -}
  data _▹_⇒_ : Type → Type → Type → Set where
    match⇒⇒ : ∀{A B} → (A ⇒ B) ▹ A ⇒ B
    match⇒⋆ : ⋆ ▹ ⋆ ⇒ ⋆

  data _▹_×_ : Type → Type → Type → Set where
    match×× : ∀{A B} → (A `× B) ▹ A × B
    match×⋆ : ⋆ ▹ ⋆ × ⋆

  data _▹_⊎_ : Type → Type → Type → Set where
    match⊎⊎ : ∀{A B} → (A `⊎ B) ▹ A ⊎ B
    match⊎⋆ : ⋆ ▹ ⋆ ⊎ ⋆

  ▹⇒⊑ : ∀{C A B} → C ▹ A ⇒ B → C ⊑ A ⇒ B
  ▹⇒⊑ match⇒⇒ = fun⊑ Refl⊑ Refl⊑
  ▹⇒⊑ match⇒⋆ = unk⊑

  ▹×⊑ : ∀{C A B} → C ▹ A × B → C ⊑ A `× B
  ▹×⊑ match×× = pair⊑ Refl⊑ Refl⊑
  ▹×⊑ match×⋆ = unk⊑

  ▹⊎⊑ : ∀{C A B} → C ▹ A ⊎ B → C ⊑ A `⊎ B
  ▹⊎⊑ match⊎⊎ = sum⊑ Refl⊑ Refl⊑
  ▹⊎⊑ match⊎⋆ = unk⊑

  ▹⇒-pres-prec : ∀ {A A′ A₁ A₁′ A₂ A₂′}
    → (m : A ▹ A₁ ⇒ A₂) → (m′ : A′ ▹ A₁′ ⇒ A₂′)
    → A ⊑ A′
      --------------------
    → A₁ ⊑ A₁′ × A₂ ⊑ A₂′
  ▹⇒-pres-prec match⇒⇒ match⇒⇒ (fun⊑ lp₁ lp₂) = ⟨ lp₁ , lp₂ ⟩
  ▹⇒-pres-prec match⇒⇒ match⇒⋆ ()
  ▹⇒-pres-prec match⇒⋆ match⇒⇒ lp = ⟨ unk⊑ , unk⊑ ⟩
  ▹⇒-pres-prec match⇒⋆ match⇒⋆ lp = ⟨ unk⊑ , unk⊑ ⟩

  ▹×-pres-prec : ∀ {A A′ A₁ A₁′ A₂ A₂′}
    → (m : A ▹ A₁ × A₂) → (m′ : A′ ▹ A₁′ × A₂′)
    → A ⊑ A′
      --------------------
    → A₁ ⊑ A₁′ × A₂ ⊑ A₂′
  ▹×-pres-prec match×× match×× (pair⊑ lp₁ lp₂) = ⟨ lp₁ , lp₂ ⟩
  ▹×-pres-prec match×× match×⋆ = λ ()
  ▹×-pres-prec match×⋆ match×× lp = ⟨ unk⊑ , unk⊑ ⟩
  ▹×-pres-prec match×⋆ match×⋆ lp = ⟨ lp , lp ⟩

  ▹⊎-pres-prec : ∀ {A A′ A₁ A₁′ A₂ A₂′}
    → (m : A ▹ A₁ ⊎ A₂) (m′ : A′ ▹ A₁′ ⊎ A₂′)
    → A ⊑ A′
      --------------------
    → A₁ ⊑ A₁′ × A₂ ⊑ A₂′
  ▹⊎-pres-prec match⊎⊎ match⊎⊎ (sum⊑ lp₁ lp₂) = ⟨ lp₁ , lp₂ ⟩
  ▹⊎-pres-prec match⊎⋆ match⊎⊎ lp = ⟨ unk⊑ , unk⊑ ⟩
  ▹⊎-pres-prec match⊎⋆ match⊎⋆ lp = ⟨ lp , lp ⟩

  ⨆-pres-prec : ∀ {A A′ B B′}
    → (aa : A ~ A′) → (bb : B ~ B′)
    → A ⊑ B
    → A′ ⊑ B′
      -------------
    → ⨆ aa ⊑ ⨆ bb
  ⨆-pres-prec unk~L unk~L unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~L unk~R unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~L base~ unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~L (fun~ _ _) unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~L (pair~ _ _) unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~L (sum~ _ _) unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~R unk~L unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~R unk~R unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~R base~ unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~R (fun~ _ _) unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~R (pair~ _ _) unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~R (sum~ _ _) unk⊑ unk⊑ = unk⊑
  ⨆-pres-prec unk~L unk~L unk⊑ base⊑ = base⊑
  ⨆-pres-prec unk~L base~ unk⊑ base⊑ = base⊑
  ⨆-pres-prec unk~L unk~L unk⊑ (fun⊑ lp₁ lp₂) = fun⊑ lp₁ lp₂
  ⨆-pres-prec unk~L (fun~ aa bb) unk⊑ (fun⊑ lp₁ lp₂) =
    fun⊑ (⨆-pres-prec unk~R aa lp₁ unk⊑) (⨆-pres-prec unk~L bb unk⊑ lp₂)
  ⨆-pres-prec unk~L unk~L unk⊑ (pair⊑ lp₁ lp₂) = pair⊑ lp₁ lp₂
  ⨆-pres-prec unk~L (pair~ aa bb) unk⊑ (pair⊑ lp₁ lp₂) =
    pair⊑ (⨆-pres-prec unk~L aa unk⊑ lp₁) (⨆-pres-prec unk~L bb unk⊑ lp₂)
  ⨆-pres-prec unk~L unk~L unk⊑ (sum⊑ lp₁ lp₂) = sum⊑ lp₁ lp₂
  ⨆-pres-prec unk~L (sum~ aa bb) unk⊑ (sum⊑ lp₁ lp₂) =
    sum⊑ (⨆-pres-prec unk~L aa unk⊑ lp₁) (⨆-pres-prec unk~L bb unk⊑ lp₂)
  ⨆-pres-prec unk~R unk~R base⊑ unk⊑ = base⊑
  ⨆-pres-prec unk~R base~ base⊑ unk⊑ = base⊑
  ⨆-pres-prec base~ base~ base⊑ base⊑ = base⊑
  ⨆-pres-prec unk~R unk~R (fun⊑ lp₁ lp₂) unk⊑ = fun⊑ lp₁ lp₂
  ⨆-pres-prec unk~R (fun~ aa bb) (fun⊑ lp₁ lp₂) unk⊑ =
    fun⊑ (⨆-pres-prec unk~L aa unk⊑ lp₁) (⨆-pres-prec unk~R bb lp₂ unk⊑)
  ⨆-pres-prec (fun~ aa₁ aa₂) (fun~ bb₁ bb₂) (fun⊑ lpa₁ lpa₂) (fun⊑ lpb₁ lpb₂) =
    fun⊑ (⨆-pres-prec aa₁ bb₁ lpb₁ lpa₁) (⨆-pres-prec aa₂ bb₂ lpa₂ lpb₂)
  ⨆-pres-prec unk~R unk~R (pair⊑ lp₁ lp₂) unk⊑ = pair⊑ lp₁ lp₂
  ⨆-pres-prec unk~R (pair~ bb₁ bb₂) (pair⊑ lp₁ lp₂) unk⊑ =
    pair⊑ (⨆-pres-prec unk~R bb₁ lp₁ unk⊑) (⨆-pres-prec unk~R bb₂ lp₂ unk⊑)
  ⨆-pres-prec (pair~ aa₁ aa₂) (pair~ bb₁ bb₂) (pair⊑ lpa₁ lpa₂) (pair⊑ lpb₁ lpb₂) =
    pair⊑ (⨆-pres-prec aa₁ bb₁ lpa₁ lpb₁) (⨆-pres-prec aa₂ bb₂ lpa₂ lpb₂)
  ⨆-pres-prec unk~R unk~R (sum⊑ lp₁ lp₂) unk⊑ = sum⊑ lp₁ lp₂
  ⨆-pres-prec unk~R (sum~ bb₁ bb₂) (sum⊑ lp₁ lp₂) unk⊑ =
    sum⊑ (⨆-pres-prec unk~R bb₁ lp₁ unk⊑) (⨆-pres-prec unk~R bb₂ lp₂ unk⊑)
  ⨆-pres-prec (sum~ aa₁ aa₂) (sum~ bb₁ bb₂) (sum⊑ lpa₁ lpa₂) (sum⊑ lpb₁ lpb₂) =
    sum⊑ (⨆-pres-prec aa₁ bb₁ lpa₁ lpb₁) (⨆-pres-prec aa₂ bb₂ lpa₂ lpb₂)

  -- If two types are consistent then their less precise counterparts are consistent too.
  lp-consis : ∀ {A A′ B B′}
    → A′ ~ B′
    → A ⊑ A′ → B ⊑ B′
      -----------------
    → A ~ B
  lp-consis unk~L unk⊑ lpB = unk~L
  lp-consis unk~R unk⊑ lpB = unk~L
  lp-consis unk~R base⊑ unk⊑ = unk~R
  lp-consis unk~R (fun⊑ _ _) unk⊑ = unk~R
  lp-consis unk~R (pair⊑ _ _) unk⊑ = unk~R
  lp-consis unk~R (sum⊑ _ _) unk⊑ = unk~R
  lp-consis base~ unk⊑ lpB = unk~L
  lp-consis base~ base⊑ unk⊑ = unk~R
  lp-consis base~ base⊑ base⊑ = base~
  lp-consis (fun~ c~ c~₁) unk⊑ lpB = unk~L
  lp-consis (fun~ c~ c~₁) (fun⊑ lpA lpA₁) unk⊑ = unk~R
  lp-consis (fun~ c~₁ c~₂) (fun⊑ lpA₁ lpA₂) (fun⊑ lpB₁ lpB₂) = fun~ (lp-consis c~₁ lpB₁ lpA₁) (lp-consis c~₂ lpA₂ lpB₂)
  lp-consis (pair~ c~₁ c~₂) unk⊑ lpB = unk~L
  lp-consis (pair~ c~₁ c~₂) (pair⊑ lpA₁ lpA₂) unk⊑ = unk~R
  lp-consis (pair~ c~₁ c~₂) (pair⊑ lpA₁ lpA₂) (pair⊑ lpB₁ lpB₂) = pair~ (lp-consis c~₁ lpA₁ lpB₁) (lp-consis c~₂ lpA₂ lpB₂)
  lp-consis (sum~ c~₁ c~₂) unk⊑ lpB = unk~L
  lp-consis (sum~ c~₁ c~₂) (sum⊑ lpA₁ lpA₂) unk⊑ = unk~R
  lp-consis (sum~ c~₁ c~₂) (sum⊑ lpA₁ lpA₂) (sum⊑ lpB₁ lpB₂) = sum~ (lp-consis c~₁ lpA₁ lpB₁) (lp-consis c~₂ lpA₂ lpB₂)

  lp-¬⋆ : ∀ {T T′}
    → T ≢ ⋆ → T ⊑ T′
      ---------------
    → T′ ≢ ⋆
  lp-¬⋆ nd unk⊑ = contradiction refl nd
  lp-¬⋆ nd base⊑ = nd
  lp-¬⋆ nd (fun⊑ lp lp₁) = λ ()
  lp-¬⋆ nd (pair⊑ lp lp₁) = λ ()
  lp-¬⋆ nd (sum⊑ lp lp₁) = λ ()

  {- Suppose G₁ , G₂ are ground types,
    A   ~  B
    ⊔|     ⊔|
    G₁  ≡  G₂
  -}
  lp-consis-ground-eq : ∀ {A B G₁ G₂}
    → Ground G₁ → Ground G₂
    → A ~ B
    → G₁ ⊑ A → G₂ ⊑ B
      -----------------
    → G₁ ≡ G₂
  lp-consis-ground-eq g1 g2 unk~L unk⊑ unk⊑ = refl
  lp-consis-ground-eq () g2 unk~L unk⊑ base⊑
  lp-consis-ground-eq () g2 unk~L unk⊑ (fun⊑ lp2 lp3)
  lp-consis-ground-eq () g2 unk~L unk⊑ (pair⊑ lp2 lp3)
  lp-consis-ground-eq () g2 unk~L unk⊑ (sum⊑ lp2 lp3)
  lp-consis-ground-eq g1 () unk~R base⊑ unk⊑
  lp-consis-ground-eq g1 () unk~R (fun⊑ lp1 lp3) unk⊑
  lp-consis-ground-eq g1 () unk~R (pair⊑ lp1 lp3) unk⊑
  lp-consis-ground-eq g1 () unk~R (sum⊑ lp1 lp3) unk⊑
  lp-consis-ground-eq g1 g2 base~ base⊑ base⊑ = refl
  lp-consis-ground-eq G-Fun G-Fun (fun~ c c₁) lp1 lp2 = refl
  lp-consis-ground-eq G-Pair G-Pair (pair~ c c₁) lp1 lp2 = refl
  lp-consis-ground-eq G-Sum G-Sum (sum~ c c₁) lp1 lp2 = refl

  {- Suppose B ≢ ⋆ (otherwise G₁ and G₂ may not be consistent), we have:
    A  ~  B  ~  C
    ⊔|          ⊔|
    G₁    ≡     G₂
  -}
  lp-double-consis-ground-eq : ∀ {A B C G₁ G₂}
    → Ground G₁ → Ground G₂
    → A ~ B → B ~ C
    → G₁ ⊑ A → G₂ ⊑ C
    → B ≢ ⋆
      -----------------
    → G₁ ≡ G₂
  lp-double-consis-ground-eq g1 g2 unk~R unk~L base⊑ base⊑ neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 base~ base~ base⊑ base⊑ neq = refl
  lp-double-consis-ground-eq g1 g2 unk~R unk~L base⊑ (fun⊑ lp2 lp3) neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~L base⊑ (pair⊑ lp2 lp3) neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~L base⊑ (sum⊑ lp2 lp3) neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~L (fun⊑ lp1 lp3) lp2 neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~R (fun⊑ lp1 lp3) lp2 neq = contradiction refl neq
  lp-double-consis-ground-eq g1 () (fun~ c1 c3) unk~R (fun⊑ lp1 lp3) unk⊑ neq
  lp-double-consis-ground-eq G-Fun G-Fun (fun~ c1 c3) (fun~ c2 c4) (fun⊑ lp1 lp3) (fun⊑ lp2 lp4) neq = refl
  lp-double-consis-ground-eq g1 g2 unk~R unk~L (pair⊑ lp1 lp3) base⊑ neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~L (pair⊑ lp1 lp3) (fun⊑ lp2 lp4) neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~L (pair⊑ lp1 lp3) (pair⊑ lp2 lp4) neq = contradiction refl neq
  lp-double-consis-ground-eq G-Pair G-Pair (pair~ c1 c3) c2 (pair⊑ lp1 lp3) (pair⊑ lp2 lp4) neq = refl
  lp-double-consis-ground-eq g1 g2 unk~R unk~L (pair⊑ lp1 lp3) (sum⊑ lp2 lp4) neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~L (sum⊑ lp1 lp3) lp2 neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~R (sum⊑ lp1 lp3) lp2 neq = contradiction refl neq
  lp-double-consis-ground-eq g1 () (sum~ c1 c3) unk~R (sum⊑ lp1 lp3) unk⊑ neq
  lp-double-consis-ground-eq G-Sum G-Sum (sum~ c1 c3) (sum~ c2 c4) (sum⊑ lp1 lp3) (sum⊑ lp2 lp4) neq = refl
  lp-double-consis-ground-eq g1 () c1 unk~R base⊑ unk⊑ neq
  lp-double-consis-ground-eq g1 g2 unk~R unk~R (pair⊑ _ _) lp2 neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~L unk~L unk⊑ lp2 neq = contradiction refl neq
  lp-double-consis-ground-eq g1 g2 unk~L unk~R unk⊑ unk⊑ neq = refl
  lp-double-consis-ground-eq () g2 unk~L base~ unk⊑ lp2 neq
  lp-double-consis-ground-eq () g2 unk~L (fun~ c2 c3) unk⊑ lp2 neq
  lp-double-consis-ground-eq () g2 unk~L (pair~ c2 c3) unk⊑ lp2 neq
  lp-double-consis-ground-eq () g2 unk~L (sum~ c2 c3) unk⊑ lp2 neq

  -- The ground type ⋆ ⇒ ⋆ sits at the bottom of the precision lattice of all function types.
  ground-fun-⊑ : ∀ {A B} → ⋆ ⇒ ⋆ ⊑ A ⇒ B
  ground-fun-⊑ = fun⊑ unk⊑ unk⊑

  ground-pair-⊑ : ∀ {A B} → ⋆ `× ⋆ ⊑ A `× B
  ground-pair-⊑ = pair⊑ unk⊑ unk⊑

  ground-sum-⊑ : ∀ {A B} → ⋆ `⊎ ⋆ ⊑ A `⊎ B
  ground-sum-⊑ = sum⊑ unk⊑ unk⊑

  -- A type that is less precise than a ground type and not ⋆ must also be ground.
  ⊑G-nd-ground : ∀ {A G}
    → Ground G → A ⊑ G  → A ≢ ⋆
      -----------------------------
    → Ground A
  ⊑G-nd-ground G-Base unk⊑ x = contradiction refl x
  ⊑G-nd-ground G-Base base⊑ x = G-Base
  ⊑G-nd-ground G-Fun unk⊑ x = contradiction refl x
  ⊑G-nd-ground G-Fun (fun⊑ unk⊑ unk⊑) x = G-Fun
  ⊑G-nd-ground G-Pair unk⊑ x = contradiction refl x
  ⊑G-nd-ground G-Pair (pair⊑ unk⊑ unk⊑) x = G-Pair
  ⊑G-nd-ground G-Sum unk⊑ x = contradiction refl x
  ⊑G-nd-ground G-Sum (sum⊑ unk⊑ unk⊑) x = G-Sum

  nd⋢⋆ : ∀ {A} → A ≢ ⋆ → ¬ A ⊑ ⋆
  nd⋢⋆ nd unk⊑ = contradiction refl nd

  -- A ground type cannot be ⋆
  ground-nd : ∀ {G} → Ground G → G ≢ ⋆
  ground-nd G-Base ()
  ground-nd G-Fun ()
  ground-nd G-Pair ()
  ground-nd G-Sum ()

  -- Relax on precision by using the ground type G instead of A, suppose G ~ A.
  ⊑-ground-relax : ∀ {A B G}
    → Ground G
    → A ⊑ B → A ~ G → A ≢ ⋆
      ------------------------
    → G ⊑ B
  ⊑-ground-relax _ unk⊑ unk~L nd = contradiction refl nd
  ⊑-ground-relax _ base⊑ base~ nd = base⊑
  ⊑-ground-relax G-Fun (fun⊑ lp1 lp2) (fun~ c1 c2) nd = fun⊑ unk⊑ unk⊑
  ⊑-ground-relax G-Pair (pair⊑ lp1 lp2) (pair~ c1 c2) nd = pair⊑ unk⊑ unk⊑
  ⊑-ground-relax G-Sum (sum⊑ lp1 lp2) (sum~ c1 c2) nd = sum⊑ unk⊑ unk⊑

  ⊑-ground-consis : ∀ {G A B}
    → Ground G
    → G ⊑ A → A ~ B → B ≢ ⋆
      ------------------------
    → G ⊑ B
  ⊑-ground-consis G-Base base⊑ unk~R nd = contradiction refl nd
  ⊑-ground-consis G-Base base⊑ base~ nd = base⊑
  ⊑-ground-consis G-Fun (fun⊑ lp1 lp2) unk~R nd = contradiction refl nd
  ⊑-ground-consis G-Fun (fun⊑ lp1 lp2) (fun~ c1 c2) nd = fun⊑ unk⊑ unk⊑
  ⊑-ground-consis G-Pair (pair⊑ lp1 lp2) unk~R nd = contradiction refl nd
  ⊑-ground-consis G-Pair (pair⊑ lp1 lp2) (pair~ c1 c2) nd = pair⊑ unk⊑ unk⊑
  ⊑-ground-consis G-Sum (sum⊑ lp1 lp2) unk~R nd = contradiction refl nd
  ⊑-ground-consis G-Sum (sum⊑ lp1 lp2) (sum~ c1 c2) nd = sum⊑ unk⊑ unk⊑

  -- Suppose G ≡ ground A and H ≡ ground B
  ⊑-ground-monotone : ∀ {A B G H}
    → A ≢ ⋆ → B ≢ ⋆ → ¬ Ground A → ¬ Ground B
    → Ground G → Ground H
    → A ~ G → B ~ H
    → A ⊑ B
      ---------
    → G ⊑ H
  ⊑-ground-monotone a-nd b-nd a-ng b-ng g h c1 c2 unk⊑ = contradiction refl a-nd
  ⊑-ground-monotone a-nd b-nd a-ng b-ng g h c1 c2 base⊑ = contradiction G-Base a-ng
  ⊑-ground-monotone a-nd b-nd a-ng b-ng G-Fun G-Fun _ _ (fun⊑ lp1 lp2) = fun⊑ unk⊑ unk⊑
  ⊑-ground-monotone a-nd b-nd a-ng b-ng G-Pair G-Pair _ _ (pair⊑ lp1 lp2) = pair⊑ unk⊑ unk⊑
  ⊑-ground-monotone a-nd b-nd a-ng b-ng G-Sum G-Sum _ _ (sum⊑ lp1 lp2) = sum⊑ unk⊑ unk⊑

  ground-⊑-eq : ∀ {G H}
    → Ground G → Ground H
    → G ⊑ H
      ------
    → G ≡ H
  ground-⊑-eq G-Base G-Base base⊑ = refl
  ground-⊑-eq G-Fun G-Fun (fun⊑ _ _) = refl
  ground-⊑-eq G-Pair G-Pair (pair⊑ _ _) = refl
  ground-⊑-eq G-Sum G-Sum (sum⊑ _ _) = refl
