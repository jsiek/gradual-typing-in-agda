module Types where

  open import Data.Bool
  open import Data.Empty using () renaming (⊥ to Bot)
  open import Data.Empty.Irrelevant using (⊥-elim)
  open import Data.Integer using (ℤ)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit renaming (⊤ to Top)
  open import Primitives renaming (Prim to PrimD; Void to ⊥; rep to prim-rep)
     public
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)

  infix  7 _⇒_
  infix  9 _`×_
  infix  8 _`⊎_
  infix 10 `_

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


  data Atomic : Type → Set where
    A-Unk : Atomic ⋆
    A-Base : ∀{ι} → Atomic (` ι)

  base? : (A : Type) → Dec (Σ[ ι ∈ Base ] A ≡ ` ι)
  base? ⋆ = no G
    where G : ¬ Σ-syntax Base (λ ι → ⋆ ≡ ` ι)
          G ⟨ _ , () ⟩
  base? (` ι) = yes ⟨ ι , refl ⟩
  base? (A ⇒ A₁) =  no G
    where G : ¬ Σ-syntax Base (λ ι → A ⇒ A₁ ≡ ` ι)
          G ⟨ _ , () ⟩
  base? (A `× A₁) =  no G
    where G : ¬ Σ-syntax Base (λ ι → A `× A₁ ≡ ` ι)
          G ⟨ _ , () ⟩
  base? (A `⊎ A₁) =  no G
    where G : ¬ Σ-syntax Base (λ ι → A `⊎ A₁ ≡ ` ι)
          G ⟨ _ , () ⟩

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
  rep (t₁ ⇒ t₂) = (rep t₁) → (rep t₂)
  rep (t₁ `× t₂) = Bot
  rep (t `⊎ t₁) = Bot

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
  prim? ⋆ = no (λ ())
  prim? (` x) = yes P-Base
  prim? (A ⇒ B) with prim? B
  ... | no pb = no λ x → contradiction (P-Fun2 x) pb
  prim? (⋆ ⇒ B) | yes pb = no (λ ())
  prim? (` x ⇒ B) | yes pb = yes (P-Fun pb)
  prim? ((A ⇒ A₁) ⇒ B) | yes pb = no (λ ())
  prim? (A `× A₁ ⇒ B) | yes pb = no (λ ())
  prim? (A `⊎ A₁ ⇒ B) | yes pb = no (λ ())
  prim? (A `× A₁) = no (λ ())
  prim? (A `⊎ A₁) = no (λ ())

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

  Refl⊑ : ∀{A} → A ⊑ A
  Refl⊑ {⋆} = unk⊑
  Refl⊑ {` ι} = base⊑
  Refl⊑ {A ⇒ A₁} = fun⊑ Refl⊑ Refl⊑
  Refl⊑ {A `× A₁} = pair⊑ Refl⊑ Refl⊑
  Refl⊑ {A `⊎ A₁} = sum⊑ Refl⊑ Refl⊑

  Trans⊑ : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
  Trans⊑ unk⊑ b = unk⊑
  Trans⊑ base⊑ b = b
  Trans⊑ (fun⊑ a a₁) (fun⊑ b b₁) = fun⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)
  Trans⊑ (pair⊑ a a₁) (pair⊑ b b₁) = pair⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)
  Trans⊑ (sum⊑ a a₁) (sum⊑ b b₁) = sum⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)

  AntiSym⊑ : ∀ {A B} → A ⊑ B → B ⊑ A → A ≡ B
  AntiSym⊑ unk⊑ unk⊑ = refl
  AntiSym⊑ base⊑ base⊑ = refl
  AntiSym⊑ {A ⇒ B}{A' ⇒ B'} (fun⊑ a a₁) (fun⊑ b b₁) =
    cong₂ (_⇒_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)
  AntiSym⊑ (pair⊑ a a₁) (pair⊑ b b₁) =
    cong₂ (_`×_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)
  AntiSym⊑ (sum⊑ a a₁) (sum⊑ b b₁) =
    cong₂ (_`⊎_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)

  ⊑L⋆ : ∀{A} → A ⊑ ⋆ → A ≡ ⋆
  ⊑L⋆ {⋆} unk⊑ = refl

  ⊑RBase : ∀{C ι} → ` ι ⊑ C → C ≡ ` ι
  ⊑RBase {ι} base⊑ = refl

  ⊑LBase : ∀{A ι} → A ⊑ ` ι →  A ≡ (` ι) ⊎ A ≡ ⋆
  ⊑LBase {⋆} {ι} unk⊑ = inj₂ refl
  ⊑LBase {` ι} {ι} base⊑ = inj₁ refl

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
    base~ : ∀{ι} → ` ι ~ ` ι
    fun~ : ∀{A B A' B'}
      → A' ~ A  →  B ~ B'
        -------------------
      → (A ⇒ B) ~ (A' ⇒ B')
    pair~ : ∀{A B A' B'}
      → A ~ A'  →  B ~ B'
        -------------------
      → (A `× B) ~ (A' `× B')
    sum~ : ∀{A B A' B'}
      → A ~ A'  →  B ~ B'
        -------------------
      → (A `⊎ B) ~ (A' `⊎ B')

  Sym~ : ∀ {A B} → A ~ B → B ~ A
  Sym~ unk~L = unk~R
  Sym~ unk~R = unk~L
  Sym~ base~ = base~
  Sym~ (fun~ c c₁) = fun~ (Sym~ c) (Sym~ c₁)
  Sym~ (pair~ c c₁) = pair~ (Sym~ c) (Sym~ c₁)
  Sym~ (sum~ c c₁) = sum~ (Sym~ c) (Sym~ c₁)

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

  ⊑Base→~Base : ∀{A ι} → A ⊑ ` ι → A ~ ` ι
  ⊑Base→~Base unk⊑ = unk~L
  ⊑Base→~Base base⊑ = base~

{-
  base-eq? : (A : Base) → (B : Base) 
          → Dec (A ≡ B)
  base-eq? Nat Nat = yes refl
  base-eq? Nat Int = no (λ ())
  base-eq? Nat 𝔹 = no (λ ())
  base-eq? Nat Unit = no (λ ())
  base-eq? Nat ⊥ = no (λ ())
  base-eq? Int Nat = no (λ ())
  base-eq? Int Int = yes refl
  base-eq? Int 𝔹 = no (λ ())
  base-eq? Int Unit = no (λ ())
  base-eq? Int ⊥ = no (λ ())
  base-eq? 𝔹 Nat = no (λ ())
  base-eq? 𝔹 Int = no (λ ())
  base-eq? 𝔹 𝔹 = yes refl
  base-eq? 𝔹 Unit = no (λ ())
  base-eq? 𝔹 ⊥ = no (λ ())
  base-eq? Unit Nat = no (λ ())
  base-eq? Unit Int = no (λ ())
  base-eq? Unit 𝔹 = no (λ ())
  base-eq? Unit Unit = yes refl
  base-eq? Unit ⊥ = no (λ ())
  base-eq? ⊥ Nat = no (λ ())
  base-eq? ⊥ Int = no (λ ())
  base-eq? ⊥ 𝔹 = no (λ ())
  base-eq? ⊥ Unit = no (λ ())
  base-eq? ⊥ ⊥ = yes refl
-}

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
  (A ⇒ A₁) `~ ⋆ = yes unk~R
  (A ⇒ A₁) `~ (` ι) = no (λ ())
  (A ⇒ A₁) `~ (B ⇒ B₁)
      with A `~ B | A₁ `~ B₁
  ... | yes ab | yes a1b1 = yes (fun~ (Sym~ ab) a1b1)
  ... | yes ab | no a1b1 = no (¬~fR a1b1)
  ... | no ab  | _ = no (¬~fL ab)
  (A ⇒ A₁) `~ (B `× B₁) = no (λ ())
  (A ⇒ A₁) `~ (B `⊎ B₁) = no (λ ())
  (A `× A₁) `~ ⋆ = yes unk~R
  (A `× A₁) `~ (` ι) = no (λ ())
  (A `× A₁) `~ (B ⇒ B₁) = no (λ ())
  (A `× A₁) `~ (B `× B₁)
      with A `~ B | A₁ `~ B₁
  ... | yes ab | yes a1b1 = yes (pair~ ab a1b1)
  ... | yes ab | no a1b1 = no (¬~pR a1b1)
  ... | no ab  | _ = no (¬~pL ab)
  (A `× A₁) `~ (B `⊎ B₁) = no (λ ())
  (A `⊎ A₁) `~ ⋆ = yes unk~R
  (A `⊎ A₁) `~ (` ι) = no (λ ())
  (A `⊎ A₁) `~ (B ⇒ B₁) = no (λ ())
  (A `⊎ A₁) `~ (B `× B₁) = no (λ ())
  (A `⊎ A₁) `~ (B `⊎ B₁)
      with A `~ B | A₁ `~ B₁
  ... | yes ab | yes a1b1 = yes (sum~ ab a1b1)
  ... | yes ab | no a1b1 = no (¬~sR a1b1)
  ... | no ab  | _ = no (¬~sL ab)

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
    fun⌣ : ∀{A B A' B'}
        -------------------
      → (A ⇒ B) ⌣ (A' ⇒ B')
    pair⌣ : ∀{A B A' B'}
        -------------------
      → (A `× B) ⌣ (A' `× B')
    sum⌣ : ∀{A B A' B'}
        -------------------
      → (A `⊎ B) ⌣ (A' `⊎ B')

  _`⌣_ : (A : Type) → (B : Type) → Dec (A ⌣ B)
  ⋆ `⌣ B = yes unk⌣L
  (` x) `⌣ ⋆ = yes unk⌣R
  (` ι) `⌣ (` ι')
      with base-eq? ι ι'
  ... | yes eq rewrite eq = yes base⌣
  ... | no neq = no G
        where G : ¬ ` ι ⌣ ` ι'
              G base⌣ = neq refl
  (` ι) `⌣ (B ⇒ B₁) = no (λ ())
  (` ι) `⌣ (B `× B₁) = no (λ ())
  (` ι) `⌣ (B `⊎ B₁) = no (λ ())
  (A ⇒ A₁) `⌣ ⋆ = yes unk⌣R
  (A ⇒ A₁) `⌣ (` x) = no (λ ())
  (A ⇒ A₁) `⌣ (B ⇒ B₁) = yes fun⌣
  (A ⇒ A₁) `⌣ (B `× B₁) = no (λ ())
  (A ⇒ A₁) `⌣ (B `⊎ B₁) = no (λ ())
  (A `× A₁) `⌣ ⋆ = yes unk⌣R
  (A `× A₁) `⌣ (` x) = no (λ ())
  (A `× A₁) `⌣ (B ⇒ B₁) = no (λ ())
  (A `× A₁) `⌣ (B `× B₁) = yes pair⌣
  (A `× A₁) `⌣ (B `⊎ B₁) = no (λ ())
  (A `⊎ A₁) `⌣ ⋆ = yes unk⌣R
  (A `⊎ A₁) `⌣ (` x) = no (λ ())
  (A `⊎ A₁) `⌣ (B ⇒ B₁) = no (λ ())
  (A `⊎ A₁) `⌣ (B `× B₁) = no (λ ())
  (A `⊎ A₁) `⌣ (B `⊎ B₁) = yes sum⌣
  
  data Ground : Type → Set where
    G-Base : ∀{ι} → Ground (` ι)
    G-Fun : Ground (⋆ ⇒ ⋆)
    G-Pair : Ground (⋆ `× ⋆)
    G-Sum : Ground (⋆ `⊎ ⋆)

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

{-
  consis-eq : ∀{A B} (c : A ~ B)→ (d : A ~ B) → c ≡ d
  consis-eq {⋆} {⋆} unk~L unk~L = {!!}
  consis-eq {⋆} {⋆} unk~L unk~R = {!!}
  consis-eq {⋆} {⋆} unk~R d = {!!}
  consis-eq {⋆} {` x} c d = {!!}
  consis-eq {⋆} {B ⇒ B₁} c d = {!!}
  consis-eq {⋆} {B `× B₁} c d = {!!}
  consis-eq {⋆} {B `⊎ B₁} c d = {!!}
  consis-eq {` x} {B} c d = {!!}
  consis-eq {A ⇒ A₁} {B} c d = {!!}
  consis-eq {A `× A₁} {B} c d = {!!}
  consis-eq {A `⊎ A₁} {B} c d = {!!}
-}

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
