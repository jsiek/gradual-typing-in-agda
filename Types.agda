module Types where

  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  open import Data.Bool
  open import Data.Unit
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)

  infix  7 _⇒_
  infix  9 _`×_
  infix  8 _`⊎_

  data Type : Set where
    ⋆ : Type
    Nat : Type
    𝔹 : Type
    _⇒_ : Type → Type → Type
    _`×_ : Type → Type → Type
    _`⊎_ : Type → Type → Type

  data Atomic : Type → Set where
    A-Unk : Atomic ⋆
    A-Nat : Atomic Nat
    A-Bool : Atomic 𝔹

  rep : Type → Set
  rep ⋆ = ⊥
  rep Nat = ℕ
  rep 𝔹 = Bool
  rep (t₁ ⇒ t₂) = (rep t₁) → (rep t₂)
  rep (t₁ `× t₂) = ⊥
  rep (t `⊎ t₁) = ⊥

  data Base : Type → Set where
    B-Nat : Base Nat
    B-Bool : Base 𝔹

  base : (A : Type) → (Base A) ⊎ ¬ (Base A)
  base ⋆ = inj₂ (λ ())
  base Nat = inj₁ B-Nat
  base 𝔹 = inj₁ B-Bool
  base (A ⇒ A₁) = inj₂ (λ ())
  base (A `× A₁) = inj₂ (λ ())
  base (A `⊎ A₁) = inj₂ (λ ())

  data Prim : Type → Set where
    P-Nat : Prim Nat
    P-Bool : Prim 𝔹
    P-Fun : ∀ {A B}
      → Base A
      → Prim B
        ------------------
      → Prim (A ⇒ B)

  prim : (A : Type) → (Prim A) ⊎ ¬ (Prim A)
  prim ⋆ = inj₂ λ ()
  prim Nat = inj₁ P-Nat
  prim 𝔹 = inj₁ P-Bool
  prim (A ⇒ A₁) with base A | prim A₁
  ... | inj₁ b | inj₁ p = inj₁ (P-Fun b p)
  ... | inj₁ b | inj₂ p = inj₂ G
        where
        G : Prim (A ⇒ A₁) → ⊥
        G (P-Fun x d) = p d
  ... | inj₂ b | _ = inj₂ G
        where
        G : Prim (A ⇒ A₁) → ⊥
        G (P-Fun x d) = b x
  prim (A `× A₁) = inj₂ (λ ())
  prim (A `⊎ A₁) = inj₂ (λ ())

  P-Fun1 : ∀ {A B}
    → Prim (A ⇒ B)
    → Base A
  P-Fun1 (P-Fun a b) = a

  P-Fun2 : ∀ {A B}
    → Prim (A ⇒ B)
    → Prim B
  P-Fun2 (P-Fun a b) = b

  ¬P-Fun : ∀{A B C} → ¬ Prim ((A ⇒ B) ⇒ C)
  ¬P-Fun (P-Fun () x₁)

  ¬P-Pair : ∀{A B C} → ¬ Prim ((A `× B) ⇒ C)
  ¬P-Pair (P-Fun () x₁)

  ¬P-Sum : ∀{A B C} → ¬ Prim ((A `⊎ B) ⇒ C)
  ¬P-Sum (P-Fun () x₁)

  ¬P-Unk : ∀{C} → ¬ Prim (⋆ ⇒ C)
  ¬P-Unk (P-Fun () x₁)


  infix 6 _⊑_

  data _⊑_ : Type → Type → Set where
    unk⊑ : ∀{A} → ⋆ ⊑ A

    nat⊑ : Nat ⊑ Nat

    bool⊑ : 𝔹 ⊑ 𝔹

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
  Refl⊑ {Nat} = nat⊑
  Refl⊑ {𝔹} = bool⊑
  Refl⊑ {A ⇒ A₁} = fun⊑ Refl⊑ Refl⊑
  Refl⊑ {A `× A₁} = pair⊑ Refl⊑ Refl⊑
  Refl⊑ {A `⊎ A₁} = sum⊑ Refl⊑ Refl⊑

  Trans⊑ : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
  Trans⊑ unk⊑ b = unk⊑
  Trans⊑ nat⊑ b = b
  Trans⊑ bool⊑ b = b
  Trans⊑ (fun⊑ a a₁) (fun⊑ b b₁) = fun⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)
  Trans⊑ (pair⊑ a a₁) (pair⊑ b b₁) = pair⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)
  Trans⊑ (sum⊑ a a₁) (sum⊑ b b₁) = sum⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)

  AntiSym⊑ : ∀ {A B} → A ⊑ B → B ⊑ A → A ≡ B
  AntiSym⊑ unk⊑ unk⊑ = refl
  AntiSym⊑ nat⊑ nat⊑ = refl
  AntiSym⊑ bool⊑ bool⊑ = refl
  AntiSym⊑ {A ⇒ B}{A' ⇒ B'} (fun⊑ a a₁) (fun⊑ b b₁) =
    cong₂ (_⇒_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)
  AntiSym⊑ (pair⊑ a a₁) (pair⊑ b b₁) =
    cong₂ (_`×_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)
  AntiSym⊑ (sum⊑ a a₁) (sum⊑ b b₁) =
    cong₂ (_`⊎_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)

  ⊑L⋆ : ∀{A} → A ⊑ ⋆ → A ≡ ⋆
  ⊑L⋆ {⋆} unk⊑ = refl

  ⊑R𝔹 : ∀{C} → 𝔹 ⊑ C → C ≡ 𝔹
  ⊑R𝔹 {𝔹} bool⊑ = refl

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

  ⊑RBase : ∀{A B} → Base A → A ⊑ B →  B ≡ A
  ⊑RBase {.Nat} {.Nat} B-Nat nat⊑ = refl
  ⊑RBase {.𝔹} {.𝔹} B-Bool bool⊑ = refl

  ⊑LBase : ∀{A B} → Base B → A ⊑ B →  A ≡ B ⊎ A ≡ ⋆
  ⊑LBase B-Nat unk⊑ = inj₂ refl
  ⊑LBase B-Nat nat⊑ = inj₁ refl
  ⊑LBase B-Bool unk⊑ = inj₂ refl
  ⊑LBase B-Bool bool⊑ = inj₁ refl

  data _~_ : Type → Type → Set where
    unk~L : ∀ {A} → ⋆ ~ A
    unk~R : ∀ {A} → A ~ ⋆
    nat~ : Nat ~ Nat
    bool~ : 𝔹 ~ 𝔹
    fun~ : ∀{A B A' B'}
      → A ~ A'  →  B ~ B'
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


  consis : ∀{C A B}
      → A ⊑ C → B ⊑ C
        -------------
      → A ~ B
  consis unk⊑ bc = unk~L
  consis nat⊑ unk⊑ = unk~R
  consis nat⊑ nat⊑ = nat~
  consis bool⊑ unk⊑ = unk~R
  consis bool⊑ bool⊑ = bool~
  consis (fun⊑ ac ac₁) unk⊑ = unk~R
  consis (fun⊑ ac ac₁) (fun⊑ bc bc₁) = fun~ (consis ac bc) (consis ac₁ bc₁)
  consis (pair⊑ ac ac₁) unk⊑ = unk~R
  consis (pair⊑ ac ac₁) (pair⊑ bc bc₁) = pair~ (consis ac bc) (consis ac₁ bc₁)
  consis (sum⊑ ac ac₁) unk⊑ = unk~R
  consis (sum⊑ ac ac₁) (sum⊑ bc bc₁) = sum~ (consis ac bc) (consis ac₁ bc₁)

  consis-ub : ∀{A B} → A ~ B → Σ[ C ∈ Type ] A ⊑ C × B ⊑ C
  consis-ub{B = B} unk~L = ⟨ B , ⟨ unk⊑ , Refl⊑ ⟩ ⟩
  consis-ub{A = A} unk~R = ⟨ A , ⟨ Refl⊑ , unk⊑ ⟩ ⟩
  consis-ub nat~ = ⟨ Nat , ⟨ nat⊑ , nat⊑ ⟩ ⟩
  consis-ub bool~ = ⟨ 𝔹 , ⟨ bool⊑ , bool⊑ ⟩ ⟩
  consis-ub (fun~ ab₁ ab₂)
      with consis-ub ab₁ | consis-ub ab₂
  ... | ⟨ C₁ , ⟨ ac1 , bc1 ⟩ ⟩ | ⟨ C₂ , ⟨ ac2 , bc2 ⟩ ⟩ =
        ⟨ C₁ ⇒ C₂ , ⟨ (fun⊑ ac1 ac2) , fun⊑ bc1 bc2 ⟩ ⟩
  consis-ub (pair~ ab₁ ab₂)
      with consis-ub ab₁ | consis-ub ab₂
  ... | ⟨ C₁ , ⟨ ac1 , bc1 ⟩ ⟩ | ⟨ C₂ , ⟨ ac2 , bc2 ⟩ ⟩ =
        ⟨ C₁ `× C₂ , ⟨ (pair⊑ ac1 ac2) , pair⊑ bc1 bc2 ⟩ ⟩
  consis-ub (sum~ ab₁ ab₂)
      with consis-ub ab₁ | consis-ub ab₂
  ... | ⟨ C₁ , ⟨ ac1 , bc1 ⟩ ⟩ | ⟨ C₂ , ⟨ ac2 , bc2 ⟩ ⟩ =
        ⟨ C₁ `⊎ C₂ , ⟨ (sum⊑ ac1 ac2) , sum⊑ bc1 bc2 ⟩ ⟩

  Refl~ : ∀ {A} → A ~ A
  Refl~ {A} = consis Refl⊑ Refl⊑

  Sym~ : ∀ {A B} → A ~ B → B ~ A
  Sym~ unk~L = unk~R
  Sym~ unk~R = unk~L
  Sym~ nat~ = nat~
  Sym~ bool~ = bool~
  Sym~ (fun~ c c₁) = fun~ (Sym~ c) (Sym~ c₁)
  Sym~ (pair~ c c₁) = pair~ (Sym~ c) (Sym~ c₁)
  Sym~ (sum~ c c₁) = sum~ (Sym~ c) (Sym~ c₁)

  ub : (C : Type) → (A : Type) → (B : Type) → Set
  ub C A B = (A ⊑ C) × (B ⊑ C)

  lub : (C : Type) → (A : Type) → (B : Type) → Set
  lub C A B = (ub C A B) × (∀{C'} → ub C' A B → C ⊑ C')


  _`⊔_ : (A : Type) → (B : Type) → ∀ { c : A ~ B } → Σ[ C ∈ Type ] (lub C A B)
  (.⋆ `⊔ B) {unk~L} = ⟨ B , ⟨ ⟨ unk⊑ , Refl⊑ ⟩ , (λ x → proj₂ x) ⟩ ⟩
  (A `⊔ .⋆) {unk~R} = ⟨ A , ⟨ ⟨ Refl⊑ , unk⊑ ⟩ , (λ {C'} → proj₁) ⟩ ⟩
  (.Nat `⊔ .Nat) {nat~} = ⟨ Nat , ⟨ ⟨ nat⊑ , nat⊑ ⟩ , (λ {x} → proj₁) ⟩ ⟩
  (.𝔹 `⊔ .𝔹) {bool~} = ⟨ 𝔹 , ⟨ ⟨ bool⊑ , bool⊑ ⟩ , (λ {x} → proj₁) ⟩ ⟩
  ((A ⇒ B) `⊔ (A' ⇒ B')) {fun~ c c₁} with (A `⊔ A') {c} | (B `⊔ B') {c₁}
  ... | ⟨ C , lub1 ⟩ | ⟨ D , lub2 ⟩ =
    let x = fun⊑ (proj₁ (proj₁ lub1)) (proj₁ (proj₁ lub2)) in
    let y = fun⊑ (proj₂ (proj₁ lub1)) (proj₂ (proj₁ lub2))in 
    ⟨ (C ⇒ D) , ⟨ ⟨ x , y ⟩ , G ⟩ ⟩
    where
    G : {C' : Type} →
        Σ (A ⇒ B ⊑ C') (λ x₁ → A' ⇒ B' ⊑ C') → C ⇒ D ⊑ C'
    G {.(_ ⇒ _)} ⟨ fun⊑ a-b-cp a-b-cp₁ , fun⊑ ap-bp-cp ap-bp-cp₁ ⟩ =
      fun⊑ (proj₂ lub1 ⟨ a-b-cp , ap-bp-cp ⟩) (proj₂ lub2 ⟨ a-b-cp₁ , ap-bp-cp₁ ⟩)

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

  ⊔L : ∀ {A A'} {c : A ~ A'} → A ~ ((A ⊔ A') {c})
  ⊔L {A}{A'}{c} with (A `⊔ A') {c}
  ...    | ⟨ B , ⟨ q1 , q2 ⟩ ⟩ = consis {B} (proj₁ q1) (q2 q1)

  ⊔R : ∀ {A A'} {c : A ~ A'} → A' ~ ((A ⊔ A') {c})
  ⊔R {A}{A'}{c} with (A `⊔ A') {c}
  ...    | ⟨ B , ⟨ q1 , q2 ⟩ ⟩ = consis {B} (proj₂ q1) (q2 q1)

  ~⇒L : ∀{A B A' B'} → (A ⇒ B) ~ (A' ⇒ B') → A ~ A'
  ~⇒L (fun~ c c₁) = c

  ~⇒R : ∀{A B A' B'} → (A ⇒ B) ~ (A' ⇒ B') → B ~ B'
  ~⇒R (fun~ c c₁) = c₁

  ~×L : ∀{A B A' B'} → (A `× B) ~ (A' `× B') → A ~ A'
  ~×L (pair~ c c₁) = c

  ~×R : ∀{A B A' B'} → (A `× B) ~ (A' `× B') → B ~ B'
  ~×R (pair~ c c₁) = c₁

  ~⊎L : ∀{A B A' B'} → (A `⊎ B) ~ (A' `⊎ B') → A ~ A'
  ~⊎L (sum~ c c₁) = c

  ~⊎R : ∀{A B A' B'} → (A `⊎ B) ~ (A' `⊎ B') → B ~ B'
  ~⊎R (sum~ c c₁) = c₁

  ¬~nb : ¬ (Nat ~ 𝔹)
  ¬~nb ()

  ¬~nf : ∀{A B} → ¬ (Nat ~ (A ⇒ B))
  ¬~nf ()

  ¬~np : ∀{A B} → ¬ (Nat ~ (A `× B))
  ¬~np ()

  ¬~ns : ∀{A B} → ¬ (Nat ~ (A `⊎ B))
  ¬~ns ()

  ¬~bn : ¬ (𝔹 ~ Nat)
  ¬~bn ()

  ¬~bf : ∀{A B} → ¬ (𝔹 ~ (A ⇒ B))
  ¬~bf ()

  ¬~bp : ∀{A B} → ¬ (𝔹 ~ (A `× B))
  ¬~bp ()


  ¬~bs : ∀{A B} → ¬ (𝔹 ~ (A `⊎ B))
  ¬~bs ()

  ¬~fn : ∀{A B} → ¬ ((A ⇒ B) ~ Nat)
  ¬~fn ()

  ¬~fb : ∀{A B} → ¬ ((A ⇒ B) ~ 𝔹)
  ¬~fb ()

  ¬~fp : ∀{A B A' B'} → ¬ ((A ⇒ B) ~ (A' `× B'))
  ¬~fp ()

  ¬~fs : ∀{A B A' B'} → ¬ ((A ⇒ B) ~ (A' `⊎ B'))
  ¬~fs ()

  ¬~pn : ∀{A B} → ¬ ((A `× B) ~ Nat)
  ¬~pn ()

  ¬~pb : ∀{A B} → ¬ ((A `× B) ~ 𝔹)
  ¬~pb ()

  ¬~pf : ∀{A B A' B'} → ¬ ((A `× B) ~ (A' ⇒ B'))
  ¬~pf ()

  ¬~ps : ∀{A B A' B'} → ¬ ((A `× B) ~ (A' `⊎ B'))
  ¬~ps ()

  ¬~sn : ∀{A B} → ¬ ((A `⊎ B) ~ Nat)
  ¬~sn ()

  ¬~sb : ∀{A B} → ¬ ((A `⊎ B) ~ 𝔹)
  ¬~sb ()

  ¬~sf : ∀{A B A' B'} → ¬ ((A `⊎ B) ~ (A' ⇒ B'))
  ¬~sf ()

  ¬~sp : ∀{A B A' B'} → ¬ ((A `⊎ B) ~ (A' `× B'))
  ¬~sp ()

  ¬~fL : ∀ {A B A' B'}
    → ¬ (A ~ B)
      ------------------------
    →  ¬ ((A ⇒ A') ~ (B ⇒ B'))
  ¬~fL {A} {B} {A'} {B'} d1 (fun~ c c₁) = d1 c

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

  ⊑𝔹→~𝔹 : ∀{A} → A ⊑ 𝔹 → A ~ 𝔹
  ⊑𝔹→~𝔹 unk⊑ = unk~L
  ⊑𝔹→~𝔹 bool⊑ = bool~

  _`~_ : (A : Type) → (B : Type) → (A ~ B) ⊎ (¬ (A ~ B))
  ⋆ `~ B = inj₁ unk~L
  Nat `~ ⋆ = inj₁ unk~R
  Nat `~ Nat = inj₁ nat~
  Nat `~ 𝔹 = inj₂ (λ ())
  Nat `~ (B ⇒ B₁) = inj₂ (λ ())
  Nat `~ (B `× B₁) = inj₂ (λ ())
  Nat `~ (B `⊎ B₁) = inj₂ (λ ())
  𝔹 `~ ⋆ = inj₁ unk~R
  𝔹 `~ Nat = inj₂ (λ ())
  𝔹 `~ 𝔹 = inj₁ bool~
  𝔹 `~ (B ⇒ B₁) = inj₂ (λ ())
  𝔹 `~ (B `× B₁) = inj₂ (λ ())
  𝔹 `~ (B `⊎ B₁) = inj₂ (λ ())
  (A ⇒ A₁) `~ ⋆ = inj₁ unk~R
  (A ⇒ A₁) `~ Nat = inj₂ (λ ())
  (A ⇒ A₁) `~ 𝔹 = inj₂ (λ ())
  (A ⇒ A₁) `~ (B ⇒ B₁) with A `~ B | A₁ `~ B₁
  ... | inj₁ c | inj₁ d = inj₁ (fun~ c d)
  ... | inj₁ c | inj₂ d = inj₂ ((¬~fR d))
  ... | inj₂ c | _ = inj₂ ((¬~fL c))
  (A ⇒ A₁) `~ (B `× B₁) = inj₂ (λ ())
  (A ⇒ A₁) `~ (B `⊎ B₁) = inj₂ (λ ())
  (A `× A₁) `~ ⋆ = inj₁ unk~R
  (A `× A₁) `~ Nat = inj₂ (λ ())
  (A `× A₁) `~ 𝔹 = inj₂ (λ ())
  (A `× A₁) `~ (B ⇒ B₁) = inj₂ (λ ())
  (A `× A₁) `~ (B `× B₁) with A `~ B | A₁ `~ B₁
  ... | inj₁ c | inj₁ d = inj₁ (pair~ c d)
  ... | inj₁ c | inj₂ d = inj₂ (¬~pR d)
  ... | inj₂ c | _ = inj₂ (¬~pL c)
  (A `× A₁) `~ (B `⊎ B₁) = inj₂ (λ ())
  (A `⊎ A₁) `~ ⋆ = inj₁ unk~R
  (A `⊎ A₁) `~ Nat = inj₂ (λ ())
  (A `⊎ A₁) `~ 𝔹 = inj₂ (λ ())
  (A `⊎ A₁) `~ (B ⇒ B₁) = inj₂ (λ ())
  (A `⊎ A₁) `~ (B `× B₁) = inj₂ (λ ())
  (A `⊎ A₁) `~ (B `⊎ B₁) with A `~ B | A₁ `~ B₁
  ... | inj₁ c | inj₁ d = inj₁ (sum~ c d)
  ... | inj₁ c | inj₂ d = inj₂ (¬~sR d)
  ... | inj₂ c | _ = inj₂ (¬~sL c)

  eq-unk : (A : Type) → (A ≡ ⋆) ⊎ (A ≢ ⋆)
  eq-unk ⋆ = inj₁ refl
  eq-unk Nat = inj₂ (λ ())
  eq-unk 𝔹 = inj₂ (λ ())
  eq-unk (A ⇒ A₁) = inj₂ (λ ())
  eq-unk (A `× A₁) = inj₂ (λ ())
  eq-unk (A `⊎ A₁) = inj₂ (λ ())

  {- Shallow Consistency, used in Lazy Casts -}

  data _⌣_ : Type → Type → Set where
    unk⌣L : ∀ {A} → ⋆ ⌣ A
    unk⌣R : ∀ {A} → A ⌣ ⋆
    nat⌣ : Nat ⌣ Nat
    bool⌣ : 𝔹 ⌣ 𝔹
    fun⌣ : ∀{A B A' B'}
        -------------------
      → (A ⇒ B) ⌣ (A' ⇒ B')
    pair⌣ : ∀{A B A' B'}
        -------------------
      → (A `× B) ⌣ (A' `× B')
    sum⌣ : ∀{A B A' B'}
        -------------------
      → (A `⊎ B) ⌣ (A' `⊎ B')
    
  _`⌣_ : (A : Type) → (B : Type) → (A ⌣ B) ⊎ (¬ (A ⌣ B))
  ⋆ `⌣ B = inj₁ unk⌣L
  Nat `⌣ ⋆ = inj₁ unk⌣R
  Nat `⌣ Nat = inj₁ nat⌣
  Nat `⌣ 𝔹 = inj₂ (λ ())
  Nat `⌣ (B ⇒ B₁) = inj₂ (λ ())
  Nat `⌣ (B `× B₁) = inj₂ (λ ())
  Nat `⌣ (B `⊎ B₁) = inj₂ (λ ())
  𝔹 `⌣ ⋆ = inj₁ unk⌣R
  𝔹 `⌣ Nat = inj₂ (λ ())
  𝔹 `⌣ 𝔹 = inj₁ bool⌣
  𝔹 `⌣ (B ⇒ B₁) = inj₂ (λ ())
  𝔹 `⌣ (B `× B₁) = inj₂ (λ ())
  𝔹 `⌣ (B `⊎ B₁) = inj₂ (λ ())
  (A ⇒ A₁) `⌣ ⋆ = inj₁ unk⌣R
  (A ⇒ A₁) `⌣ Nat = inj₂ (λ ())
  (A ⇒ A₁) `⌣ 𝔹 = inj₂ (λ ())
  (A ⇒ A₁) `⌣ (B ⇒ B₁) = inj₁ fun⌣
  (A ⇒ A₁) `⌣ (B `× B₁) = inj₂ (λ ())
  (A ⇒ A₁) `⌣ (B `⊎ B₁) = inj₂ (λ ())
  (A `× A₁) `⌣ ⋆ = inj₁ unk⌣R
  (A `× A₁) `⌣ Nat = inj₂ (λ ())
  (A `× A₁) `⌣ 𝔹 = inj₂ (λ ())
  (A `× A₁) `⌣ (B ⇒ B₁) = inj₂ (λ ())
  (A `× A₁) `⌣ (B `× B₁) = inj₁ pair⌣
  (A `× A₁) `⌣ (B `⊎ B₁) = inj₂ (λ ())
  (A `⊎ A₁) `⌣ ⋆ = inj₁ unk⌣R
  (A `⊎ A₁) `⌣ Nat = inj₂ (λ ())
  (A `⊎ A₁) `⌣ 𝔹 = inj₂ (λ ())
  (A `⊎ A₁) `⌣ (B ⇒ B₁) = inj₂ (λ ())
  (A `⊎ A₁) `⌣ (B `× B₁) = inj₂ (λ ())
  (A `⊎ A₁) `⌣ (B `⊎ B₁) = inj₁ sum⌣

  data Ground : Type → Set where
    G-Base : ∀{A} → Base A → Ground A
    G-Fun : Ground (⋆ ⇒ ⋆)
    G-Pair : Ground (⋆ `× ⋆)
    G-Sum : Ground (⋆ `⊎ ⋆)

  not-ground⋆ : ¬ Ground ⋆
  not-ground⋆ (G-Base ())

  ground⇒1 : ∀{A}{B} → Ground (A ⇒ B) → A ≢ ⋆ → ⊥
  ground⇒1 (G-Base ()) nd
  ground⇒1 G-Fun nd = nd refl

  ground⇒2 : ∀{A}{B} → Ground (A ⇒ B) → B ≢ ⋆ → ⊥
  ground⇒2 (G-Base ()) nd
  ground⇒2 G-Fun nd = nd refl

  ground×1 : ∀{A}{B} → Ground (A `× B) → A ≢ ⋆ → ⊥
  ground×1 (G-Base ()) nd
  ground×1 G-Pair nd = nd refl

  ground×2 : ∀{A}{B} → Ground (A `× B) → B ≢ ⋆ → ⊥
  ground×2 (G-Base ()) nd
  ground×2 G-Pair nd = nd refl

  ground⊎1 : ∀{A}{B} → Ground (A `⊎ B) → A ≢ ⋆ → ⊥
  ground⊎1 (G-Base ()) nd
  ground⊎1 G-Sum nd = nd refl

  ground⊎2 : ∀{A}{B} → Ground (A `⊎ B) → B ≢ ⋆ → ⊥
  ground⊎2 (G-Base ()) nd
  ground⊎2 G-Sum nd = nd refl

  ground : (A : Type) → {nd : A ≢ ⋆} → Σ[ B ∈ Type ] Ground B × (A ~ B)
  ground ⋆ {nd} = ⊥-elim (nd refl)
  ground Nat {nd} = ⟨ Nat , ⟨ G-Base B-Nat , nat~ ⟩ ⟩
  ground 𝔹 {nd} = ⟨ 𝔹 , ⟨ G-Base B-Bool , bool~ ⟩ ⟩
  ground (A ⇒ A₁) {nd} = ⟨ ⋆ ⇒ ⋆ , ⟨ G-Fun , fun~ unk~R unk~R ⟩ ⟩
  ground (A `× A₁) {nd} = ⟨ ⋆ `× ⋆ , ⟨ G-Pair , pair~ unk~R unk~R ⟩ ⟩
  ground (A `⊎ A₁) {nd} = ⟨ ⋆ `⊎ ⋆ , ⟨ G-Sum , sum~ unk~R unk~R ⟩ ⟩

  ground? : (A : Type) → Ground A ⊎ (¬ Ground A)
  ground? ⋆ = inj₂ λ x → contradiction x not-ground⋆
  ground? Nat = inj₁ (G-Base B-Nat)
  ground? 𝔹 = inj₁ (G-Base B-Bool)
  ground? (A₁ `× A₂) with eq-unk A₁ | eq-unk A₂
  ... | inj₁ eq1 | inj₁ eq2 rewrite eq1 | eq2 = inj₁ G-Pair
  ... | inj₁ eq1 | inj₂ eq2 rewrite eq1 = inj₂ λ x → ground×2 x eq2
  ... | inj₂ eq1 | _ = inj₂ λ x → ground×1 x eq1
  ground? (A₁ `⊎ A₂) with eq-unk A₁ | eq-unk A₂
  ... | inj₁ eq1 | inj₁ eq2 rewrite eq1 | eq2 = inj₁ G-Sum
  ... | inj₁ eq1 | inj₂ eq2 rewrite eq1 = inj₂ λ x → ground⊎2 x eq2
  ... | inj₂ eq1 | _ = inj₂ λ x → ground⊎1 x eq1
  ground? (A₁ ⇒ A₂) with eq-unk A₁ | eq-unk A₂
  ... | inj₁ eq1 | inj₁ eq2 rewrite eq1 | eq2 = inj₁ G-Fun
  ... | inj₁ eq1 | inj₂ eq2 rewrite eq1 = inj₂ λ x → ground⇒2 x eq2
  ... | inj₂ eq1 | _ = inj₂ λ x → ground⇒1 x eq1

  base-eq? : (A : Type) → (B : Type) → {a : Base A} → {b : Base B}
          → A ≡ B ⊎ A ≢ B
  base-eq? .Nat .Nat {B-Nat} {B-Nat} = inj₁ refl
  base-eq? .Nat .𝔹 {B-Nat} {B-Bool} = inj₂ (λ ())
  base-eq? .𝔹 .Nat {B-Bool} {B-Nat} = inj₂ (λ ())
  base-eq? .𝔹 .𝔹 {B-Bool} {B-Bool} = inj₁ refl
  
  gnd-eq? : (A : Type) → (B : Type) → {a : Ground A} → {b : Ground B}
          → A ≡ B ⊎ A ≢ B
  gnd-eq? A B {G-Base x} {G-Base x₁} = base-eq? A B {x} {x₁}
  gnd-eq? .Nat .(⋆ ⇒ ⋆) {G-Base B-Nat} {G-Fun} = inj₂ λ ()
  gnd-eq? .𝔹 .(⋆ ⇒ ⋆) {G-Base B-Bool} {G-Fun} = inj₂ λ ()
  gnd-eq? .Nat .(⋆ `× ⋆) {G-Base B-Nat} {G-Pair} = inj₂ (λ ())
  gnd-eq? .𝔹 .(⋆ `× ⋆) {G-Base B-Bool} {G-Pair} = inj₂ (λ ())
  gnd-eq? .Nat .(⋆ `⊎ ⋆) {G-Base B-Nat} {G-Sum} = inj₂ (λ ())
  gnd-eq? .𝔹 .(⋆ `⊎ ⋆) {G-Base B-Bool} {G-Sum} = inj₂ (λ ())
  gnd-eq? .(⋆ ⇒ ⋆) .Nat {G-Fun} {G-Base B-Nat} = inj₂ λ ()
  gnd-eq? .(⋆ ⇒ ⋆) .𝔹 {G-Fun} {G-Base B-Bool} = inj₂ λ ()
  gnd-eq? .(⋆ ⇒ ⋆) .(⋆ ⇒ ⋆) {G-Fun} {G-Fun} = inj₁ refl
  gnd-eq? .(⋆ ⇒ ⋆) .(⋆ `× ⋆) {G-Fun} {G-Pair} = inj₂ (λ ())
  gnd-eq? .(⋆ ⇒ ⋆) .(⋆ `⊎ ⋆) {G-Fun} {G-Sum} = inj₂ (λ ())
  gnd-eq? .(⋆ `× ⋆) .Nat {G-Pair} {G-Base B-Nat} = inj₂ (λ ())
  gnd-eq? .(⋆ `× ⋆) .𝔹 {G-Pair} {G-Base B-Bool} = inj₂ (λ ())
  gnd-eq? .(⋆ `× ⋆) .(⋆ ⇒ ⋆) {G-Pair} {G-Fun} = inj₂ (λ ())
  gnd-eq? .(⋆ `× ⋆) .(⋆ `× ⋆) {G-Pair} {G-Pair} = inj₁ refl
  gnd-eq? .(⋆ `× ⋆) .(⋆ `⊎ ⋆) {G-Pair} {G-Sum} = inj₂ (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) .Nat {G-Sum} {G-Base B-Nat} = inj₂ (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) .𝔹 {G-Sum} {G-Base B-Bool} = inj₂ (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) .(⋆ ⇒ ⋆) {G-Sum} {G-Fun} = inj₂ (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) .(⋆ `× ⋆) {G-Sum} {G-Pair} = inj₂ (λ ())
  gnd-eq? .(⋆ `⊎ ⋆) .(⋆ `⊎ ⋆) {G-Sum} {G-Sum} = inj₁ refl

