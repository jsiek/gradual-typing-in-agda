module Types2 where

  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  open import Data.Integer using (ℤ)
  open import Data.Bool
  open import Data.List
  open import Data.Unit renaming (⊤ to Top)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)

  infix  7 _⇒_
  infixl  7 _∘_
  infix  9 _`×_
  infix  8 _`⊎_
  infix 10 `_

  data Base : Set where
    Nat : Base
    Int : Base
    𝔹 : Base
    Unit : Base
    ⊥ : Base

  data Kind : Set where
    typ : Kind
    ⇢_ : Kind → Kind

  data TyCon : Kind → Set where
    Fun : TyCon (⇢ ⇢ typ)
    Pair : TyCon (⇢ ⇢ typ)
    Sum : TyCon (⇢ ⇢ typ)
    Ref : TyCon (⇢ typ)

  data Typ : Kind → Set where
    ⋆ : Typ typ
    `_ : Base → Typ typ
    con : ∀{κ} → TyCon κ → Typ κ
    _∘_ : ∀{κ'} → Typ (⇢ κ') → Typ typ → Typ κ'

  _⇒_ : Typ typ → Typ typ → Typ typ
  A ⇒ B = ((con Fun) ∘ A) ∘ B

  _`×_ : Typ typ → Typ typ → Typ typ
  A `× B = ((con Pair) ∘ A) ∘ B

  _`⊎_ : Typ typ → Typ typ → Typ typ
  A `⊎ B = ((con Sum) ∘ A) ∘ B

  Type = Typ typ

  data Atomic : Type → Set where
    A-Unk : Atomic ⋆
    A-Base : ∀{ι} → Atomic (` ι)

  base? : (A : Type) → Dec (Σ[ ι ∈ Base ] A ≡ ` ι)
  base? ⋆ = no G
    where G : ¬ Σ-syntax Base (λ ι → ⋆ ≡ ` ι)
          G ⟨ _ , () ⟩
  base? (` ι) = yes ⟨ ι , refl ⟩
  base? (con F) =  no G
    where G : ¬ Σ-syntax Base (λ ι → con F ≡ ` ι)
          G ⟨ _ , () ⟩
  base? (F ∘ A) =  no G
    where G : ¬ Σ-syntax Base (λ ι → (F ∘ A) ≡ ` ι)
          G ⟨ fst , () ⟩

  rep-base : Base → Set
  rep-base Nat = ℕ
  rep-base Int = ℤ
  rep-base 𝔹 = Bool
  rep-base Unit = Top
  rep-base ⊥ = Bot

  rep-kind : Kind → Set₁
  rep-kind typ = Set
  rep-kind (⇢ κ') = Set → rep-kind κ'

  rep-tycon : ∀{κ} → TyCon κ → rep-kind κ 
  rep-tycon Fun = λ a → λ b → (a → b)
  rep-tycon Pair = λ a → λ b → Bot
  rep-tycon Sum = λ a → λ b → Bot
  rep-tycon Ref = λ a → Bot
  
  rep : ∀{κ} → Typ κ → rep-kind κ
  rep ⋆ = Bot
  rep (` ι) = rep-base ι
  rep (con F) = rep-tycon F
  rep (F ∘ A) = (rep F) (rep A)
  
  data Prim : Type → Set where
    P-Base : ∀{ι} → Prim (` ι)
    P-Fun : ∀ {ι B}
      → Prim B
        ------------------
      → Prim ((` ι) ⇒ B)

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
  prim? (con x) = no λ ()
  prim? (con x ∘ A₁) = no λ ()
  prim? ((con Fun ∘ ⋆) ∘ A₁) = no (λ ())
  prim? ((con Fun ∘ (` x)) ∘ A₁) with prim? A₁
  ... | yes pb = yes (P-Fun pb)
  ... | no pb = no G
        where G : ¬ Prim ((con Fun ∘ (` x)) ∘ A₁)
              G (P-Fun p) = ⊥-elim (pb p)
  prim? ((con Fun ∘ con x) ∘ A₁) = no (λ ())
  prim? ((con Fun ∘ (A₂ ∘ A₃)) ∘ A₁) = no (λ ())
  prim? ((con Pair ∘ A₂) ∘ A₁) = no (λ ())
  prim? ((con Sum ∘ A₂) ∘ A₁) = no (λ ())
  prim? (((A ∘ A₃) ∘ A₂) ∘ A₁) = no (λ ())

  ¬P-Fun : ∀{A B C} → ¬ Prim ((A ⇒ B) ⇒ C)
  ¬P-Fun ()

  ¬P-Pair : ∀{A B C} → ¬ Prim ((A `× B) ⇒ C)
  ¬P-Pair ()

  ¬P-Sum : ∀{A B C} → ¬ Prim ((A `⊎ B) ⇒ C)
  ¬P-Sum ()

  ¬P-Unk : ∀{C} → ¬ Prim (⋆ ⇒ C)
  ¬P-Unk ()
  

  infix 6 _⊑_

  data _⊑_ : ∀{κ} → Typ κ → Typ κ → Set where
    unk⊑ : ∀{A} → ⋆ ⊑ A

    base⊑ : ∀{ι} → ` ι ⊑ ` ι

    con⊑ : ∀ {κ}{F : TyCon κ}
        -------------
      → con F ⊑ con F
      
    app⊑ : ∀ {κ}{F F' : Typ (⇢ κ)}{A A' : Type}
      → F ⊑ F' → A ⊑ A'
        ---------------
      → F ∘ A ⊑ F' ∘ A'

  Refl⊑ : ∀{κ}{A : Typ κ} → A ⊑ A
  Refl⊑ {κ}{⋆} = unk⊑
  Refl⊑ {κ}{` ι} = base⊑
  Refl⊑ {κ}{con F } = con⊑
  Refl⊑ {κ}{F ∘ A} = app⊑ Refl⊑ Refl⊑

  Trans⊑ : ∀ {κ}{A B C : Typ κ} → A ⊑ B → B ⊑ C → A ⊑ C
  Trans⊑ {.typ} unk⊑ bc = unk⊑
  Trans⊑ {.typ} base⊑ bc = bc
  Trans⊑ {κ} con⊑ bc = bc
  Trans⊑ {κ} (app⊑ ab ab₁) (app⊑ bc bc₁) = app⊑ (Trans⊑ ab bc) (Trans⊑ ab₁ bc₁)

  AntiSym⊑ : ∀ {κ}{A B : Typ κ} → A ⊑ B → B ⊑ A → A ≡ B
  AntiSym⊑ unk⊑ unk⊑ = refl
  AntiSym⊑ base⊑ ba = refl
  AntiSym⊑ con⊑ ba = refl
  AntiSym⊑ (app⊑ ab ab₁) (app⊑ ba ba₁) =
    cong₂ _∘_ (AntiSym⊑ ab ba) (AntiSym⊑ ab₁ ba₁)

  data _`⊑_ : List Type → List Type → Set where
    le-nil : [] `⊑ []
    le-cons : ∀{A As B Bs}
            → A ⊑ B  → As `⊑ Bs
            → (A ∷ As) `⊑ (B ∷ Bs)

  kind-app : (ls : List Type) → Kind
  kind-app [] = typ
  kind-app (A ∷ ls) = ⇢ (kind-app ls)

  apps : (l : List Type) → Typ (kind-app l) → Type
  apps [] F = F
  apps (A ∷ As) F = apps As (F ∘ A)

  ⊑L⋆ : ∀{A} → A ⊑ ⋆ → A ≡ ⋆
  ⊑L⋆ {⋆} unk⊑ = refl

  ⊑RBase : ∀{C ι} → ` ι ⊑ C → C ≡ ` ι
  ⊑RBase {ι} base⊑ = refl

  ⊑LBase : ∀{A ι} → A ⊑ ` ι →  A ≡ (` ι) ⊎ A ≡ ⋆
  ⊑LBase {⋆} {ι} unk⊑ = inj₂ refl
  ⊑LBase {` ι} {ι} base⊑ = inj₁ refl

{-
  data LikeList : ∀{A B} → List A → List B → Set where
    nil-ll : LikeList [] []
    cons-ll : ∀{A B As Bs} → LikeList As Bs → LikeList (A ∷ As) (B ∷ Bs)

  ⊑Lcon : ∀{Bs : List Type}{A : Type}{F : TyCon (kind-app Bs)} 
        → A ⊑ (apps Bs (con F))
        → (A ≡ ⋆) ⊎ Σ[ As ∈ LikeList Bs As ]
                     (A ≡ (apps As (con F))) × (As `⊑ Bs)
  ⊑Lcon {A}{Bs} ls = ?
-}

{-

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
  consis base⊑ unk⊑ = unk~R
  consis base⊑ base⊑ = base~
  consis (fun⊑ ac ac₁) unk⊑ = unk~R
  consis (fun⊑ ac ac₁) (fun⊑ bc bc₁) = fun~ (consis ac bc) (consis ac₁ bc₁)
  consis (pair⊑ ac ac₁) unk⊑ = unk~R
  consis (pair⊑ ac ac₁) (pair⊑ bc bc₁) = pair~ (consis ac bc) (consis ac₁ bc₁)
  consis (sum⊑ ac ac₁) unk⊑ = unk~R
  consis (sum⊑ ac ac₁) (sum⊑ bc bc₁) = sum~ (consis ac bc) (consis ac₁ bc₁)

  consis-ub : ∀{A B} → A ~ B → Σ[ C ∈ Type ] A ⊑ C × B ⊑ C
  consis-ub{B = B} unk~L = ⟨ B , ⟨ unk⊑ , Refl⊑ ⟩ ⟩
  consis-ub{A = A} unk~R = ⟨ A , ⟨ Refl⊑ , unk⊑ ⟩ ⟩
  consis-ub (base~ {ι = ι}) = ⟨ ` ι , ⟨ base⊑ , base⊑ ⟩ ⟩
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
  Sym~ base~ = base~
  Sym~ (fun~ c c₁) = fun~ (Sym~ c) (Sym~ c₁)
  Sym~ (pair~ c c₁) = pair~ (Sym~ c) (Sym~ c₁)
  Sym~ (sum~ c c₁) = sum~ (Sym~ c) (Sym~ c₁)

  ub : (C : Type) → (A : Type) → (B : Type) → Set
  ub C A B = (A ⊑ C) × (B ⊑ C)

  lub : (C : Type) → (A : Type) → (B : Type) → Set
  lub C A B = (ub C A B) × (∀{C'} → ub C' A B → C ⊑ C')

  infix 6 _`⊔_
  _`⊔_ : (A : Type) → (B : Type) → ∀ { c : A ~ B } → Σ[ C ∈ Type ] (lub C A B)
  (.⋆ `⊔ B) {unk~L} = ⟨ B , ⟨ ⟨ unk⊑ , Refl⊑ ⟩ , (λ x → proj₂ x) ⟩ ⟩
  (A `⊔ .⋆) {unk~R} = ⟨ A , ⟨ ⟨ Refl⊑ , unk⊑ ⟩ , (λ {C'} → proj₁) ⟩ ⟩
  (` ι `⊔ ` ι) {base~} = ⟨ ` ι , ⟨ ⟨ base⊑ , base⊑ ⟩ , (λ {x} → proj₁) ⟩ ⟩
  ((A ⇒ B) `⊔ (A' ⇒ B')) {fun~ c c₁} with (A `⊔ A') {c} | (B `⊔ B') {c₁}
  ... | ⟨ C , lub1 ⟩ | ⟨ D , lub2 ⟩ =
    let x = fun⊑ (proj₁ (proj₁ lub1)) (proj₁ (proj₁ lub2)) in
    let y = fun⊑ (proj₂ (proj₁ lub1)) (proj₂ (proj₁ lub2))in 
    ⟨ (C ⇒ D) , ⟨ ⟨ x , y ⟩ , G ⟩ ⟩
    where
    G : {C' : Type} →
        Σ (A ⇒ B ⊑ C') (λ x₁ → A' ⇒ B' ⊑ C') → C ⇒ D ⊑ C'
    G {.(_ ⇒ _)} ⟨ fun⊑ a-b-cp a-b-cp₁ , fun⊑ ap-bp-cp ap-bp-cp₁ ⟩ =
      fun⊑ (proj₂ lub1 ⟨ a-b-cp , ap-bp-cp ⟩)
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

  ⊑Base→~Base : ∀{A ι} → A ⊑ ` ι → A ~ ` ι
  ⊑Base→~Base unk⊑ = unk~L
  ⊑Base→~Base base⊑ = base~

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
  ... | yes ab | yes a1b1 = yes (fun~ ab a1b1)
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

  eq-unk : (A : Type) → Dec (A ≡ ⋆)
  eq-unk ⋆ = yes refl
  eq-unk (` ι) = no (λ ())
  eq-unk (A ⇒ A₁) = no (λ ())
  eq-unk (A `× A₁) = no (λ ())
  eq-unk (A `⊎ A₁) = no (λ ())

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

  ground : (A : Type) → {nd : A ≢ ⋆} → Σ[ B ∈ Type ] Ground B × (A ~ B)
  ground ⋆ {nd} = ⊥-elim (nd refl)
  ground (` ι) {nd} = ⟨ ` ι , ⟨ G-Base , base~ ⟩ ⟩
  ground (A ⇒ A₁) {nd} = ⟨ ⋆ ⇒ ⋆ , ⟨ G-Fun , fun~ unk~R unk~R ⟩ ⟩
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
-}
