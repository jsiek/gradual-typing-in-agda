module AGT where

  open import Agda.Primitive renaming (_⊔_ to _⊍_)
  open import Types
  open import Labels
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; z≤n; s≤s) renaming (_⊔_ to _∨_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)

  data SType : Set where
    `_ : Base → SType
    _⇒_ : SType → SType → SType
    _`×_ : SType → SType → SType
    _`⊎_ : SType → SType → SType

  to-type : SType → Type
  to-type (` ι) = (` ι)
  to-type (S ⇒ T) = to-type S ⇒ to-type T
  to-type (S `× T) = to-type S `× to-type T
  to-type (S `⊎ T) = to-type S `⊎ to-type T

  data _⌢_ : SType → SType → Set where
    base⌢ : ∀{ι : Base} → (` ι) ⌢ (` ι)
    fun⌢ : ∀{A B A' B'}
        -------------------
      → (A ⇒ B) ⌢ (A' ⇒ B')
    pair⌢ : ∀{A B A' B'}
        -------------------
      → (A `× B) ⌢ (A' `× B')
    sum⌢ : ∀{A B A' B'}
        -------------------
      → (A `⊎ B) ⌢ (A' `⊎ B')
      
  {- Concretization -}

  data Conc : Type → SType → Set where
    c-base : ∀{ι} → Conc (` ι) (` ι)
    c-fun : ∀{T₁ T₂ : Type} {S₁ S₂ : SType}
       → Conc T₁ S₁  →  Conc T₂ S₂
         -------------------------
       → Conc (T₁ ⇒ T₂) (S₁ ⇒ S₂)
    c-pair : ∀{T₁ T₂ : Type} {S₁ S₂ : SType}
       → Conc T₁ S₁  →  Conc T₂ S₂
         -------------------------
       → Conc (T₁ `× T₂) (S₁ `× S₂)
    c-sum : ∀{T₁ T₂ : Type} {S₁ S₂ : SType}
       → Conc T₁ S₁  →  Conc T₂ S₂
         -------------------------
       → Conc (T₁ `⊎ T₂) (S₁ `⊎ S₂)
    c-unk : ∀{S} → Conc ⋆ S

  infix 6 _`⊑_
  data _`⊑_ : Type → Type → Set where
    prec : ∀{A B}
          → (∀{S} → Conc A S → Conc B S)
            ----------------------------
          → A `⊑ B

  conc : (A : Type) → Σ[ S ∈ SType ] Conc A S
  conc ⋆ = ⟨ ` 𝔹 , c-unk ⟩
  conc (` ι) = ⟨ ` ι , c-base ⟩
  conc (A ⇒ B) with conc A | conc B
  ... | ⟨ A' , ca ⟩ | ⟨ B' , cb ⟩ =
      ⟨ A' ⇒ B' , c-fun ca cb ⟩
  conc (A `× B) with conc A | conc B
  ... | ⟨ A' , ca ⟩ | ⟨ B' , cb ⟩ =
      ⟨ A' `× B' , c-pair ca cb ⟩
  conc (A `⊎ B) with conc A | conc B
  ... | ⟨ A' , ca ⟩ | ⟨ B' , cb ⟩ =
      ⟨ A' `⊎ B' , c-sum ca cb ⟩

  prec-unk-inv : ∀{A}
    → ⋆ `⊑ A
      ------
    → A ≡ ⋆
  prec-unk-inv {⋆} (prec f) = refl
  prec-unk-inv {` ι} (prec f) with f {` ι ⇒ ` ι} c-unk
  ... | ()
  prec-unk-inv {A ⇒ A₁} (prec f) with f {` Nat} c-unk
  ... | ()
  prec-unk-inv {A `× A₁} (prec f) with f {` Nat} c-unk
  ... | ()
  prec-unk-inv {A `⊎ A₁} (prec f) with f {` Nat} c-unk
  ... | ()

  prec-base-inv : ∀{A ι}
    → ` ι `⊑ A
      ---------------
    → A ≡ ` ι ⊎ A ≡ ⋆
  prec-base-inv {⋆} (prec f) = inj₂ refl
  prec-base-inv {` ι} {ι'} (prec f) with f {` ι'} c-base
  ... | c-base = inj₁ refl
  prec-base-inv {A ⇒ A₁} {ι} (prec f) with f {` ι} c-base
  ... | ()
  prec-base-inv {A `× A₁} {ι} (prec f) with f {` ι} c-base
  ... | ()
  prec-base-inv {A `⊎ A₁} {ι} (prec f) with f {` ι} c-base
  ... | ()

  prec-fun-inv : ∀{A₁ A₂ B₁ B₂}
     → (A₁ ⇒ A₂) `⊑ (B₁ ⇒ B₂)
       -----------------------
     → (A₁ `⊑ B₁) × (A₂ `⊑ B₂)
  prec-fun-inv {A₁}{A₂}{B₁}{B₂} (prec f) =
    ⟨ prec g , prec h ⟩
    where
    g : {S : SType} → Conc A₁ S → Conc B₁ S
    g ca with conc A₂
    ... | ⟨ A₂' , ca2 ⟩ with f (c-fun ca ca2)
    ... | c-fun a b = a
    
    h : {S : SType} → Conc A₂ S → Conc B₂ S
    h ca with conc A₁
    ... | ⟨ A' , ca1 ⟩ with f (c-fun ca1 ca )
    ... | c-fun a b = b

  prec-left-fun-inv : ∀{A₁ A₂ B}
     → (A₁ ⇒ A₂) `⊑ B
       -----------------------
     → (Σ[ B₁ ∈ Type ] Σ[ B₂ ∈ Type ] (B ≡ B₁ ⇒ B₂) × (A₁ `⊑ B₁) × (A₂ `⊑ B₂))
       ⊎ B ≡ ⋆
  prec-left-fun-inv {A₁} {A₂} {⋆} (prec f) = inj₂ refl
  prec-left-fun-inv {A₁} {A₂} {` ι} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-fun ca1 ca2)
  ... | ()
  prec-left-fun-inv {A₁} {A₂} {B₁ ⇒ B₂} (prec f) with prec-fun-inv (prec f)
  ... | ⟨ a1b1 , a2b2 ⟩ =
    inj₁ ⟨ B₁ , ⟨ B₂ , ⟨ refl , ⟨ a1b1 , a2b2 ⟩ ⟩ ⟩ ⟩
  prec-left-fun-inv {A₁} {A₂} {B `× B₁} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-fun ca1 ca2)
  ... | ()
  prec-left-fun-inv {A₁} {A₂} {B `⊎ B₁} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-fun ca1 ca2)
  ... | ()

  prec-pair-inv : ∀{A₁ A₂ B₁ B₂}
     → (A₁ `× A₂) `⊑ (B₁ `× B₂)
       -----------------------
     → (A₁ `⊑ B₁) × (A₂ `⊑ B₂)
  prec-pair-inv {A₁}{A₂}{B₁}{B₂} (prec f) =
    ⟨ prec g , prec h ⟩
    where
    g : {S : SType} → Conc A₁ S → Conc B₁ S
    g ca with conc A₂
    ... | ⟨ A₂' , ca2 ⟩ with f (c-pair ca ca2)
    ... | c-pair a b = a
    
    h : {S : SType} → Conc A₂ S → Conc B₂ S
    h ca with conc A₁
    ... | ⟨ A' , ca1 ⟩ with f (c-pair ca1 ca )
    ... | c-pair a b = b

  prec-left-pair-inv : ∀{A₁ A₂ B}
     → (A₁ `× A₂) `⊑ B
       -----------------------
     → (Σ[ B₁ ∈ Type ] Σ[ B₂ ∈ Type ] (B ≡ B₁ `× B₂) × (A₁ `⊑ B₁) × (A₂ `⊑ B₂))
       ⊎ B ≡ ⋆
  prec-left-pair-inv {A₁} {A₂} {⋆} (prec f) = inj₂ refl
  prec-left-pair-inv {A₁} {A₂} {` ι} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-pair ca1 ca2)
  ... | ()
  prec-left-pair-inv {A₁} {A₂} {B ⇒ B₁} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-pair ca1 ca2)
  ... | ()
  prec-left-pair-inv {A₁} {A₂} {B₁ `× B₂} (prec f) with prec-pair-inv (prec f)
  ... | ⟨ a1b1 , a2b2 ⟩ =
    inj₁ ⟨ B₁ , ⟨ B₂ , ⟨ refl , ⟨ a1b1 , a2b2 ⟩ ⟩ ⟩ ⟩
  prec-left-pair-inv {A₁} {A₂} {B `⊎ B₁} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-pair ca1 ca2)
  ... | ()

  prec-sum-inv : ∀{A₁ A₂ B₁ B₂}
     → (A₁ `⊎ A₂) `⊑ (B₁ `⊎ B₂)
       -----------------------
     → (A₁ `⊑ B₁) × (A₂ `⊑ B₂)
  prec-sum-inv {A₁}{A₂}{B₁}{B₂} (prec f) =
    ⟨ prec g , prec h ⟩
    where
    g : {S : SType} → Conc A₁ S → Conc B₁ S
    g ca with conc A₂
    ... | ⟨ A₂' , ca2 ⟩ with f (c-sum ca ca2)
    ... | c-sum a b = a
    
    h : {S : SType} → Conc A₂ S → Conc B₂ S
    h ca with conc A₁
    ... | ⟨ A' , ca1 ⟩ with f (c-sum ca1 ca )
    ... | c-sum a b = b

  prec-left-sum-inv : ∀{A₁ A₂ B}
     → (A₁ `⊎ A₂) `⊑ B
       -----------------------
     → (Σ[ B₁ ∈ Type ] Σ[ B₂ ∈ Type ] (B ≡ B₁ `⊎ B₂) × (A₁ `⊑ B₁) × (A₂ `⊑ B₂))
       ⊎ B ≡ ⋆
  prec-left-sum-inv {A₁} {A₂} {⋆} (prec f) = inj₂ refl
  prec-left-sum-inv {A₁} {A₂} {` ι} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-sum ca1 ca2)
  ... | ()
  prec-left-sum-inv {A₁} {A₂} {B ⇒ B₁} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-sum ca1 ca2)
  ... | ()
  prec-left-sum-inv {A₁} {A₂} {B `× B₁} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-sum ca1 ca2)
  ... | ()
  prec-left-sum-inv {A₁} {A₂} {B₁ `⊎ B₂} (prec f) with prec-sum-inv (prec f)
  ... | ⟨ a1b1 , a2b2 ⟩ =
    inj₁ ⟨ B₁ , ⟨ B₂ , ⟨ refl , ⟨ a1b1 , a2b2 ⟩ ⟩ ⟩ ⟩

  le-implies-prec : ∀ {A B} → A ⊑ B → B `⊑ A
  
  le-implies-prec unk⊑ = prec (λ {S} _ → c-unk)
  le-implies-prec base⊑ = prec (λ {S} z → z)
  le-implies-prec (fun⊑ le₁ le₂)
     with le-implies-prec le₁ | le-implies-prec le₂
  ... | prec imp1 | prec imp2 =
     prec λ { (c-fun x y) → c-fun (imp1 x) (imp2 y) }
  le-implies-prec (pair⊑ le₁ le₂)
     with le-implies-prec le₁ | le-implies-prec le₂
  ... | prec imp1 | prec imp2 =
     prec λ { (c-pair x y) → c-pair (imp1 x) (imp2 y) }
  le-implies-prec (sum⊑ le₁ le₂)
     with le-implies-prec le₁ | le-implies-prec le₂
  ... | prec imp1 | prec imp2 =
     prec λ { (c-sum x y) → c-sum (imp1 x) (imp2 y) }

  prec-implies-le : ∀{A B} → A `⊑ B → B ⊑ A
  prec-implies-le {⋆} {B} (prec f) with prec-unk-inv (prec f)
  ... | eq rewrite eq = unk⊑
  prec-implies-le {` ι} {B} (prec f) with prec-base-inv (prec f)
  ... | inj₁ eq rewrite eq = base⊑
  ... | inj₂ eq rewrite eq = unk⊑
  prec-implies-le {A₁ ⇒ A₂} {B} (prec f) with prec-left-fun-inv (prec f)
  ... | inj₁ ⟨ B₁ , ⟨ B₂ , ⟨ eq , ⟨ a1b1 , a2b2 ⟩ ⟩ ⟩ ⟩ rewrite eq =
        fun⊑ (prec-implies-le a1b1) (prec-implies-le a2b2)
  ... | inj₂ eq rewrite eq = unk⊑
  prec-implies-le {A₁ `× A₂} {B} (prec f) with prec-left-pair-inv (prec f)
  ... | inj₁ ⟨ B₁ , ⟨ B₂ , ⟨ eq , ⟨ a1b1 , a2b2 ⟩ ⟩ ⟩ ⟩ rewrite eq =
        pair⊑ (prec-implies-le a1b1) (prec-implies-le a2b2)
  ... | inj₂ eq rewrite eq = unk⊑
  prec-implies-le {A₁ `⊎ A₂} {B} (prec f) with prec-left-sum-inv (prec f)
  ... | inj₁ ⟨ B₁ , ⟨ B₂ , ⟨ eq , ⟨ a1b1 , a2b2 ⟩ ⟩ ⟩ ⟩ rewrite eq =
        sum⊑ (prec-implies-le a1b1) (prec-implies-le a2b2)
  ... | inj₂ eq rewrite eq = unk⊑

  data _~'_ : Type → Type → Set where
    cons : ∀ {A B : Type} {S : SType}
           → Conc A S → Conc B S
             -------------------
           → A ~' B

  cons-implies-ceq : ∀ {A B} → A ~ B → A ~' B
  cons-implies-ceq {.⋆}{B} unk~L with conc B
  ... | ⟨ B' , cb ⟩ = cons c-unk cb
  cons-implies-ceq {A}{⋆} unk~R with conc A
  ... | ⟨ A' , ca ⟩ = cons ca c-unk
  cons-implies-ceq base~ = cons c-base c-base
  cons-implies-ceq {A₁ ⇒ A₂}{B₁ ⇒ B₂} (fun~ cns₁ cns₂)
      with cons-implies-ceq cns₁ | cons-implies-ceq cns₂
  ... | cons{S = S₁} c1 c2 | cons{S = S₂} c3 c4 =
    cons (c-fun c2 c3) (c-fun c1 c4)
  cons-implies-ceq {A₁ `× A₂}{B₁ `× B₂} (pair~ cns₁ cns₂)
      with cons-implies-ceq cns₁ | cons-implies-ceq cns₂
  ... | cons{S = S₁} c1 c2 | cons{S = S₂} c3 c4 =
    cons (c-pair c1 c3) (c-pair c2 c4)
  cons-implies-ceq {A₁ `⊎ A₂}{B₁ `⊎ B₂} (sum~ cns₁ cns₂)
      with cons-implies-ceq cns₁ | cons-implies-ceq cns₂
  ... | cons{S = S₁} c1 c2 | cons{S = S₂} c3 c4 =
    cons (c-sum c1 c3) (c-sum c2 c4)

  ceq-implies-cons : ∀ {A B} → A ~' B → A ~ B
  ceq-implies-cons {.(` _)} {.(` _)} (cons {S = .(` _)} c-base c-base) = base~
  ceq-implies-cons {.(` _)} {.⋆} (cons {S = .(` _)} c-base c-unk) = unk~R
  ceq-implies-cons (cons {S = .(_ ⇒ _)} (c-fun as as₁) (c-fun bs bs₁)) =
      fun~ (ceq-implies-cons (cons bs as)) (ceq-implies-cons (cons as₁ bs₁))
  ceq-implies-cons (cons {S = .(_ ⇒ _)} (c-fun as as₁) c-unk) = unk~R
  ceq-implies-cons (cons {S = .(_ `× _)} (c-pair as as₁) (c-pair bs bs₁)) =
      pair~ (ceq-implies-cons (cons as bs)) (ceq-implies-cons (cons as₁ bs₁))
  ceq-implies-cons (cons {S = .(_ `× _)} (c-pair as as₁) c-unk) = unk~R
  ceq-implies-cons (cons {S = .(_ `⊎ _)} (c-sum as as₁) (c-sum bs bs₁)) =
      sum~ (ceq-implies-cons (cons as bs)) (ceq-implies-cons (cons as₁ bs₁))
  ceq-implies-cons (cons {S = .(_ `⊎ _)} (c-sum as as₁) c-unk) = unk~R
  ceq-implies-cons (cons {S = S} c-unk bs) = unk~L


  {- Abstraction -}

  data AllFuns : (SType → Set) → Set where
    funs : ∀{P}
      → (∀{T : SType} → P T → Σ[ T₁ ∈ SType ] Σ[ T₂ ∈ SType ]
            T ≡ T₁ ⇒ T₂)
        -----------------------------------------------------
      → AllFuns P

  data AllPairs : (SType → Set) → Set where
    pairs : ∀{P}
      → (∀{T : SType} → P T → Σ[ T₁ ∈ SType ] Σ[ T₂ ∈ SType ]
            T ≡ T₁ `× T₂)
        -----------------------------------------------------
      → AllPairs P

  data AllSums : (SType → Set) → Set where
    sums : ∀{P}
      → (∀{T : SType} → P T → Σ[ T₁ ∈ SType ] Σ[ T₂ ∈ SType ]
            T ≡ T₁ `⊎ T₂)
        -----------------------------------------------------
      → AllSums P

  data Dom : (SType → Set) → SType → Set where
    in-dom : ∀{P : (SType → Set)} {T₁ T₂}
      → P (T₁ ⇒ T₂)
        ---------------------------------------------
      → Dom P T₁

  data Cod : (SType → Set) → SType → Set where
    in-cod : ∀{P} {T₁ T₂}
      → P (T₁ ⇒ T₂)
        ---------------------------------------------
      → Cod P T₂

  data Proj₁ : (SType → Set) → SType → Set where
    in-proj₁ : ∀{P : (SType → Set)} {T₁ T₂}
      → P (T₁ `× T₂)
        ---------------------------------------------
      → Proj₁ P T₁

  data Proj₂ : (SType → Set) → SType → Set where
    in-proj₂ : ∀{P : (SType → Set)} {T₁ T₂}
      → P (T₁ `× T₂)
        ---------------------------------------------
      → Proj₂ P T₂

  data In₁ : (SType → Set) → SType → Set where
    in-in₁ : ∀{P : (SType → Set)} {T₁ T₂}
      → P (T₁ `⊎ T₂)
        ---------------------------------------------
      → In₁ P T₁

  data In₂ : (SType → Set) → SType → Set where
    in-in₂ : ∀{P : (SType → Set)} {T₁ T₂}
      → P (T₁ `⊎ T₂)
        ---------------------------------------------
      → In₂ P T₂

  data Abs : (SType → Set) → Type → Set₁ where
    abs-base : ∀{P : SType → Set} {ι : Base}
      → P (` ι)
      → (∀{T : SType} → P T → T ≡ ` ι)
        -------------------------------
      → Abs P (` ι)
    abs-fun : ∀{P : SType → Set}{A B : Type}
      → AllFuns P
      → Abs (Dom P) A
      → Abs (Cod P) B
        ----------------------
      → Abs P (A ⇒ B)
    abs-pair : ∀{P : SType → Set}{A B : Type}
      → AllPairs P
      → Abs (Proj₁ P) A
      → Abs (Proj₂ P) B
        ----------------------
      → Abs P (A `× B)
    abs-sum : ∀{P : SType → Set}{A B : Type}
      → AllSums P
      → Abs (In₁ P) A
      → Abs (In₂ P) B
        ----------------------
      → Abs P (A `⊎ B)
    abs-any : ∀{P : SType → Set} {S T : SType}
      → ¬ (S ⌢ T)
      → P S → P T
        ---------------
      → Abs P ⋆

  abs-non-empty : ∀{P : SType → Set}{A : Type}
                → Abs P A
                → Σ[ T ∈ SType ] P T
  abs-non-empty {P} {` ι} (abs-base x x₁) = ⟨ ` ι , x ⟩
  abs-non-empty {P} {⋆} (abs-any{T = T} x x₁ x₂) = ⟨ T , x₂ ⟩
  abs-non-empty {P} {_} (abs-fun x abs₁ abs₂)
      with abs-non-empty abs₁
  ... | ⟨ T₁ , in-dom {T₂ = T₂'} PT₁T₂' ⟩ =
        ⟨ (T₁ ⇒ T₂') , PT₁T₂' ⟩
  abs-non-empty {P} {_} (abs-pair x abs₁ abs₂)
      with abs-non-empty abs₁
  ... | ⟨ T₁ , in-proj₁ {T₂ = T₂'} PT₁T₂' ⟩ =
        ⟨ (T₁ `× T₂') , PT₁T₂' ⟩
  abs-non-empty {P} {_} (abs-sum x abs₁ abs₂)
      with abs-non-empty abs₁
  ... | ⟨ T₁ , in-in₁ {T₂ = T₂'} PT₁T₂' ⟩ =
        ⟨ (T₁ `⊎ T₂') , PT₁T₂' ⟩

  _⊆_ : (SType → Set) → (SType → Set) → Set
  P ⊆ P' = ∀{T : SType} → P T → P' T

  _⇔_ : (SType → Set) → (SType → Set) → Set
  P ⇔ P' = P ⊆ P' × P' ⊆ P

  dom-subset : ∀{P Q : SType → Set}
          →  P ⊆ Q
            -------------
          → Dom P ⊆ Dom Q
  dom-subset pq (in-dom x) = in-dom (pq x)

  proj₁-subset : ∀{P Q : SType → Set}
          →  P ⊆ Q
            -------------
          → Proj₁ P ⊆ Proj₁ Q
  proj₁-subset pq (in-proj₁ x) = in-proj₁ (pq x)

  in₁-subset : ∀{P Q : SType → Set}
          →  P ⊆ Q
            -------------
          → In₁ P ⊆ In₁ Q
  in₁-subset pq (in-in₁ x) = in-in₁ (pq x)

  cod-subset : ∀{P Q : SType → Set}
          →  P ⊆ Q
            -------------
          → Cod P ⊆ Cod Q
  cod-subset pq (in-cod x) = in-cod (pq x)

  proj₂-subset : ∀{P Q : SType → Set}
          →  P ⊆ Q
            -------------
          → Proj₂ P ⊆ Proj₂ Q
  proj₂-subset pq (in-proj₂ x) = in-proj₂ (pq x)

  in₂-subset : ∀{P Q : SType → Set}
          →  P ⊆ Q
            -------------
          → In₂ P ⊆ In₂ Q
  in₂-subset pq (in-in₂ x) = in-in₂ (pq x)

  dom-equiv : ∀{P Q : SType → Set}
          →  P ⇔ Q
            -------------
          → Dom P ⇔ Dom Q
  dom-equiv pq = ⟨ (dom-subset (proj₁ pq)) , (dom-subset (proj₂ pq)) ⟩

  cod-equiv : ∀{P Q : SType → Set}
          →  P ⇔ Q
            -------------
          → Cod P ⇔ Cod Q
  cod-equiv pq = ⟨ (cod-subset (proj₁ pq)) , (cod-subset (proj₂ pq)) ⟩

  proj₁-equiv : ∀{P Q : SType → Set}
          →  P ⇔ Q
            -----------------
          → Proj₁ P ⇔ Proj₁ Q
  proj₁-equiv pq = ⟨ (proj₁-subset (proj₁ pq)) , (proj₁-subset (proj₂ pq)) ⟩

  proj₂-equiv : ∀{P Q : SType → Set}
          →  P ⇔ Q
            -------------
          → Proj₂ P ⇔ Proj₂ Q
  proj₂-equiv pq = ⟨ (proj₂-subset (proj₁ pq)) , (proj₂-subset (proj₂ pq)) ⟩

  in₁-equiv : ∀{P Q : SType → Set}
          →  P ⇔ Q
            -----------------
          → In₁ P ⇔ In₁ Q
  in₁-equiv pq = ⟨ (in₁-subset (proj₁ pq)) , (in₁-subset (proj₂ pq)) ⟩

  in₂-equiv : ∀{P Q : SType → Set}
          →  P ⇔ Q
            -------------
          → In₂ P ⇔ In₂ Q
  in₂-equiv pq = ⟨ (in₂-subset (proj₁ pq)) , (in₂-subset (proj₂ pq)) ⟩

  allfuns-equiv : ∀{P Q : SType → Set}
          → AllFuns P   →  P ⇔ Q
            --------------------
          → AllFuns Q
  allfuns-equiv{P}{Q} (funs f) p-q = (funs G)
    where
    G : {T : SType} →
           Q T → Σ-syntax SType (λ T₁ → Σ-syntax SType (λ T₂ → T ≡ (T₁ ⇒ T₂)))
    G {T} qt with f {T} ((proj₂ p-q) qt)
    ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq =
          ⟨ T₁ , ⟨ T₂ , refl ⟩ ⟩

  allpairs-equiv : ∀{P Q : SType → Set}
          → AllPairs P   →  P ⇔ Q
            --------------------
          → AllPairs Q
  allpairs-equiv{P}{Q} (pairs f) p-q = (pairs G)
    where
    G : {T : SType} →
           Q T → Σ-syntax SType (λ T₁ → Σ-syntax SType (λ T₂ → T ≡ (T₁ `× T₂)))
    G {T} qt with f {T} ((proj₂ p-q) qt)
    ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq =
          ⟨ T₁ , ⟨ T₂ , refl ⟩ ⟩

  allsums-equiv : ∀{P Q : SType → Set}
          → AllSums P   →  P ⇔ Q
            --------------------
          → AllSums Q
  allsums-equiv{P}{Q} (sums f) p-q = (sums G)
    where
    G : {T : SType} →
           Q T → Σ-syntax SType (λ T₁ → Σ-syntax SType (λ T₂ → T ≡ (T₁ `⊎ T₂)))
    G {T} qt with f {T} ((proj₂ p-q) qt)
    ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq =
          ⟨ T₁ , ⟨ T₂ , refl ⟩ ⟩

  abs-equiv : ∀{P Q : SType → Set}{A : Type}
          → Abs P A  →  P ⇔ Q
            -----------------
          → Abs Q A
  abs-equiv (abs-base x x₁) p-q =
     abs-base (proj₁ p-q x) (λ {T} z → x₁ (proj₂ p-q z))
  abs-equiv{P}{Q} (abs-fun{A = A}{B = B} allf abs-dom-p abs-cod-p) p-q =
    let dp⇔dq = dom-equiv p-q in
    let cp⇔cq = cod-equiv p-q in
    abs-fun (allfuns-equiv allf p-q) (abs-equiv abs-dom-p (dom-equiv p-q))
                 (abs-equiv abs-cod-p (cod-equiv p-q) )
  abs-equiv{P}{Q} (abs-pair{A = A}{B = B} allf abs-dom-p abs-cod-p) p-q =
    let dp⇔dq = proj₁-equiv p-q in
    let cp⇔cq = proj₂-equiv p-q in
    abs-pair (allpairs-equiv allf p-q) (abs-equiv abs-dom-p (proj₁-equiv p-q))
                 (abs-equiv abs-cod-p (proj₂-equiv p-q) )
  abs-equiv{P}{Q} (abs-sum{A = A}{B = B} allf abs-dom-p abs-cod-p) p-q =
    let dp⇔dq = in₁-equiv p-q in
    let cp⇔cq = in₂-equiv p-q in
    abs-sum (allsums-equiv allf p-q) (abs-equiv abs-dom-p (in₁-equiv p-q))
                 (abs-equiv abs-cod-p (in₂-equiv p-q) )
  abs-equiv (abs-any x x₁ x₂) p-q =
     abs-any x (proj₁ p-q x₁) (proj₁ p-q x₂)

  conc-abs-sound : ∀{P : SType → Set}{A : Type}
     → Abs P A  
       ----------
     → P ⊆ Conc A
  conc-abs-sound (abs-base p-i p-base) {T} pt
      rewrite p-base {T} pt = c-base
  conc-abs-sound (abs-fun allfun abs-a abs-b) pt
      with allfun
  ... | funs af
      with af pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq =
        let ih1 = conc-abs-sound abs-a in
        let ih2 = conc-abs-sound abs-b in
        c-fun (ih1 (in-dom pt)) (ih2 (in-cod pt))
  conc-abs-sound (abs-pair all abs-a abs-b) pt
      with all
  ... | pairs af
      with af pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq =
        let ih1 = conc-abs-sound abs-a in
        let ih2 = conc-abs-sound abs-b in
        c-pair (ih1 (in-proj₁ pt)) (ih2 (in-proj₂ pt))
  conc-abs-sound (abs-sum all abs-a abs-b) pt
      with all
  ... | sums af
      with af pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq =
        let ih1 = conc-abs-sound abs-a in
        let ih2 = conc-abs-sound abs-b in
        c-sum (ih1 (in-in₁ pt)) (ih2 (in-in₂ pt))
  conc-abs-sound (abs-any x x₁ x₂) pt = c-unk

  c-any-base  : ∀{A ι}
     → Conc A (` ι)
     → A ≡ (` ι) ⊎ A ≡ ⋆
  c-any-base c-base = inj₁ refl
  c-any-base c-unk = inj₂ refl

  c-any-fun  : ∀{A T₁ T₂}
     → Conc A (T₁ ⇒ T₂)
     → (Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂ × Conc A₁ T₁ × Conc A₂ T₂)
       ⊎ A ≡ ⋆
  c-any-fun (c-fun{T₁}{T₂} c c₁) =
      inj₁ ⟨ T₁ , ⟨ T₂ , ⟨ refl , ⟨ c , c₁ ⟩ ⟩ ⟩ ⟩
  c-any-fun c-unk = inj₂ refl

  c-any-pair  : ∀{A T₁ T₂}
     → Conc A (T₁ `× T₂)
     → (Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂ × Conc A₁ T₁ × Conc A₂ T₂)
       ⊎ A ≡ ⋆
  c-any-pair (c-pair{T₁}{T₂} c c₁) =
      inj₁ ⟨ T₁ , ⟨ T₂ , ⟨ refl , ⟨ c , c₁ ⟩ ⟩ ⟩ ⟩
  c-any-pair c-unk = inj₂ refl

  c-any-sum  : ∀{A T₁ T₂}
     → Conc A (T₁ `⊎ T₂)
     → (Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂ × Conc A₁ T₁ × Conc A₂ T₂)
       ⊎ A ≡ ⋆
  c-any-sum (c-sum{T₁}{T₂} c c₁) =
      inj₁ ⟨ T₁ , ⟨ T₂ , ⟨ refl , ⟨ c , c₁ ⟩ ⟩ ⟩ ⟩
  c-any-sum c-unk = inj₂ refl

  conc-sh-cons : ∀{A T₁ T₂}
     → Conc A T₁  →  Conc A T₂
       -----------------------
     → A ≡ ⋆ ⊎ (T₁ ⌢ T₂)
  conc-sh-cons c-base c-base = inj₂ base⌢
  conc-sh-cons (c-fun a-t1 a-t3) (c-fun a-t2 a-t4) = inj₂ fun⌢
  conc-sh-cons (c-pair a-t1 a-t3) (c-pair a-t2 a-t4) = inj₂ pair⌢
  conc-sh-cons (c-sum a-t1 a-t3) (c-sum a-t2 a-t4) = inj₂ sum⌢
  conc-sh-cons c-unk a-t2 = inj₁ refl

  abs-optimal : ∀ {P : SType → Set} {A A' : Type}
    → (Σ[ T ∈ SType ] P T)
    → P ⊆ Conc A  →  Abs P A'
      -------------------------
    → A ⊑ A'
  abs-optimal ⟨ T , pt ⟩ p-ca (abs-base p-i all-base)
      with pt
  ... | pt'
      rewrite all-base pt
      with c-any-base (p-ca pt') 
  ... | inj₁ eq rewrite eq = Refl⊑
  ... | inj₂ eq rewrite eq = unk⊑
  abs-optimal{P = P} ⟨ T , pt ⟩ p-ca (abs-fun{A = A}{B = B} allf abs-p1-b1 abs-p2-b2)
      with allf
  ... | funs af
      with af pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq 
      with c-any-fun (p-ca pt)
  ... | inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ a=a12 , ⟨ c1 , c2 ⟩ ⟩ ⟩ ⟩ rewrite a=a12 =
      let ih1 = abs-optimal ⟨ T₁ , in-dom pt ⟩ domP⊆ca1 abs-p1-b1 in
      let ih2 = abs-optimal ⟨ T₂ , in-cod pt ⟩ codP⊆ca2 abs-p2-b2 in
      fun⊑ ih1 ih2
      where domP⊆ca1 : Dom P ⊆ Conc A₁
            domP⊆ca1 {T'} (in-dom {T₂ = T₂} PT'⇒T2)
                with p-ca PT'⇒T2 
            ... | c-fun c-a1t' c-a2t2 = c-a1t'

            codP⊆ca2 : Cod P ⊆ Conc A₂
            codP⊆ca2 {T'} (in-cod {T₁ = T₁} PT₁⇒T')
                with p-ca PT₁⇒T'
            ... | c-fun c1 c2 = c2
  ... | inj₂ a=unk rewrite a=unk =
        unk⊑
  abs-optimal{P = P} ⟨ T , pt ⟩ p-ca (abs-pair{A = A}{B = B} all abs-p1-b1 abs-p2-b2)
      with all
  ... | pairs ap
      with ap pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq 
      with c-any-pair (p-ca pt)
  ... | inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ a=a12 , ⟨ c1 , c2 ⟩ ⟩ ⟩ ⟩ rewrite a=a12 =
      let ih1 = abs-optimal ⟨ T₁ , in-proj₁ pt ⟩ domP⊆ca1 abs-p1-b1 in
      let ih2 = abs-optimal ⟨ T₂ , in-proj₂ pt ⟩ codP⊆ca2 abs-p2-b2 in
      pair⊑ ih1 ih2
      where domP⊆ca1 : Proj₁ P ⊆ Conc A₁
            domP⊆ca1 {T'} (in-proj₁ {T₂ = T₂} PT'⇒T2)
                with p-ca PT'⇒T2 
            ... | c-pair c-a1t' c-a2t2 = c-a1t'

            codP⊆ca2 : Proj₂ P ⊆ Conc A₂
            codP⊆ca2 {T'} (in-proj₂ {T₁ = T₁} PT₁⇒T')
                with p-ca PT₁⇒T'
            ... | c-pair c1 c2 = c2
  ... | inj₂ a=unk rewrite a=unk =
        unk⊑
  abs-optimal{P = P} ⟨ T , pt ⟩ p-ca (abs-sum{A = A}{B = B} all abs-p1-b1 abs-p2-b2)
      with all
  ... | sums ap
      with ap pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq 
      with c-any-sum (p-ca pt)
  ... | inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ a=a12 , ⟨ c1 , c2 ⟩ ⟩ ⟩ ⟩ rewrite a=a12 =
      let ih1 = abs-optimal ⟨ T₁ , in-in₁ pt ⟩ domP⊆ca1 abs-p1-b1 in
      let ih2 = abs-optimal ⟨ T₂ , in-in₂ pt ⟩ codP⊆ca2 abs-p2-b2 in
      sum⊑ ih1 ih2
      where domP⊆ca1 : In₁ P ⊆ Conc A₁
            domP⊆ca1 {T'} (in-in₁ {T₂ = T₂} PT'⇒T2)
                with p-ca PT'⇒T2 
            ... | c-sum c-a1t' c-a2t2 = c-a1t'

            codP⊆ca2 : In₂ P ⊆ Conc A₂
            codP⊆ca2 {T'} (in-in₂ {T₁ = T₁} PT₁⇒T')
                with p-ca PT₁⇒T'
            ... | c-sum c1 c2 = c2
  ... | inj₂ a=unk rewrite a=unk =
        unk⊑
  abs-optimal ⟨ T , pt ⟩ p-ca (abs-any a b c )
      with conc-sh-cons (p-ca b) (p-ca c) 
  ... | inj₁ A≡⋆ rewrite A≡⋆ = 
        unk⊑
  ... | inj₂ x = 
        contradiction x a

  all-funs-conc⇒ : ∀{A B} → AllFuns (Conc (A ⇒ B))
  all-funs-conc⇒{A}{B} = funs f
    where f : {T : SType} → Conc (A ⇒ B) T →
              Σ-syntax SType (λ T₁ → Σ-syntax SType (λ T₂ → T ≡ (T₁ ⇒ T₂)))
          f {.(_ ⇒ _)} (c-fun{S₁ = S₁}{S₂ = S₂} c c₁) = ⟨ S₁ , ⟨ S₂ , refl ⟩ ⟩

  all-pairs-conc× : ∀{A B} → AllPairs (Conc (A `× B))
  all-pairs-conc×{A}{B} = pairs f
    where f : {T : SType} → Conc (A `× B) T →
              Σ-syntax SType (λ T₁ → Σ-syntax SType (λ T₂ → T ≡ (T₁ `× T₂)))
          f {.(_ `× _)} (c-pair{S₁ = S₁}{S₂ = S₂} c c₁) = ⟨ S₁ , ⟨ S₂ , refl ⟩ ⟩

  all-sums-conc⊎ : ∀{A B} → AllSums (Conc (A `⊎ B))
  all-sums-conc⊎{A}{B} = sums f
    where f : {T : SType} → Conc (A `⊎ B) T →
              Σ-syntax SType (λ T₁ → Σ-syntax SType (λ T₂ → T ≡ (T₁ `⊎ T₂)))
          f {.(_ `⊎ _)} (c-sum{S₁ = S₁}{S₂ = S₂} c c₁) = ⟨ S₁ , ⟨ S₂ , refl ⟩ ⟩

  dom-conc⇒⊆ : ∀{A B} → Dom (Conc (A ⇒ B)) ⊆ Conc A
  dom-conc⇒⊆ (in-dom (c-fun x x₁)) = x

  proj₁-conc×⊆ : ∀{A B} → Proj₁ (Conc (A `× B)) ⊆ Conc A
  proj₁-conc×⊆ (in-proj₁ (c-pair x x₁)) = x

  in₁-conc⊎⊆ : ∀{A B} → In₁ (Conc (A `⊎ B)) ⊆ Conc A
  in₁-conc⊎⊆ (in-in₁ (c-sum x x₁)) = x

  cod-conc⇒⊆ : ∀{A B} → Cod (Conc (A ⇒ B)) ⊆ Conc B
  cod-conc⇒⊆ (in-cod (c-fun x x₁)) = x₁

  proj₂-conc×⊆ : ∀{A B} → Proj₂ (Conc (A `× B)) ⊆ Conc B
  proj₂-conc×⊆ (in-proj₂ (c-pair x x₁)) = x₁

  in₂-conc⊎⊆ : ∀{A B} → In₂ (Conc (A `⊎ B)) ⊆ Conc B
  in₂-conc⊎⊆ (in-in₂ (c-sum x x₁)) = x₁

  conc-dom⇒⊆ : ∀{A B} → Conc A ⊆ Dom (Conc (A ⇒ B))
  conc-dom⇒⊆ {ι}{B} c-base with conc B
  ... | ⟨ B' , x ⟩ = in-dom (c-fun c-base x)
  conc-dom⇒⊆ {B = B} (c-fun c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-dom (c-fun (c-fun c c₁) x)
  conc-dom⇒⊆ {B = B} (c-pair c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-dom (c-fun (c-pair c c₁) x)
  conc-dom⇒⊆ {B = B} (c-sum c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-dom (c-fun (c-sum c c₁) x)
  conc-dom⇒⊆ {B = B} c-unk with conc B
  ... | ⟨ B' , x ⟩ = in-dom (c-fun c-unk x)

  conc-proj₁×⊆ : ∀{A B} → Conc A ⊆ Proj₁ (Conc (A `× B))
  conc-proj₁×⊆ {ι}{B} c-base with conc B
  ... | ⟨ B' , x ⟩ = in-proj₁ (c-pair c-base x)
  conc-proj₁×⊆ {B = B} (c-fun c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-proj₁ (c-pair (c-fun c c₁) x)
  conc-proj₁×⊆ {B = B} (c-pair c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-proj₁ (c-pair (c-pair c c₁) x)
  conc-proj₁×⊆ {B = B} (c-sum c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-proj₁ (c-pair (c-sum c c₁) x)
  conc-proj₁×⊆ {B = B} c-unk with conc B
  ... | ⟨ B' , x ⟩ = in-proj₁ (c-pair c-unk x)

  conc-in₁⊎⊆ : ∀{A B} → Conc A ⊆ In₁ (Conc (A `⊎ B))
  conc-in₁⊎⊆ {ι}{B} c-base with conc B
  ... | ⟨ B' , x ⟩ = in-in₁ (c-sum c-base x)
  conc-in₁⊎⊆ {B = B} (c-fun c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-in₁ (c-sum (c-fun c c₁) x)
  conc-in₁⊎⊆ {B = B} (c-pair c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-in₁ (c-sum (c-pair c c₁) x)
  conc-in₁⊎⊆ {B = B} (c-sum c c₁) with conc B
  ... | ⟨ B' , x ⟩ = in-in₁ (c-sum (c-sum c c₁) x)
  conc-in₁⊎⊆ {B = B} c-unk with conc B
  ... | ⟨ B' , x ⟩ = in-in₁ (c-sum c-unk x)

  conc-cod⇒⊆ : ∀{A B} → Conc B ⊆ Cod (Conc (A ⇒ B))
  conc-cod⇒⊆ {A} {.(` _)} c-base with conc A
  ... | ⟨ A' , x ⟩ = in-cod (c-fun x c-base)
  conc-cod⇒⊆ {A} {.(_ ⇒ _)} (c-fun cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-cod (c-fun x (c-fun cb cb₁))
  conc-cod⇒⊆ {A} {.(_ `× _)} (c-pair cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-cod (c-fun x (c-pair cb cb₁))
  conc-cod⇒⊆ {A} {.(_ `⊎ _)} (c-sum cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-cod (c-fun x (c-sum cb cb₁))
  conc-cod⇒⊆ {A} {.⋆} c-unk with conc A
  ... | ⟨ A' , x ⟩ = in-cod (c-fun x c-unk)

  conc-proj₂×⊆ : ∀{A B} → Conc B ⊆ Proj₂ (Conc (A `× B))
  conc-proj₂×⊆ {A} {.(` _)} c-base with conc A
  ... | ⟨ A' , x ⟩ = in-proj₂ (c-pair x c-base)
  conc-proj₂×⊆ {A} {.(_ ⇒ _)} (c-fun cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-proj₂ (c-pair x (c-fun cb cb₁))
  conc-proj₂×⊆ {A} {.(_ `× _)} (c-pair cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-proj₂ (c-pair x (c-pair cb cb₁))
  conc-proj₂×⊆ {A} {.(_ `⊎ _)} (c-sum cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-proj₂ (c-pair x (c-sum cb cb₁))
  conc-proj₂×⊆ {A} {.⋆} c-unk with conc A
  ... | ⟨ A' , x ⟩ = in-proj₂ (c-pair x c-unk)

  conc-in₂⊎⊆ : ∀{A B} → Conc B ⊆ In₂ (Conc (A `⊎ B))
  conc-in₂⊎⊆ {A} {.(` _)} c-base with conc A
  ... | ⟨ A' , x ⟩ = in-in₂ (c-sum x c-base)
  conc-in₂⊎⊆ {A} {.(_ ⇒ _)} (c-fun cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-in₂ (c-sum x (c-fun cb cb₁))
  conc-in₂⊎⊆ {A} {.(_ `× _)} (c-pair cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-in₂ (c-sum x (c-pair cb cb₁))
  conc-in₂⊎⊆ {A} {.(_ `⊎ _)} (c-sum cb cb₁) with conc A
  ... | ⟨ A' , x ⟩ = in-in₂ (c-sum x (c-sum cb cb₁))
  conc-in₂⊎⊆ {A} {.⋆} c-unk with conc A
  ... | ⟨ A' , x ⟩ = in-in₂ (c-sum x c-unk)

  dom-conc⇒⇔ : ∀{A B} → Dom (Conc (A ⇒ B)) ⇔ Conc A
  dom-conc⇒⇔ = ⟨ dom-conc⇒⊆ , conc-dom⇒⊆ ⟩

  proj₁-conc×⇔ : ∀{A B} → Proj₁ (Conc (A `× B)) ⇔ Conc A
  proj₁-conc×⇔ = ⟨ proj₁-conc×⊆ , conc-proj₁×⊆ ⟩

  in₁-conc⊎⇔ : ∀{A B} → In₁ (Conc (A `⊎ B)) ⇔ Conc A
  in₁-conc⊎⇔ = ⟨ in₁-conc⊎⊆ , conc-in₁⊎⊆ ⟩

  cod-conc⇒⇔ : ∀{A B} → Cod (Conc (A ⇒ B)) ⇔ Conc B
  cod-conc⇒⇔ = ⟨ cod-conc⇒⊆ , conc-cod⇒⊆ ⟩

  proj₂-conc×⇔ : ∀{A B} → Proj₂ (Conc (A `× B)) ⇔ Conc B
  proj₂-conc×⇔ = ⟨ proj₂-conc×⊆ , conc-proj₂×⊆ ⟩

  in₂-conc⊎⇔ : ∀{A B} → In₂ (Conc (A `⊎ B)) ⇔ Conc B
  in₂-conc⊎⇔ = ⟨ in₂-conc⊎⊆ , conc-in₂⊎⊆ ⟩

  Sym⇔ : ∀{P Q} → P ⇔ Q → Q ⇔ P
  Sym⇔ pq = ⟨ (proj₂ pq) , (proj₁ pq) ⟩

{-
   Corollary abs-optimimal and conc-abs-sound:

   α(γ(A)) = A

   -}

  conc-abs-id : ∀{A B : Type}{P : SType → Set}
    → Abs (Conc A) B
      -------------------
    → A ≡ B
  conc-abs-id {A}{B}{P} abs-conc-ab =
    let A⊑B = (abs-optimal {Conc A}{A}{B} (conc A) (λ {T} z → z)) abs-conc-ab in
    let B⊑A = prec-implies-le (prec (conc-abs-sound abs-conc-ab)) in
    AntiSym⊑ A⊑B B⊑A

  conc-abs-id2 : ∀{A : Type}{P : SType → Set}
    → Abs (Conc A) A
  conc-abs-id2 {⋆} {P} = abs-any{S = ` Nat}{T = ` 𝔹} (λ ()) c-unk c-unk
  conc-abs-id2 {` x} {P} = abs-base c-base G
     where G : {T : SType} → Conc (` x) T → T ≡ (` x)
           G {.(` _)} c-base = refl
  conc-abs-id2 {A ⇒ B} {P} =
     let x1 = Sym⇔ (dom-conc⇒⇔ {A} {B}) in
     let ih1 = conc-abs-id2 {A} {P} in 
     let y1 = abs-equiv ih1 x1 in
     let x2 = Sym⇔ (cod-conc⇒⇔ {A} {B}) in
     let ih2 = conc-abs-id2 {B} {P} in 
     let y2 = abs-equiv ih2 x2 in
     abs-fun all-funs-conc⇒ y1 y2
  conc-abs-id2 {A `× B} {P} =
     let x1 = Sym⇔ (proj₁-conc×⇔ {A} {B}) in
     let ih1 = conc-abs-id2 {A} {P} in 
     let y1 = abs-equiv ih1 x1 in
     let x2 = Sym⇔ (proj₂-conc×⇔ {A} {B}) in
     let ih2 = conc-abs-id2 {B} {P} in 
     let y2 = abs-equiv ih2 x2 in
     abs-pair all-pairs-conc× y1 y2
  conc-abs-id2 {A `⊎ B} {P} =
     let x1 = Sym⇔ (in₁-conc⊎⇔ {A} {B}) in
     let ih1 = conc-abs-id2 {A} {P} in 
     let y1 = abs-equiv ih1 x1 in
     let x2 = Sym⇔ (in₂-conc⊎⇔ {A} {B}) in
     let ih2 = conc-abs-id2 {B} {P} in 
     let y2 = abs-equiv ih2 x2 in
     abs-sum all-sums-conc⊎ y1 y2
  


  {-
   Def. of interior based on Prop 15 and a little subsequent reasoning.
   -}

  data L (P : SType → SType → Set) (G₁ : Type) (G₂ : Type) : SType → Set where
    leftp : ∀{T₁ T₂ : SType}
           → Conc G₁ T₁  →  Conc G₂ T₂  →  P T₁ T₂
             -------------------------------------
           → L P G₁ G₂ T₁

  data R (P : SType → SType → Set) (G₁ : Type) (G₂ : Type) : SType → Set where
    rightp : ∀{T₁ T₂ : SType}
           → Conc G₁ T₁  →  Conc G₂ T₂  →  P T₁ T₂
             -------------------------------------
           → R P G₁ G₂ T₂

  data Interior {n : Level} (P : SType → SType → Set)
               : Type → Type → Type → Type → Set₁ where
    inter : ∀{G₁ G₂ G₃ G₄}
          → Abs (L P G₁ G₂) G₃
          → Abs (R P G₁ G₂) G₄
            ----------------------
          → Interior P G₁ G₂ G₃ G₄

  L⇒-intro : ∀{P : SType → SType → Set}{G₁₁ G₁₂ G₂₁ G₂₂ T₁ T₂}
      → (∀{T₁ T₂ T₃ T₄ : SType} → P T₁ T₃ → P T₂ T₄ → P (T₁ ⇒ T₂) (T₃ ⇒ T₄))
      → L P G₁₁ G₂₁ T₁ → L P G₁₂ G₂₂ T₂
      → L P (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂) (T₁ ⇒ T₂)
  L⇒-intro p (leftp x x₁ x₂) (leftp x₃ x₄ x₅) =
      leftp (c-fun x x₃) (c-fun x₁ x₄) (p x₂ x₅)
 
  L⇒-elim : ∀{P : SType → SType → Set}{G₁₁ G₁₂ G₂₁ G₂₂ T₁ T₂}
      → (∀{T₁ T₂ T₃ T₄ : SType} → P (T₁ ⇒ T₂) (T₃ ⇒ T₄) → P T₁ T₃ × P T₂ T₄)
      → L P (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂) (T₁ ⇒ T₂)
      → L P G₁₁ G₂₁ T₁ × L P G₁₂ G₂₂ T₂
  L⇒-elim p (leftp (c-fun x x₄) (c-fun x₁ x₃) x₂) =
     ⟨ (leftp x x₁ (proj₁ (p x₂))) , leftp x₄ x₃ (proj₂ (p x₂)) ⟩

  data STypeEq (A : SType) (B : SType) : Set where
    stype-eq : A ≡ B → STypeEq A B

  L=→cc : ∀{G₁ G₂ T} → L STypeEq G₁ G₂ T → Conc G₁ T × Conc G₂ T
  L=→cc (leftp x x₁ (stype-eq refl)) = ⟨ x , x₁ ⟩

  cc→L= : ∀{G₁ G₂ T} → Conc G₁ T → Conc G₂ T → L STypeEq G₁ G₂ T
  cc→L= g1t g2t = leftp g1t g2t (stype-eq refl)

  L=→R= : ∀{G₁ G₂ T} → L STypeEq G₁ G₂ T → R STypeEq G₁ G₂ T
  L=→R= (leftp x x₁ (stype-eq refl)) = rightp x x₁ (stype-eq refl)

  R=→L= : ∀{G₁ G₂ T} → R STypeEq G₁ G₂ T → L STypeEq G₁ G₂ T
  R=→L= (rightp x x₁ (stype-eq refl)) = leftp x x₁ (stype-eq refl)

  L=⇔R= : ∀{G₁ G₂} → R STypeEq G₁ G₂ ⇔ L STypeEq G₁ G₂
  L=⇔R= = ⟨ R=→L= , L=→R= ⟩

  cct-consis : ∀{G1 G2 T} → Conc G1 T → Conc G2 T → G1 ~ G2
  cct-consis c-base c-base = base~
  cct-consis c-base c-unk = unk~R
  cct-consis (c-fun c1t c1t₁) (c-fun c2t c2t₁) =
      fun~ (cct-consis c2t c1t) (cct-consis c1t₁ c2t₁)
  cct-consis (c-fun c1t c1t₁) c-unk = unk~R
  cct-consis (c-pair c1t c1t₁) (c-pair c2t c2t₁) =
      pair~ (cct-consis c1t c2t) (cct-consis c1t₁ c2t₁)
  cct-consis (c-pair c1t c1t₁) c-unk = unk~R
  cct-consis (c-sum c1t c1t₁) (c-sum c2t c2t₁) =
      sum~ (cct-consis c1t c2t) (cct-consis c1t₁ c2t₁)
  cct-consis (c-sum c1t c1t₁) c-unk = unk~R
  cct-consis c-unk c2t = unk~L

  cct-c⊔' : ∀{G1 G2 T} {c : G1 ~ G2} → (c1 : Conc G1 T) → (c2 : Conc G2 T)
           → Conc ((G1 ⊔ G2){c}) T
  cct-c⊔' {` ι}{` ι}{c = c} c-base c-base with (` ι `⊔ ` ι){c}
  ... | ⟨ T , ⟨ ⟨ base⊑ , base⊑ ⟩ , b ⟩ ⟩ = c-base
  cct-c⊔' {` ι}{⋆}{c = c} c-base c-unk with (` ι `⊔ ⋆){c}
  ... | ⟨ T , ⟨ ⟨ base⊑ , unk⊑ ⟩ , b ⟩ ⟩ = c-base
  cct-c⊔'{c = fun~ c1 c2} (c-fun c1t c1t₁) (c-fun c2t c2t₁) =
      c-fun (cct-c⊔' {c = c1} c2t c1t) (cct-c⊔' {c = c2} c1t₁ c2t₁)
  cct-c⊔'{c = unk~R} (c-fun c1t c1t₁) c-unk = c-fun c1t c1t₁
  cct-c⊔'{c = pair~ c1 c2} (c-pair c1t c1t₁) (c-pair c2t c2t₁) =
      c-pair (cct-c⊔' {c = c1} c1t c2t) (cct-c⊔' {c = c2} c1t₁ c2t₁)
  cct-c⊔'{c = unk~R} (c-pair c1t c1t₁) c-unk = c-pair c1t c1t₁
  cct-c⊔'{c = sum~ c1 c2} (c-sum c1t c1t₁) (c-sum c2t c2t₁) =
      c-sum (cct-c⊔' {c = c1} c1t c2t) (cct-c⊔' {c = c2} c1t₁ c2t₁)
  cct-c⊔'{c = unk~R} (c-sum c1t c1t₁) c-unk = c-sum c1t c1t₁
  cct-c⊔'{⋆}{G2}{c = unk~L} c-unk c2t with (⋆ `⊔ G2){unk~L}
  ... | ⟨ T , ⟨ ⟨ x , y ⟩ , b ⟩ ⟩ = c2t
  cct-c⊔' {⋆} {⋆} {c = unk~R {⋆}} c-unk c-unk = c-unk

  cct-c⊔ : ∀{G1 G2 T} → (c1 : Conc G1 T) → (c2 : Conc G2 T)
           → Conc ((G1 ⊔ G2){cct-consis c1 c2}) T
  cct-c⊔ c-base c-base = c-base
  cct-c⊔ c-base c-unk = c-base
  cct-c⊔ (c-fun c1t c1t₁) (c-fun c2t c2t₁) =
      c-fun (cct-c⊔ c2t c1t) (cct-c⊔ c1t₁ c2t₁)
  cct-c⊔ (c-fun c1t c1t₁) c-unk = c-fun c1t c1t₁
  cct-c⊔ (c-pair c1t c1t₁) (c-pair c2t c2t₁) =
      c-pair (cct-c⊔ c1t c2t) (cct-c⊔ c1t₁ c2t₁)
  cct-c⊔ (c-pair c1t c1t₁) c-unk = c-pair c1t c1t₁
  cct-c⊔ (c-sum c1t c1t₁) (c-sum c2t c2t₁) =
      c-sum (cct-c⊔ c1t c2t) (cct-c⊔ c1t₁ c2t₁)
  cct-c⊔ (c-sum c1t c1t₁) c-unk = c-sum c1t c1t₁
  cct-c⊔ c-unk c2t = c2t

  c⊔-cct : ∀{G1 G2 T c} → Conc ((G1 ⊔ G2){c}) T
         → (Conc G1 T × Conc G2 T)
  c⊔-cct {.⋆} {G2} {T} {unk~L} ct = ⟨ c-unk , ct ⟩
  c⊔-cct {G1} {.⋆} {T} {unk~R} ct = ⟨ ct , c-unk ⟩
  c⊔-cct {.(` _)} {.(` _)} {T} {base~} ct = ⟨ ct , ct ⟩
  c⊔-cct {A₁ ⇒ A₂} {B₁ ⇒ B₂} {T₁ ⇒ T₂} {fun~ c c₁} (c-fun ct ct₁) 
      with c⊔-cct {c = c} ct | c⊔-cct {c = c₁} ct₁
  ... | ⟨ cb1 , ca1 ⟩ | ⟨ cb2 , ba2 ⟩ = 
        ⟨ (c-fun ca1 cb2) , (c-fun cb1 ba2) ⟩
  c⊔-cct {A₁ `× A₂} {B₁ `× B₂} {T₁ `× T₂} {pair~ c c₁} (c-pair ct ct₁)
      with c⊔-cct {c = c} ct | c⊔-cct {c = c₁} ct₁
  ... | ⟨ cb1 , ca1 ⟩ | ⟨ cb2 , ba2 ⟩ = 
        ⟨ (c-pair cb1 cb2) , (c-pair ca1 ba2) ⟩
  c⊔-cct {A₁ `⊎ A₂} {B₁ `⊎ B₂} {T₁ `⊎ T₂} {sum~ c c₁} (c-sum ct ct₁)
      with c⊔-cct {c = c} ct | c⊔-cct {c = c₁} ct₁
  ... | ⟨ cb1 , ca1 ⟩ | ⟨ cb2 , ba2 ⟩ = 
        ⟨ (c-sum cb1 cb2) , (c-sum ca1 ba2 ) ⟩

  _iff_ : Set → Set → Set
  P iff Q = (P → Q) × (Q → P)

  prop-17 : ∀{G1 G2 T} →
     (Σ[ c ∈ G1 ~ G2 ] Conc ((G1 ⊔ G2){c}) T) iff (Conc G1 T × Conc G2 T)
  prop-17 {G1}{G2}{T} = ⟨ G , H ⟩
    where G : Σ-syntax (G1 ~ G2) (λ c → Conc ((G1 ⊔ G2){c}) T) →
               Conc G1 T × Conc G2 T
          G ⟨ fst , snd ⟩ = c⊔-cct {G1}{G2}{T}{fst} snd

          H : Conc G1 T × Conc G2 T →
                 Σ-syntax (G1 ~ G2) (λ c → Conc ((G1 ⊔ G2){c}) T)
          H ⟨ fst , snd ⟩ = ⟨ (cct-consis fst snd) , (cct-c⊔ fst snd) ⟩

  I= : Type → Type → Type → Type → Set₁ 
  I= = Interior {lzero} STypeEq

  conc-prec : ∀{G : Type}{T : SType} → Conc G T → G ⊑ to-type T
  conc-prec c-base = base⊑
  conc-prec (c-fun g-t g-t₁) = fun⊑ (conc-prec g-t) (conc-prec g-t₁)
  conc-prec (c-pair g-t g-t₁) = pair⊑ (conc-prec g-t) (conc-prec g-t₁)
  conc-prec (c-sum g-t g-t₁) = sum⊑ (conc-prec g-t) (conc-prec g-t₁)
  conc-prec c-unk = unk⊑

  to-type-base : ∀{T ι} → (` ι) ≡ to-type T  →  T ≡ (` ι)
  to-type-base {` ι'} refl = refl
  to-type-base {T ⇒ T₁} ()
  to-type-base {T₁ `× T₂} ()
  to-type-base {T₁ `⊎ T₂} ()

  cong⇒L : ∀{G₁ G₂ T₁ T₂ : Type} → (_≡_ {a = lzero}{A = Type} (G₁ ⇒ G₂) (T₁ ⇒ T₂)) → G₁ ≡ T₁
  cong⇒L refl = refl

  cong⇒R : ∀{G₁ G₂ T₁ T₂ : Type} → (_≡_ {a = lzero}{A = Type} (G₁ ⇒ G₂) (T₁ ⇒ T₂)) → G₂ ≡ T₂
  cong⇒R refl = refl

  cong×L : ∀{G₁ G₂ T₁ T₂ : Type} → (_≡_ {a = lzero}{A = Type} (G₁ `× G₂) (T₁ `× T₂)) → G₁ ≡ T₁
  cong×L refl = refl

  cong×R : ∀{G₁ G₂ T₁ T₂ : Type} → (_≡_ {a = lzero}{A = Type} (G₁ `× G₂) (T₁ `× T₂)) → G₂ ≡ T₂
  cong×R refl = refl

  cong⊎L : ∀{G₁ G₂ T₁ T₂ : Type} → (_≡_ {a = lzero}{A = Type} (G₁ `⊎ G₂) (T₁ `⊎ T₂)) → G₁ ≡ T₁
  cong⊎L refl = refl

  cong⊎R : ∀{G₁ G₂ T₁ T₂ : Type} → (_≡_ {a = lzero}{A = Type} (G₁ `⊎ G₂) (T₁ `⊎ T₂)) → G₂ ≡ T₂
  cong⊎R refl = refl

  to-type-fun : ∀{T G₁ G₂} → (G₁ ⇒ G₂) ≡ to-type T
        →  Σ[ T₁ ∈ SType ] Σ[ T₂ ∈ SType ]
           T ≡ T₁ ⇒ T₂ × G₁ ≡ to-type T₁ × G₂ ≡ to-type T₂
  to-type-fun {` x} ()
  to-type-fun {T₁ ⇒ T₂} g12-t =
      ⟨ T₁ , ⟨ T₂ , ⟨ refl , ⟨ cong⇒L g12-t , cong⇒R g12-t ⟩ ⟩ ⟩ ⟩
  to-type-fun {T `× T₁} ()
  to-type-fun {T `⊎ T₁} ()

  to-type-pair : ∀{T G₁ G₂} → (G₁ `× G₂) ≡ to-type T
        →  Σ[ T₁ ∈ SType ] Σ[ T₂ ∈ SType ]
           T ≡ T₁ `× T₂ × G₁ ≡ to-type T₁ × G₂ ≡ to-type T₂
  to-type-pair {` x} ()
  to-type-pair {T ⇒ T₁} ()
  to-type-pair {T₁ `× T₂} g12-t =
      ⟨ T₁ , ⟨ T₂ , ⟨ refl , ⟨ cong×L g12-t , cong×R g12-t ⟩ ⟩ ⟩ ⟩
  to-type-pair {T `⊎ T₁} ()

  to-type-sum : ∀{T G₁ G₂} → (G₁ `⊎ G₂) ≡ to-type T
        →  Σ[ T₁ ∈ SType ] Σ[ T₂ ∈ SType ]
           T ≡ T₁ `⊎ T₂ × G₁ ≡ to-type T₁ × G₂ ≡ to-type T₂
  to-type-sum {` x} ()
  to-type-sum {T ⇒ T₁} ()
  to-type-sum {T `× T₁} ()
  to-type-sum {T₁ `⊎ T₂} g12-t =
      ⟨ T₁ , ⟨ T₂ , ⟨ refl , ⟨ cong⊎L g12-t , cong⊎R g12-t ⟩ ⟩ ⟩ ⟩

  prec-conc : ∀{G G' : Type}{T : SType} → G ⊑ G' → G' ≡ to-type T → Conc G T
  prec-conc unk⊑ g'-t = c-unk
  prec-conc base⊑ g'-t rewrite to-type-base g'-t = c-base
  prec-conc (fun⊑ g-g' g-g'') g'-t
      with to-type-fun g'-t
  ... | ⟨ T₁ , ⟨ T₂ , ⟨ T≡T₁⇒T₂ , ⟨ G₁≡T₁ , G₂≡T₂ ⟩ ⟩ ⟩ ⟩
      rewrite G₁≡T₁ | G₂≡T₂ | T≡T₁⇒T₂ =
       c-fun (prec-conc g-g' refl) (prec-conc g-g'' refl)
  prec-conc (pair⊑ g-g' g-g'') g'-t
      with to-type-pair g'-t
  ... | ⟨ T₁ , ⟨ T₂ , ⟨ T≡T₁×T₂ , ⟨ G₁≡T₁ , G₂≡T₂ ⟩ ⟩ ⟩ ⟩
      rewrite G₁≡T₁ | G₂≡T₂ | T≡T₁×T₂ =
       c-pair (prec-conc g-g' refl) (prec-conc g-g'' refl)
  prec-conc (sum⊑ g-g' g-g'') g'-t
      with to-type-sum g'-t
  ... | ⟨ T₁ , ⟨ T₂ , ⟨ T≡T₁⊎T₂ , ⟨ G₁≡T₁ , G₂≡T₂ ⟩ ⟩ ⟩ ⟩
      rewrite G₁≡T₁ | G₂≡T₂ | T≡T₁⊎T₂ =
       c-sum (prec-conc g-g' refl) (prec-conc g-g'' refl)

  L=⋆⋆ : ∀{T : SType} → L STypeEq ⋆ ⋆ T
  L=⋆⋆ {T} = leftp c-unk c-unk (stype-eq refl)

  L=⋆G→conc : ∀{G : Type}{T : SType} → L STypeEq ⋆ G T → Conc G T
  L=⋆G→conc {G} {T} (leftp c-unk x₁ (stype-eq refl)) = x₁

  L=G⋆→conc : ∀{G : Type}{T : SType} → L STypeEq G ⋆ T → Conc G T
  L=G⋆→conc {G} {T} (leftp x c-unk (stype-eq x₁)) = x

  conc→L=G⋆ : ∀{G : Type}{T : SType} → Conc G T → L STypeEq G ⋆ T
  conc→L=G⋆ c-base = leftp c-base c-unk (stype-eq refl)
  conc→L=G⋆ (c-fun cgt cgt₁) = leftp (c-fun cgt cgt₁) c-unk (stype-eq refl)
  conc→L=G⋆ (c-pair cgt cgt₁) = leftp (c-pair cgt cgt₁) c-unk (stype-eq refl)
  conc→L=G⋆ (c-sum cgt cgt₁) = leftp (c-sum cgt cgt₁) c-unk (stype-eq refl)
  conc→L=G⋆ c-unk = leftp c-unk c-unk (stype-eq refl)
  
  conc→L=⋆G : ∀{G : Type}{T : SType} → Conc G T → L STypeEq G ⋆ T
  conc→L=⋆G c-base = leftp c-base c-unk (stype-eq refl)
  conc→L=⋆G (c-fun cgt cgt₁) = leftp (c-fun cgt cgt₁) c-unk (stype-eq refl)
  conc→L=⋆G (c-pair cgt cgt₁) = leftp (c-pair cgt cgt₁) c-unk (stype-eq refl)
  conc→L=⋆G (c-sum cgt cgt₁) = leftp (c-sum cgt cgt₁) c-unk (stype-eq refl)
  conc→L=⋆G c-unk = leftp c-unk c-unk (stype-eq refl)
  
  all-funs-L= : ∀{G₁ G₂ G₃ G₄} → AllFuns (L STypeEq (G₁ ⇒ G₂) (G₃ ⇒ G₄))
  all-funs-L= {G₁}{G₂}{G₃}{G₄} = funs f
     where f : {T : SType} →
             L STypeEq (G₁ ⇒ G₂) (G₃ ⇒ G₄) T →
             Σ-syntax SType (λ T₁ → Σ-syntax SType (λ T₂ → T ≡ (T₁ ⇒ T₂)))
           f {S₃ ⇒ S₄} (leftp (c-fun x x₃) (c-fun x₁ x₄) x₂) =
               ⟨ S₃ , ⟨ S₄ , refl ⟩ ⟩

  γ⊔ : (G₁ : Type) → (G₂ : Type) → (c : G₁ ~ G₂) → SType → Set
  γ⊔ G₁ G₂ c T = Conc ((G₁ ⊔ G₂){c}) T

  L=→Conc⊔ : ∀ {G₁ G₂ T} → (c : G₁ ~ G₂) → L STypeEq G₁ G₂ T → γ⊔ G₁ G₂ c T
  L=→Conc⊔{G₁}{G₂}{T} c l =
     cct-c⊔' {c = c} (proj₁ (L=→cc l)) (proj₂ (L=→cc l))

  Conc⊔→L= : ∀ {G₁ G₂ T} → (c : G₁ ~ G₂) → (γ⊔ G₁ G₂ c T) → L STypeEq G₁ G₂ T 
  Conc⊔→L= {G₁} {G₂} {T} c T∈γG₁⊔G₂ with prop-17{G₁}{G₂}{T}
  ... | ⟨ f , g ⟩
      with f ⟨ c , T∈γG₁⊔G₂ ⟩
  ... | ⟨ a , b ⟩ = cc→L= a b 

  Conc⊔⇔L= : ∀ {G₁ G₂} → (c : G₁ ~ G₂) → (γ⊔ G₁ G₂ c) ⇔ L STypeEq G₁ G₂
  Conc⊔⇔L= c = ⟨ Conc⊔→L= c , L=→Conc⊔ c ⟩

  Trans⇔ : ∀{P Q R} → P ⇔ Q → Q ⇔ R → P ⇔ R
  Trans⇔ pq qr = ⟨ (λ {T} z → proj₁ qr (proj₁ pq z)) , (λ {T} z → proj₂ pq (proj₂ qr z)) ⟩

  abs-γ⊔ : ∀ {G₁ G₂} → (c : G₁ ~ G₂)
         → Abs (γ⊔ G₁ G₂ c) ((G₁ ⊔ G₂) {c})
  abs-γ⊔ {G₁}{G₂} c = conc-abs-id2{P = (γ⊔ G₁ G₂ c)}
        
  prop-16 : ∀ {G₁ G₂} → (c : G₁ ~ G₂) → I= G₁ G₂ ((G₁ ⊔ G₂){c}) ((G₁ ⊔ G₂){c})
  prop-16 {G₁}{G₂} c =
     inter (abs-equiv (abs-γ⊔ c) (Conc⊔⇔L= c))
           (abs-equiv (abs-γ⊔ c) (Trans⇔ (Conc⊔⇔L= c) (Sym⇔ (L=⇔R= {G₁}{G₂}))))

  STypeEq⇒ : ∀ {T₁ T₂ T₃ T₄ : SType}
           → STypeEq T₁ T₃ → STypeEq T₂ T₄
           → STypeEq (T₁ ⇒ T₂) (T₃ ⇒ T₄)
  STypeEq⇒ (stype-eq refl) (stype-eq refl) = stype-eq refl

  {- 

   In AGT with simple types, casts are a triple of types where the
   middle type is an upper bound of the source and target, which
   corresponds to the threesomes of Siek and Wadler (2010).

   -}

  data Cast : Type → Set where
    _⇒_⇒_ : (A : Type) → (B : Type) → (C : Type)
          → {ab : A ⊑ B } → {cb : C ⊑ B} → Cast (A ⇒ C)
    error : (A : Type) → (B : Type) → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc
  
  {-

   OBSOLETE, NEEDS TO BE UPDATED, EVEN LESS LIKE AGT NOW

   The identity casts (at base type) and error casts are active. All
   the other casts are inert. This treatment of identity casts as
   active is a bit different from the AGT paper, but I think it is
   nicer.

   -}

  data Inert : ∀{A} → Cast A → Set where
    inert : ∀{A B C} {ab : A ⊑ B} {cb : C ⊑ B}
          → ¬ (Σ[ ι ∈ Base ] A ≡ ` ι × C ≡ ` ι)
          → A ≢ ⋆
          → Inert ((A ⇒ B ⇒ C){ab}{cb})

  data Active : ∀{A} → Cast A → Set where
    activeId : ∀ {ι : Base}{ab}{cb} → Active (((` ι) ⇒ (` ι) ⇒ (` ι)){ab}{cb})
    activeError : ∀ {A B} → Active (error A B)
    activeA⋆ : ∀{B C}{ab : ⋆ ⊑ B}{cb : C ⊑ B} → Active ((⋆ ⇒ B ⇒ C) {ab}{cb})

  baseAndEq? : (A : Type) → (B : Type) → Dec (Σ[ ι ∈ Base ] A ≡ ` ι × B ≡ ` ι)
  baseAndEq? A B
      with base? A | base? B
  ... | yes ba | no bb = no G
        where G : ¬ Σ Base (λ ι → Σ (A ≡ ` ι) (λ x → B ≡ ` ι))
              G ⟨ fst₁ , ⟨ _ , snd₁ ⟩ ⟩ =
                 contradiction ⟨ fst₁ , snd₁ ⟩ bb
  ... | no ba | _ = no G
        where G : ¬ Σ Base (λ ι → Σ (A ≡ ` ι) (λ x → B ≡ ` ι))
              G ⟨ fst₁ , ⟨ fst₂ , _ ⟩ ⟩ =
                 contradiction ⟨ fst₁ , fst₂ ⟩ ba
  ... | yes ⟨ ι₁ , refl ⟩ | yes ⟨ ι₂ , refl ⟩
      with base-eq? ι₁ ι₂
  ... | yes eq rewrite eq = yes ⟨ ι₂ , ⟨ refl , refl ⟩ ⟩
  ... | no neq = no G
      where G : ¬ Σ Base (λ ι → Σ (A ≡ ` ι) (λ x → B ≡ ` ι))
            G ⟨ fst₁ , ⟨ refl , refl ⟩ ⟩ = neq refl

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert {.(A ⇒ C)} ((A ⇒ B ⇒ C){ab}{cb})
      with baseAndEq? A C
  ... | no nbe
      with eq-unk A
  ... | yes A≡⋆ rewrite A≡⋆ = inj₁ activeA⋆
  ... | no A≢⋆ = inj₂ (inert nbe A≢⋆)
  ActiveOrInert {.(A ⇒ C)} ((A ⇒ B ⇒ C){ab}{cb})
      | yes ⟨ ι , ⟨ A≡ι , C≡ι ⟩ ⟩ rewrite A≡ι | C≡ι
      with ⊑RBase cb
  ... | b=c rewrite b=c = inj₁ activeId
  ActiveOrInert {.(A ⇒ B)} (error A B) = inj₁ activeError

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A₁ A₂ B₁ B₂ C₁ C₂ ab cb}
          → Cross (((A₁ ⇒ A₂) ⇒ (B₁ ⇒ B₂) ⇒ (C₁ ⇒ C₂)){ab}{cb})
    C-pair : ∀{A₁ A₂ B₁ B₂ C₁ C₂ ab cb}
          → Cross (((A₁ `× A₂) ⇒ (B₁ `× B₂) ⇒ (C₁ `× C₂)){ab}{cb})
    C-sum : ∀{A₁ A₂ B₁ B₂ C₁ C₂ ab cb}
          → Cross (((A₁ `⊎ A₂) ⇒ (B₁ `⊎ B₂) ⇒ (C₁ `⊎ C₂)){ab}{cb})

  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ ((A ⇒ B ⇒ (C₁ ⇒ C₂)){ab}{cb}) (inert ¬b ¬⋆) 
      with ⊑R⇒ cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12
      with ⊑L⇒ ab
  ... | inj₁ A≡⋆ = ⊥-elim (¬⋆ A≡⋆)
  ... | inj₂ ⟨ A₁ , ⟨ A₂ , ⟨ A=A₁⇒A₂ , ⟨ A1⊑B1 , A2⊑B2 ⟩ ⟩ ⟩ ⟩ rewrite A=A₁⇒A₂ =
        ⟨ C-fun , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× ((.⋆ ⇒ .(_ `× _) ⇒ .(_ `× _)) {unk⊑} {pair⊑ cb cb₁}) (inert x x₁) =
      ⊥-elim (x₁ refl)
  Inert-Cross× (((A₁ `× A₂) ⇒ (B₁ `× B₂) ⇒ (C₁ `× C₂)) {pair⊑ ab ab₁} {pair⊑ cb cb₁})
      (inert x x₁) =
      ⟨ C-pair , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ ((_ ⇒ _ ⇒ .(_ `⊎ _)) {unk⊑} {sum⊑ cb cb₁}) (inert x x₁) =
      ⊥-elim (x₁ refl)
  Inert-Cross⊎ (((A₁ `⊎ A₂) ⇒ (B₁ `⊎ B₂) ⇒ (C₁ `⊎ C₂)) {sum⊑ ab ab₁} {sum⊑ cb cb₁})
      (inert x x₁) =
      ⟨ C-sum , ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ ⟩

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
  dom (((A₁ ⇒ A₂) ⇒ B ⇒ (C₁ ⇒ C₂)){ab}{cb}) (C-fun)
      with ⊑R⇒ cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12 
      with ab
  ... | fun⊑ ab1 ab2 = (C₁ ⇒ B₁ ⇒ A₁){c1⊑b1}{ab1}

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (((A₁ ⇒ A₂) ⇒ B ⇒ (C₁ ⇒ C₂)){ab}{cb}) (C-fun)
      with ⊑R⇒ cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12 
      with ab
  ... | fun⊑ ab1 ab2 = (A₂ ⇒ B₂ ⇒ C₂){ab2}{c2⊑b2}

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (((A₁ `× A₂) ⇒ B ⇒ (C₁ `× C₂)){ab}{cb}) (C-pair)
      with ⊑R× cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12 
      with ab
  ... | pair⊑ ab1 ab2 = (A₁ ⇒ B₁ ⇒ C₁){ab1}{c1⊑b1}

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (((A₁ `× A₂) ⇒ B ⇒ (C₁ `× C₂)){ab}{cb}) (C-pair)
      with ⊑R× cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12 
      with ab
  ... | pair⊑ ab1 ab2 = (A₂ ⇒ B₂ ⇒ C₂){ab2}{c2⊑b2}

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (((A₁ `⊎ A₂) ⇒ B ⇒ (C₁ `⊎ C₂)){ab}{cb}) (C-sum)
      with ⊑R⊎ cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12 
      with ab
  ... | sum⊑ ab1 ab2 = (A₁ ⇒ B₁ ⇒ C₁){ab1}{c1⊑b1}

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (((A₁ `⊎ A₂) ⇒ B ⇒ (C₁ `⊎ C₂)){ab}{cb}) (C-sum)
      with ⊑R⊎ cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12 
      with ab
  ... | sum⊑ ab1 ab2 = (A₂ ⇒ B₂ ⇒ C₂){ab2}{c2⊑b2}

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert ((A ⇒ B ⇒ (` ι)) {ab} {cb}) (inert x A≢⋆)
      with ⊑RBase cb
  ... | b≡c rewrite b≡c
      with ⊑LBase ab
  ... | inj₁ eq rewrite eq = x ⟨ ι , ⟨ refl , refl ⟩ ⟩
  ... | inj₂ eq⋆ = contradiction eq⋆ A≢⋆

{-  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → A ≢ ⋆ → ¬ Inert c
  baseNotInert ((A ⇒ B ⇒ (` ι)){ab}{cb}) A≢⋆ (inert p)
      with ⊑RBase cb
  ... | b≡c rewrite b≡c
      with ⊑LBase ab
  ... | inj₁ eq rewrite eq = ⟨ ι , ⟨ refl , refl ⟩ ⟩
  ... | inj₂ eq⋆ = contradiction eq⋆ A≢⋆
  baseNotInert (error A B) A⋆ = λ ()
-}

  open import PreCastStructure
  
  pcs : PreCastStruct
  pcs = record
             { Cast = Cast
             ; Inert = Inert
             ; Active = Active
             ; ActiveOrInert = ActiveOrInert
             ; Cross = Cross
             ; Inert-Cross⇒ = Inert-Cross⇒
             ; Inert-Cross× = Inert-Cross×
             ; Inert-Cross⊎ = Inert-Cross⊎
             ; dom = dom
             ; cod = cod
             ; fstC = fstC
             ; sndC = sndC
             ; inlC = inlC
             ; inrC = inrC
             ; baseNotInert = baseNotInert
             }

  import EfficientParamCastAux
  open EfficientParamCastAux pcs

  compose : ∀{A B C} → Cast (A ⇒ B) → Cast (B ⇒ C) → Cast (A ⇒ C)
  compose ((A ⇒ B ⇒ C){ab}{cb}) ((C ⇒ B' ⇒ C'){cb'}{c'b'})
      with B `~ B'
  ... | no nc = error A C' 
  ... | yes B~B'
      with (B `⊔ B') {B~B'}
  ... | ⟨ B⊔B' , ⟨ ⟨ B⊑B⊔B' , B'⊑B⊔B' ⟩ , lb ⟩ ⟩ =
         (A ⇒ B⊔B' ⇒ C'){Trans⊑ ab B⊑B⊔B'}{Trans⊑ c'b' B'⊑B⊔B'}
  compose (A ⇒ B ⇒ C) (error C C') = (error A C')
  compose (error A B) (error B C) = (error A C)
  compose (error A B) (B ⇒ B' ⇒ C) = (error A C)

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v .(_ ⇒ _ ⇒ _) {activeId} = M
  applyCast M (EfficientParamCastAux.S-val x) .(⋆ ⇒ _ ⇒ _) {activeA⋆} =
    ⊥-elim (simple⋆ M x refl)
  applyCast (M ⟨ c ⟩) (V-cast {i = inert x A≢⋆} sv) d {activeA⋆} = M ⟨ compose c d ⟩
  applyCast M v (error _ _) {activeError} = blame (pos zero)
  
  height : ∀{A B} → (c : Cast (A ⇒ B)) → ℕ
  height (_ ⇒ B ⇒ _) = height-t B
  height (error _ _) = 0

  height-lb : ∀{BB' B B' : Type}
     → (∀ {C' : Type} → Σ (B ⊑ C') (λ x → B' ⊑ C') → BB' ⊑ C')
     → B ~ B'
     → height-t BB' ≤ height-t B ∨ height-t B'
  height-lb {⋆} {B} {B'} lb B~B' = z≤n
  height-lb {` x} {B} {B'} lb B~B' = z≤n
  height-lb {BB' ⇒ BB''} {B} {B'} lb B~B' = {!!}
  height-lb {BB' `× BB''} {B} {B'} lb B~B' = {!!}
  height-lb {BB' `⊎ BB''} {B} {B'} lb B~B' = {!!}

  compose-height : ∀ {A B C} → (s : Cast (A ⇒ B)) (t : Cast (B ⇒ C))
     → height (compose s t) ≤ (height s) ∨ (height t)
  compose-height (_ ⇒ B ⇒ _) (_ ⇒ B' ⇒ _)
      with B `~ B'
  ... | no nc = z≤n
  ... | yes B~B'
      with (B `⊔ B') {B~B'}
  ... | ⟨ B⊔B' , ⟨ ⟨ B⊑B⊔B' , B'⊑B⊔B' ⟩ , lb ⟩ ⟩ =
      {!!}
  compose-height (_ ⇒ B ⇒ _) (error _ _) = z≤n
  compose-height (error _ _) (_ ⇒ B ⇒ _) = z≤n
  compose-height (error _ _) (error _ _) = z≤n

  applyCastOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}{a}
          → n ∣ false ⊢ M ok → (v : Value M)
          → Σ[ m ∈ ℕ ] m ∣ false ⊢ applyCast M v c {a} ok × m ≤ 2 + n
  applyCastOK {M = M}{c}{n}{a} Mok v = {!!}
     
  open import CastStructure

  ecs : EfficientCastStruct
  ecs = record
             { precast = pcs
             ; applyCast = applyCast
             ; compose = compose
             ; height = height
             ; compose-height = compose-height
             ; applyCastOK = applyCastOK
             }
             
  open EfficientCastStruct ecs using (c-height)
  import EfficientParamCasts
  open EfficientParamCasts ecs public

  applyCast-height : ∀{Γ}{A B}{V}{v : Value {Γ} V}{c : Cast (A ⇒ B)}
        {a : Active c}
      → c-height (applyCast V v c {a}) ≤ c-height V ∨ height c
  applyCast-height {V = V}{v}{c}{a} = {!!}

  dom-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}{x : Cross c}
       → height (dom c x) ≤ height c
  dom-height {c = c} {x} = {!!}
  
  cod-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}{x : Cross c}
       → height (cod c x) ≤ height c
  cod-height {c = c} {x} = {!!}
  
  fst-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}{x : Cross c}
       → height (fstC c x) ≤ height c
  fst-height {c = c}{x} = {!!}
  
  snd-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}{x : Cross c}
       → height (sndC c x) ≤ height c
  snd-height {c = c}{x} = {!!}
  
  inlC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}{x : Cross c}
       → height (inlC c x) ≤ height c
  inlC-height {c = c}{x} = {!!}
  
  inrC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}{x : Cross c}
       → height (inrC c x) ≤ height c
  inrC-height {c = c}{x} = {!!}
  

  ecsh : EfficientCastStructHeight
  ecsh = record
              { effcast = ecs
              ; applyCast-height = (λ {Γ}{A}{B}{V}{v}{c}{a} → applyCast-height{Γ}{A}{B}{V}{v}{c}{a})
              ; dom-height = (λ {A}{B}{C}{D}{c}{x} → dom-height{A}{B}{C}{D}{c}{x})
              ; cod-height = (λ {A}{B}{C}{D}{c}{x} → cod-height{A}{B}{C}{D}{c}{x})
              ; fst-height = (λ {A}{B}{C}{D}{c}{x} → fst-height{A}{B}{C}{D}{c}{x})
              ; snd-height = (λ {A}{B}{C}{D}{c}{x} → snd-height{A}{B}{C}{D}{c}{x})
              ; inlC-height = (λ {A}{B}{C}{D}{c}{x} → inlC-height{A}{B}{C}{D}{c}{x})
              ; inrC-height = (λ {A}{B}{C}{D}{c}{x} → inrC-height{A}{B}{C}{D}{c}{x})
              }

  import PreserveHeight
  module PH = PreserveHeight ecsh

  preserve-height : ∀ {Γ A} {M M′ : Γ ⊢ A} {ctx : ReductionCtx}
       → ctx / M —→ M′ → c-height M′ ≤ c-height M
  preserve-height M—→M′ = PH.preserve-height M—→M′


  import SpaceEfficient
  module SE = SpaceEfficient ecs

  preserve-ok : ∀{Γ A}{M M′ : Γ ⊢ A}{ctx : ReductionCtx}{n}
          → n ∣ false ⊢ M ok  →  ctx / M —→ M′
          → Σ[ m ∈ ℕ ] m ∣ false ⊢ M′ ok × m ≤ 2 + n
  preserve-ok Mok M—→M′ = SE.preserve-ok Mok M—→M′

  module EC = SE.EfficientCompile {!!}

  open import GTLC
  import GTLC2CC
  module Compile = GTLC2CC Cast {!!}

  compile-efficient : ∀{Γ A} (M : Term) (d : Γ ⊢G M ⦂ A) (ul : Bool)
      → Σ[ k ∈ ℕ ] k ∣ ul ⊢ (Compile.compile M d) ok × k ≤ 1
  compile-efficient d ul = EC.compile-efficient d ul
  
  {-

   Alternative idea about evidence.  Use consistency judgements!
   Here's the definition consitentent transitivity.

  -}

  _∘_ : ∀{A B C} → (c : A ~ B) → (d : B ~ C) → Dec (A ~ C)
  unk~L ∘ d = yes unk~L
  _∘_ {A}{⋆}{C} unk~R unk~L = A `~ C
  unk~R ∘ unk~R = yes unk~R
  base~ ∘ d = yes d
  fun~ c₁ d₁ ∘ unk~R = yes unk~R
  fun~ c₁ d₁ ∘ fun~ c₂ d₂
      with c₂ ∘ c₁ | d₁ ∘ d₂
  ... | yes c | yes d = yes (fun~ c d)
  ... | yes c | no d = no (¬~fR d)
  ... | no c | _ = no (¬~fL λ x → c (Sym~ x))
  pair~ c₁ d₁ ∘ unk~R = yes unk~R
  pair~ c₁ d₁ ∘ pair~ c₂ d₂
      with c₁ ∘ c₂ | d₁ ∘ d₂
  ... | yes c | yes d = yes (pair~ c d)
  ... | yes c | no d = no (¬~pR d)
  ... | no c | _ = no (¬~pL c)
  sum~ c₁ d₁ ∘ unk~R = yes unk~R
  sum~ c₁ d₁ ∘ sum~ c₂ d₂
      with c₁ ∘ c₂ | d₁ ∘ d₂
  ... | yes c | yes d = yes (sum~ c d)
  ... | yes c | no d = no (¬~sR d)
  ... | no c | _ = no (¬~sL c)

