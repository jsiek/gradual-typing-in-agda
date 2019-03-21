module AGT where

  open import Agda.Primitive renaming (_⊔_ to _⊍_)
  open import Types
  open import Labels
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Nat using (ℕ; zero; suc)
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
    cons (c-fun c1 c3) (c-fun c2 c4)
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
      fun~ (ceq-implies-cons (cons as bs)) (ceq-implies-cons (cons as₁ bs₁))
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
    abs-any : ∀{P : SType → Set} {S T : SType}
      → ¬ (S ⌢ T)
      → P S → P T
        ---------------
      → Abs P ⋆

{-
  dom-dom : ∀ {P P' : SType → Set} {T T' : SType}
    → Dom P P'  →  P (T ⇒ T')
      -----------------------
    → P' T
  dom-dom (dom f g) p-tt' = g p-tt'

  cod-cod : ∀ {P P' : SType → Set} {T T' : SType}
    → Cod P P'  →  P (T ⇒ T')
      -----------------------
    → P' T'
  cod-cod (cod f g) p-tt' = g p-tt'

  dom-fun : ∀{P P' : SType → Set} {T : SType}
          → Dom P P'   →   P' T
          → Σ[ T' ∈ SType ] P (T ⇒ T')
  dom-fun (dom x x₁) p't = x p't

  cod-fun : ∀{P P' : SType → Set} {T : SType}
          → Cod P P'   →   P' T
          → Σ[ T' ∈ SType ] P (T' ⇒ T)
  cod-fun (cod x x₁) p't = x p't
-}

  abs-non-empty : ∀{P : SType → Set}{A : Type} → Abs P A → Σ[ T ∈ SType ] P T
  abs-non-empty {P} {` ι} (abs-base x x₁) = ⟨ ` ι , x ⟩
  abs-non-empty {P} {⋆} (abs-any{T = T} x x₁ x₂) = ⟨ T , x₂ ⟩
  abs-non-empty {P} {_} (abs-fun x abs₁ abs₂)
      with abs-non-empty abs₁
  ... | ⟨ T₁ , in-dom {T₂ = T₂'} PT₁T₂' ⟩ =
        ⟨ (T₁ ⇒ T₂') , PT₁T₂' ⟩

  _⊆_ : (SType → Set) → (SType → Set) → Set
  P ⊆ P' = ∀{T : SType} → P T → P' T

  _⇔_ : (SType → Set) → (SType → Set) → Set
  P ⇔ P' = P ⊆ P' × P' ⊆ P

  dom-subset : ∀{P Q : SType → Set}
          →  P ⊆ Q
            -------------
          → Dom P ⊆ Dom Q
  dom-subset pq (in-dom x) = in-dom (pq x)

  cod-subset : ∀{P Q : SType → Set}
          →  P ⊆ Q
            -------------
          → Cod P ⊆ Cod Q
  cod-subset pq (in-cod x) = in-cod (pq x)

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
  abs-optimal ⟨ T , pt ⟩ p-ca (abs-any a b c )
      with conc-sh-cons (p-ca b) (p-ca c) 
  ... | inj₁ A≡⋆ rewrite A≡⋆ = 
        unk⊑
  ... | inj₂ x = 
        contradiction x a

{-

  all-funs-conc : ∀{A} → AllFuns (Conc A)
          → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  all-funs-conc {⋆} (funs f)
      with f {` Nat} c-unk
  ... | ⟨ T₁ , ⟨ T₂ , () ⟩ ⟩ 
  all-funs-conc {` ι} (funs f)
      with f {` ι} c-base
  ... | ⟨ T₁ , ⟨ T₂ , () ⟩ ⟩ 
  all-funs-conc {A₁ ⇒ A₂} af = ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩
  all-funs-conc {A₁ `× A₂} (funs f)
      with conc A₁ | conc A₂
  ... | ⟨ T₁ , cat1 ⟩ | ⟨ T₂ , cat2 ⟩ 
      with f {T₁ `× T₂} (c-pair cat1 cat2)
  ... | ⟨ T₁' , ⟨ T₂' , () ⟩ ⟩
  all-funs-conc {A₁ `⊎ A₂} (funs f)
      with conc A₁ | conc A₂
  ... | ⟨ T₁ , cat1 ⟩ | ⟨ T₂ , cat2 ⟩ 
      with f {T₁ `⊎ T₂} (c-sum cat1 cat2)
  ... | ⟨ T₁' , ⟨ T₂' , () ⟩ ⟩
-}  

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

  {- todo : prove L= and R= are equivalent -}
  {- todo : delete R=→cc and cc→R= -}

  R=→cc : ∀{G₁ G₂ T} → R STypeEq G₁ G₂ T → Conc G₁ T × Conc G₂ T
  R=→cc (rightp x x₁ (stype-eq refl)) = ⟨ x , x₁ ⟩

  cc→R= : ∀{G₁ G₂ T} → Conc G₁ T → Conc G₂ T → R STypeEq G₁ G₂ T
  cc→R= g1t g2t = rightp g1t g2t (stype-eq refl)

  cct-consis : ∀{G1 G2 T} → Conc G1 T → Conc G2 T → G1 ~ G2
  cct-consis c-base c-base = base~
  cct-consis c-base c-unk = unk~R
  cct-consis (c-fun c1t c1t₁) (c-fun c2t c2t₁) =
      fun~ (cct-consis c1t c2t) (cct-consis c1t₁ c2t₁)
  cct-consis (c-fun c1t c1t₁) c-unk = unk~R
  cct-consis (c-pair c1t c1t₁) (c-pair c2t c2t₁) =
      pair~ (cct-consis c1t c2t) (cct-consis c1t₁ c2t₁)
  cct-consis (c-pair c1t c1t₁) c-unk = unk~R
  cct-consis (c-sum c1t c1t₁) (c-sum c2t c2t₁) =
      sum~ (cct-consis c1t c2t) (cct-consis c1t₁ c2t₁)
  cct-consis (c-sum c1t c1t₁) c-unk = unk~R
  cct-consis c-unk c2t = unk~L

  cct-c⊔ : ∀{G1 G2 T} → (c1 : Conc G1 T) → (c2 : Conc G2 T)
           → Conc ((G1 ⊔ G2){cct-consis c1 c2}) T
  cct-c⊔ c-base c-base = c-base
  cct-c⊔ c-base c-unk = c-base
  cct-c⊔ (c-fun c1t c1t₁) (c-fun c2t c2t₁) =
      c-fun (cct-c⊔ c1t c2t) (cct-c⊔ c1t₁ c2t₁)
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
  c⊔-cct {A₁ ⇒ A₂} {B₁ ⇒ B₂} {T₁ ⇒ T₂} {fun~ c c₁} (c-fun ct ct₁) =
    ⟨ (c-fun (proj₁ (c⊔-cct {A₁}{B₁}{T₁}{c} ct))
             (proj₁ (c⊔-cct{A₂}{B₂}{T₂}{c₁} ct₁))) ,
      (c-fun (proj₂ (c⊔-cct {A₁}{B₁}{T₁}{c} ct))
             (proj₂ (c⊔-cct{A₂}{B₂}{T₂}{c₁} ct₁))) ⟩
  c⊔-cct {A₁ `× A₂} {B₁ `× B₂} {T₁ `× T₂} {pair~ c c₁} (c-pair ct ct₁) = 
    ⟨ (c-pair (proj₁ (c⊔-cct {A₁}{B₁}{T₁}{c} ct))
             (proj₁ (c⊔-cct{A₂}{B₂}{T₂}{c₁} ct₁))) ,
      (c-pair (proj₂ (c⊔-cct {A₁}{B₁}{T₁}{c} ct))
             (proj₂ (c⊔-cct{A₂}{B₂}{T₂}{c₁} ct₁))) ⟩
  c⊔-cct {A₁ `⊎ A₂} {B₁ `⊎ B₂} {T₁ `⊎ T₂} {sum~ c c₁} (c-sum ct ct₁) =
    ⟨ (c-sum (proj₁ (c⊔-cct {A₁}{B₁}{T₁}{c} ct))
             (proj₁ (c⊔-cct{A₂}{B₂}{T₂}{c₁} ct₁))) ,
      (c-sum (proj₂ (c⊔-cct {A₁}{B₁}{T₁}{c} ct))
             (proj₂ (c⊔-cct{A₂}{B₂}{T₂}{c₁} ct₁))) ⟩

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

  {- 

   todo : prove L=(G1,G2) ⇔ γ(G₁ ⊔ G₂)

   use prop-17 and L=→cc

  -}






  STypeEq⇒ : ∀ {T₁ T₂ T₃ T₄ : SType}
           → STypeEq T₁ T₃ → STypeEq T₂ T₄
           → STypeEq (T₁ ⇒ T₂) (T₃ ⇒ T₄)
  STypeEq⇒ (stype-eq refl) (stype-eq refl) = stype-eq refl

  dom&cod-L= : Type → Type → Type → Type → SType → Set
  dom&cod-L= G₁₁ G₁₂ G₂₁ G₂₂ T =
    Σ[ T₁ ∈ SType ] Σ[ T₂ ∈ SType ]
      T ≡ T₁ ⇒ T₂ × L STypeEq G₁₁ G₂₁ T₁ × L STypeEq G₁₂ G₂₂ T₂

  dom→L= : ∀{G₁₁ G₁₂ G₂₁ G₂₂ T}
         → Dom (L STypeEq (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂)) T
         → L STypeEq G₁₁ G₂₁ T
  dom→L= (in-dom (leftp (c-fun x x₃) (c-fun x₁ x₄) (stype-eq refl))) =
      leftp x x₁ (stype-eq refl)

  L=→dom : ∀{G₁₁ G₁₂ G₂₁ G₂₂ T}
         → L STypeEq G₁₁ G₂₁ T → L STypeEq G₁₂ G₂₂ T
         → Dom (L STypeEq (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂)) T
  L=→dom l1 l2 = in-dom (L⇒-intro STypeEq⇒ l1 l2)

  cod→L= : ∀{G₁₁ G₁₂ G₂₁ G₂₂ T}
         → Cod (L STypeEq (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂)) T
         → L STypeEq G₁₂ G₂₂ T
  cod→L= (in-cod (leftp (c-fun x x₃) (c-fun x₁ x₄) (stype-eq refl))) =
      leftp x₃ x₄ (stype-eq refl)

  L=→cod : ∀{G₁₁ G₁₂ G₂₁ G₂₂ T}
         → L STypeEq G₁₁ G₂₁ T → L STypeEq G₁₂ G₂₂ T
         → Cod (L STypeEq (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂)) T
  L=→cod l1 l2 = in-cod (L⇒-intro STypeEq⇒ l1 l2)

  dom&cod-L=→L=⇒ : ∀ {G₁₁ G₁₂ G₂₁ G₂₂ : Type}{T : SType}
          → dom&cod-L= G₁₁ G₁₂ G₂₁ G₂₂ T
          → L STypeEq (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂) T
  dom&cod-L=→L=⇒ {T = T} ⟨ T₁ , ⟨ T₂ , ⟨ eq , ⟨ fst₁ , snd ⟩ ⟩ ⟩ ⟩
      rewrite eq = L⇒-intro STypeEq⇒ fst₁ snd

  L=⇒→dom&cod-L= : ∀ {G₁₁ G₁₂ G₂₁ G₂₂ : Type}{T : SType}
          → L STypeEq (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂) T
          → dom&cod-L= G₁₁ G₁₂ G₂₁ G₂₂ T
  L=⇒→dom&cod-L= (leftp (c-fun{S₁ = S₁}{S₂ = S₂} x x₄) (c-fun x₁ x₃) (stype-eq refl)) =
    ⟨ S₁ , ⟨ S₂ , ⟨ refl , ⟨ (cc→L= x x₁) , (cc→L= x₄ x₃) ⟩ ⟩ ⟩ ⟩
  

  dom&cod-L=⇔L=⇒ : ∀ {G₁₁ G₁₂ G₂₁ G₂₂}
          → L STypeEq (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂) ⇔ dom&cod-L= G₁₁ G₁₂ G₂₁ G₂₂
  dom&cod-L=⇔L=⇒ = ⟨ L=⇒→dom&cod-L= , dom&cod-L=→L=⇒ ⟩

  abs-L=⇒L : ∀{G₁₁ G₁₂ G₂₁ G₂₂ A B}
          → Abs (L STypeEq (G₁₁ ⇒ G₁₂) (G₂₁ ⇒ G₂₂)) (A ⇒ B)
          → Abs (L STypeEq G₁₁ G₂₁) A
  abs-L=⇒L{A = A}{B = B} (abs-fun x abs₁ abs₂) =
     {!!}



  abs-L=→lub : ∀{G₁ G₂ G₃} → Abs (L STypeEq G₁ G₂) G₃ → lub G₃ G₁ G₂
  abs-L=→lub {G₁}{G₂} (abs-base{ι = ι} p-i all-i)
      with L=→cc p-i
  ... | ⟨ g1i , g2i ⟩ = ⟨ ⟨ conc-prec g1i , conc-prec g2i ⟩ , G ⟩
      where G : {C' : Type} → Σ (G₁ ⊑ C') (λ x → G₂ ⊑ C') → ` ι ⊑ C'
            G {C'} ⟨ G₁⊑C' , G₂⊑C' ⟩
                with c-any-base g1i | c-any-base g2i
            ... | inj₁ G₁≡ι | _ rewrite G₁≡ι
                with G₁⊑C'
            ... | base⊑ = base⊑
            G {C'} ⟨ G₁⊑C' , G₂⊑C' ⟩ | inj₂ G₁≡⋆ | inj₁ G₂≡ι rewrite G₂≡ι
                with G₂⊑C'
            ... | base⊑ = base⊑
            G {C'} ⟨ G₁⊑C' , G₂⊑C' ⟩ | inj₂ G₁≡⋆ | inj₂ G₂≡⋆ rewrite G₁≡⋆ | G₂≡⋆
                with all-i {` ι `× ` ι} (L=⋆⋆ {` ι `× ` ι})
            ... | ()
  abs-L=→lub {G₁}{G₂} (abs-any{S = S}{T = T} ¬S⌢T S∈L=G₁G₂ T∈L=G₁G₂)
      with L=→cc S∈L=G₁G₂ | L=→cc T∈L=G₁G₂
  ... | ⟨ c-g1s , c-g2s ⟩ | ⟨ c-g1t , c-g2t ⟩
      with conc-sh-cons c-g1s c-g1t
  ... | inj₂ S⌢T = contradiction S⌢T ¬S⌢T
  ... | inj₁ G₁≡⋆ rewrite G₁≡⋆
      with conc-sh-cons c-g2s c-g2t
  ... | inj₂ S⌢T = contradiction S⌢T ¬S⌢T
  ... | inj₁ G₂≡⋆ rewrite G₂≡⋆ = ⟨ ⟨ unk⊑ , unk⊑ ⟩ , (λ x → unk⊑) ⟩
  abs-L=→lub {G₁}{G₂} (abs-fun{A = A}{B = B} (funs all-f) abs-p1 abs-p2)
      with abs-non-empty abs-p1
  ... | ⟨ T₁ , in-dom {T₂ = T₂} T₁⇒T₂∈L=G₁G₂ ⟩
      with L=→cc T₁⇒T₂∈L=G₁G₂
  ... | ⟨ T₁⇒T₂∈γG₁ , T₁⇒T₂∈γG₂ ⟩

      with c-any-fun T₁⇒T₂∈γG₁ | c-any-fun T₁⇒T₂∈γG₂
  ... | inj₁ ⟨ G₁₁ , ⟨ G₁₂ , ⟨ G₁≡G₁₁⇒G₁₂ , ⟨ cg11 , cg12 ⟩ ⟩ ⟩ ⟩
      | inj₁ ⟨ G₂₁ , ⟨ G₂₂ , ⟨ G₂≡G₂₁⇒G₂₂ , ⟨ cg21 , cg22 ⟩ ⟩ ⟩ ⟩
      rewrite G₁≡G₁₁⇒G₁₂ | G₂≡G₂₁⇒G₂₂ =
        let A⇒B∈αLG12 = abs-fun all-funs-L= abs-p1 abs-p2 in
        let ih1 : lub A G₁₁ G₂₁
            ih1 = abs-L=→lub {!!} in
        let ih2 : lub B G₁₂ G₂₂
            ih2 = abs-L=→lub {!!} in
       ⟨ ⟨ (fun⊑ (proj₁ (proj₁ ih1)) (proj₁ (proj₁ ih2))) ,
           (fun⊑ (proj₂ (proj₁ ih1)) (proj₂ (proj₁ ih2))) ⟩ , (G ih1 ih2) ⟩
      where
      G : {C' : Type} → lub A G₁₁ G₂₁ → lub B G₁₂ G₂₂ →
          Σ (G₁₁ ⇒ G₁₂ ⊑ C') (λ x → G₂₁ ⇒ G₂₂ ⊑ C') → A ⇒ B ⊑ C'
      G {C₁ ⇒ C₂} ih1 ih2 ⟨ fun⊑ G₁₁⊑C₁ G₁₂⊑C₂ , fun⊑ G₂₁⊑C₁ G₂₁⊑C₂ ⟩ =
          fun⊑ (proj₂ ih1 ⟨ G₁₁⊑C₁ , G₂₁⊑C₁ ⟩) (proj₂ ih2 ⟨ G₁₂⊑C₂ , G₂₁⊑C₂ ⟩)

  abs-L=→lub {G₁}{G₂} (abs-fun{A = A}{B = B} (funs all-f) abs-p1 abs-p2)
      | ⟨ T₁ , in-dom {T₂ = T₂} T₁⇒T₂∈L=G₁G₂ ⟩
      | ⟨ T₁⇒T₂∈γG₁ , T₁⇒T₂∈γG₂ ⟩
      | inj₁ ⟨ G₁₁ , ⟨ G₁₂ , ⟨ G₁≡G₁₁⇒G₁₂ , ⟨ cg11 , cg12 ⟩ ⟩ ⟩ ⟩
      | inj₂ G₂≡⋆
      rewrite G₁≡G₁₁⇒G₁₂ | G₂≡⋆ =

        ⟨ ⟨ {!!} , unk⊑ ⟩ , {!!} ⟩

  ... | inj₂ G₁≡⋆
      | inj₁ ⟨ G₂₁ , ⟨ G₂₂ , ⟨ G₂≡G₂₁⇒G₂₂ , ⟨ cg21 , cg22 ⟩ ⟩ ⟩ ⟩
      rewrite G₁≡⋆ | G₂≡G₂₁⇒G₂₂ =

        {!!}

  ... | inj₂ G₁≡⋆ | inj₂ G₂≡⋆ rewrite G₁≡⋆ | G₂≡⋆
      with all-f {` Nat} (L=⋆⋆ {` Nat})
  ... | ()

{-
      with abs-non-empty abs-p1
  ... | ⟨ T₁ , P₁T₁ ⟩
      with dom-fun dm P₁T₁
  ... | ⟨ T₂ , PT₁T₂ ⟩ 
      with L=→cc PT₁T₂
  ... | ⟨ cg1t12 , cg2t12 ⟩ 
      with c-any-fun cg1t12 | c-any-fun cg2t12
  ... | inj₁ ⟨ G₁₁ , ⟨ G₁₂ , ⟨ G₁≡G₁₁⇒G₁₂ , ⟨ cg11 , cg12 ⟩ ⟩ ⟩ ⟩
      | inj₁ ⟨ G₂₁ , ⟨ G₂₂ , ⟨ G₂≡G₂₁⇒G₂₂ , ⟨ cg21 , cg22 ⟩ ⟩ ⟩ ⟩
      rewrite G₁≡G₁₁⇒G₁₂ | G₂≡G₂₁⇒G₂₂ =
        let ih1 : lub A G₁₁ G₂₁
            ih1 = abs-L=→lub {!!} in
        let ih2 : lub B G₁₂ G₂₂
            ih2 = abs-L=→lub {!!} in
        
        {!!}
        
  abs-L=→lub (abs-fun (funs all-f) dm abs-p1 cd abs-p2)
      | ⟨ T₁ , P₁T₁ ⟩ | ⟨ T₂ , PT₁T₂ ⟩ | ⟨ cg1t12 , cg2t12 ⟩ 
      | inj₁ ⟨ G₁₁ , ⟨ G₁₂ , ⟨ G₁≡G₁₁⇒G₁₂ , ⟨ cg11 , cg12 ⟩ ⟩ ⟩ ⟩
      | inj₂ G₂≡⋆
      rewrite G₁≡G₁₁⇒G₁₂ | G₂≡⋆ =

        ⟨ ⟨ {!!} , unk⊑ ⟩ , {!!} ⟩

  abs-L=→lub (abs-fun (funs all-f) dm abs-p1 cd abs-p2)
      | ⟨ T₁ , P₁T₁ ⟩ | ⟨ T₂ , PT₁T₂ ⟩ | ⟨ cg1t12 , cg2t12 ⟩ 
      | inj₂ G₁≡⋆
      | inj₁ ⟨ G₂₁ , ⟨ G₂₂ , ⟨ G₂≡G₂₁⇒G₂₂ , ⟨ cg21 , cg22 ⟩ ⟩ ⟩ ⟩
      rewrite G₁≡⋆ | G₂≡G₂₁⇒G₂₂ =

        {!!}
        
  abs-L=→lub (abs-fun (funs all-f) dm abs-p1 cd abs-p2)
      | ⟨ T₁ , P₁T₁ ⟩ | ⟨ T₂ , PT₁T₂ ⟩ | ⟨ cg1t12 , cg2t12 ⟩ 
      | inj₂ G₁≡⋆ | inj₂ G₂≡⋆ rewrite G₁≡⋆ | G₂≡⋆
      with all-f {` Nat} (L=⋆⋆ {` Nat})
  ... | ()
-}
{-
... | inj₂ G₁≡⋆
      rewrite G₁≡⋆
      with L=⋆G→conc PT₁T₂
  ... | ConcG₂T₁⇒T₂
      with c-any-fun ConcG₂T₁⇒T₂
  ... | inj₁ ⟨ G₂₁ , ⟨ G₂₂ , ⟨ G₂≡G₂₁⇒G₂₂ , ⟨ cg21 , cg22 ⟩ ⟩ ⟩ ⟩
      rewrite G₂≡G₂₁⇒G₂₂ =
        ⟨ ⟨ unk⊑ , fun⊑ (abs-optimal ⟨ T₁ , P₁T₁ ⟩ {!!} abs-p1)
                        (abs-optimal ⟨ T₂ , {!!} ⟩ {!!} abs-p2) ⟩ ,
                   (λ x → {!!}) ⟩
  ... | inj₂ G₂≡⋆ rewrite G₂≡⋆ with all-f {` Nat} (L=⋆⋆ {` Nat})
  ... | ()
-}


{-
  prop-16 : ∀ {G₁ G₂} → (c : G₁ ~ G₂) → I= G₁ G₂ ((G₁ ⊔ G₂){c}) ((G₁ ⊔ G₂){c})
  prop-16 unk~L = {!!}
  prop-16 unk~R = {!!}
  prop-16 (base~ {ι}) = inter (abs2 (proj-1 {!!} {!!}) (abs-base {!!})
                                    (proj-2 {!!} {!!}) (abs-base {!!}))
  prop-16 (fun~ c c₁) = {!!}
  prop-16 (pair~ c c₁) = {!!}
  prop-16 (sum~ c c₁) = {!!}
-}


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

   The identity casts (at base type) and error casts are active. All
   the other casts are inert. This treatment of identity casts as
   active is a bit different from the AGT paper, but I think it is
   nicer.

   -}

  data Inert : ∀{A} → Cast A → Set where
    inert : ∀{A B C} {ab : A ⊑ B} {cb : C ⊑ B}
          → ¬ (Σ[ ι ∈ Base ] A ≡ ` ι × C ≡ ` ι)
          → Inert ((A ⇒ B ⇒ C){ab}{cb})

  data Active : ∀{A} → Cast A → Set where
    activeId : ∀ {ι : Base}{ab}{cb} → Active (((` ι) ⇒ (` ι) ⇒ (` ι)){ab}{cb})
    activeError : ∀ {A B} → Active (error A B)


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
  ... | no nbe = inj₂ (inert nbe)
  ... | yes ⟨ ι , ⟨ A≡ι , C≡ι ⟩ ⟩ rewrite A≡ι | C≡ι
      with ⊑RBase cb
  ... | b=c rewrite b=c = inj₁ activeId
  ActiveOrInert {.(A ⇒ B)} (error A B) = inj₁ activeError

  import EfficientParamCasts
  module EPCR = EfficientParamCasts Cast Inert Active ActiveOrInert
  open EPCR
  
  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v .(_ ⇒ _ ⇒ _) {activeId} = M
  applyCast M v (error _ _) {activeError} = blame (pos zero)

  funCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
          → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M v ((A ⇒ B ⇒ (C₁ ⇒ C₂)){ab}{cb}) {inert _} N
      with ⊑R⇒ cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12
      with ⊑L⇒ ab
  ... | inj₁ A≡⋆ = contradiction A≡⋆ (simple⋆ M v)
  ... | inj₂ ⟨ A₁ , ⟨ A₂ , ⟨ A=A₁⇒A₂ , ⟨ A1⊑B1 , A2⊑B2 ⟩ ⟩ ⟩ ⟩ rewrite A=A₁⇒A₂ =
     (M · (N ⟨ (C₁ ⇒ B₁ ⇒ A₁){c1⊑b1}{A1⊑B1} ⟩))
             ⟨ (A₂ ⇒ B₂ ⇒ C₂){A2⊑B2}{c2⊑b2} ⟩
             
  fstCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
            → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M v ((A ⇒ B ⇒ (C₁ `× C₂)){ab}{cb}) {inert _}
      with ⊑R× cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12
      with ⊑L× ab
  ... | inj₁ A≡⋆ = contradiction A≡⋆ (simple⋆ M v)
  ... | inj₂ ⟨ A₁ , ⟨ A₂ , ⟨ A=A₁×A₂ , ⟨ A1⊑B1 , A2⊑B2 ⟩ ⟩ ⟩ ⟩ rewrite A=A₁×A₂ =
        (fst M) ⟨ (A₁ ⇒ B₁ ⇒ C₁){A1⊑B1}{c1⊑b1} ⟩

  sndCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
            → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M v ((A ⇒ B ⇒ (C₁ `× C₂)){ab}{cb}) {inert _}
      with ⊑R× cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12
      with ⊑L× ab
  ... | inj₁ A≡⋆ = contradiction A≡⋆ (simple⋆ M v)
  ... | inj₂ ⟨ A₁ , ⟨ A₂ , ⟨ A=A₁×A₂ , ⟨ A1⊑B1 , A2⊑B2 ⟩ ⟩ ⟩ ⟩ rewrite A=A₁×A₂ =
        (snd M) ⟨ (A₂ ⇒ B₂ ⇒ C₂){A2⊑B2}{c2⊑b2} ⟩

  caseCast : ∀ {Γ A A' B' C} → (L : Γ ⊢ A) → SimpleValue L
             → (c : Cast (A ⇒ (A' `⊎ B')))
             → ∀ {i : Inert c} → (Γ ⊢ A' ⇒ C) → (Γ ⊢ B' ⇒ C) → Γ ⊢ C
  caseCast{C = C} L v ((A ⇒ B ⇒ (C₁ `⊎ C₂)){ab}{cb}) {inert _} M N
      with ⊑R⊎ cb
  ... | ⟨ B₁ , ⟨ B₂ , ⟨ b=b12 , ⟨ c1⊑b1 , c2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite b=b12
      with ⊑L⊎ ab
  ... | inj₁ A≡⋆ = contradiction A≡⋆ (simple⋆ L v)
  ... | inj₂ ⟨ A₁ , ⟨ A₂ , ⟨ A=A₁⊎A₂ , ⟨ a1⊑b1 , a2⊑b2 ⟩ ⟩ ⟩ ⟩ rewrite A=A₁⊎A₂ =
      case L (M ⟨ ((C₁ ⇒ C) ⇒ (B₁ ⇒ C) ⇒ (A₁ ⇒ C)){le1}{le2} ⟩)
             (N ⟨ ((C₂ ⇒ C) ⇒ (B₂ ⇒ C) ⇒ (A₂ ⇒ C)){le3}{le4} ⟩)
      where
      le1 = fun⊑ c1⊑b1 Refl⊑
      le2 = fun⊑ a1⊑b1 Refl⊑
      le3 = fun⊑ c2⊑b2 Refl⊑
      le4 = fun⊑ a2⊑b2 Refl⊑

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

  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → A ≢ ⋆ → ¬ Inert c
  baseNotInert ((A ⇒ B ⇒ (` ι)){ab}{cb}) A≢⋆ (inert p)
      with ⊑RBase cb
  ... | b≡c rewrite b≡c
      with ⊑LBase ab
  ... | inj₁ eq rewrite eq = p ⟨ ι , ⟨ refl , refl ⟩ ⟩
  ... | inj₂ eq⋆ = contradiction eq⋆ A≢⋆
  baseNotInert (error A B) A⋆ = λ ()

  module Red = EPCR.Reduction applyCast funCast fstCast sndCast caseCast
                  baseNotInert compose
  open Red


