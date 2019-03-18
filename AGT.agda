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

  {- to do: ceq-implies-cons -}

  {- Abstraction -}

  data AllFuns : (SType → Set) → Set where
    funs : ∀{P}
      → (∀{T : SType} → P T → Σ[ T₁ ∈ SType ] Σ[ T₂ ∈ SType ]
            T ≡ T₁ ⇒ T₂)
        -----------------------------------------------------
      → AllFuns P

  data Dom : (SType → Set) → (SType → Set) → Set where
    dom : ∀{P P₁ : (SType → Set)}
      → (∀{T₁} → P₁ T₁ → Σ[ T₂ ∈ SType ] P (T₁ ⇒ T₂))
      → (∀{T₁ T₂} → P (T₁ ⇒ T₂) → P₁ T₁)
        ---------------------------------------------
      → Dom P P₁

  data Cod : (SType → Set) → (SType → Set) → Set where
    cod : ∀{P P₂}
      → (∀{T₂} → P₂ T₂ → Σ[ T₁ ∈ SType ] P (T₁ ⇒ T₂))
      → (∀{T₁ T₂} → P (T₁ ⇒ T₂) → P₂ T₂)
        ---------------------------------------------
      → Cod P P₂

  data Abs : (SType → Set) → Type → Set₁ where
    abs-base : ∀{P : SType → Set} {ι : Base}
      → (∀{T : SType} → P T → T ≡ ` ι)
        -------------------------------
      → Abs P (` ι)
    abs-fun : ∀{P P₁ P₂ : SType → Set}{A B : Type}
      → AllFuns P
      → Dom P P₁  →   Abs P₁ A
      → Cod P P₂  →   Abs P₂ B
        ----------------------
      → Abs P (A ⇒ B)
    abs-any : ∀{P : SType → Set} {S T : SType}
      → ¬ (S ⌢ T)
      → P S → P T
        ---------------
      → Abs P ⋆

  _⊆_ : (SType → Set) → (SType → Set) → Set
  P ⊆ P' = ∀{T : SType} → P T → P' T


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


  conc-abs-sound : ∀{P : SType → Set}{A : Type}
     → Abs P A  
       ----------
     → P ⊆ Conc A
  conc-abs-sound (abs-base p-base) {T} pt
    rewrite p-base {T} pt = c-base
  conc-abs-sound (abs-fun allfun dom-p abs-a cod-p abs-b) pt
      with allfun
  ... | funs af
      with af pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq =
        let ih1 = conc-abs-sound abs-a in
        let ih2 = conc-abs-sound abs-b in
        c-fun (ih1 (dom-dom dom-p pt)) (ih2 (cod-cod cod-p pt))
  conc-abs-sound (abs-any a b c) pt = c-unk

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
  abs-optimal ⟨ T , pt ⟩ p-ca (abs-base all-base)
      with pt
  ... | pt'
      rewrite all-base pt
      with c-any-base (p-ca pt') 
  ... | inj₁ eq rewrite eq = Refl⊑
  ... | inj₂ eq rewrite eq = unk⊑
  abs-optimal ⟨ T , pt ⟩ p-ca
          (abs-fun{P}{P₁}{P₂}{B₁}{B₂} allf dom-pp1 abs-p1-b1 cod-p-p2 abs-p2-b2)
      with allf
  ... | funs af
      with af pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq
      with dom-pp1
  ... | dom dom-f dom-g 
      with cod-p-p2
  ... | cod cod-f cod-g 
      with c-any-fun (p-ca pt)
  ... | inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ a=a12 , ⟨ c1 , c2 ⟩ ⟩ ⟩ ⟩ rewrite a=a12 =
      let ih1 = abs-optimal ⟨ T₁ , (dom-g pt) ⟩ p1-a1 abs-p1-b1 in
      let ih2 = abs-optimal ⟨ T₂ , (cod-g pt) ⟩ p2-a2 abs-p2-b2 in
      fun⊑ ih1 ih2
      where
      p1-a1 : P₁ ⊆ Conc A₁
      p1-a1 {T} p1t with dom-f p1t
      ... | ⟨ T₂ , p-tt2 ⟩
          with p-ca p-tt2 
      ... | c-fun c1 c2 = c1

      p2-a2 : P₂ ⊆ Conc A₂
      p2-a2 {T} p1t with cod-f p1t
      ... | ⟨ T₁ , p-t1t ⟩
          with p-ca p-t1t 
      ... | c-fun c1 c2 = c2

  ... | inj₂ a=unk rewrite a=unk =
      unk⊑
  abs-optimal ⟨ T , pt ⟩ p-ca (abs-any a b c)
      with conc-sh-cons (p-ca b) (p-ca c) 
  ... | inj₁ A≡⋆ rewrite A≡⋆ = 
        unk⊑
  ... | inj₂ x = 
        contradiction x a


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

  data STypeEq (A : SType) (B : SType) : Set where
    stype-eq : A ≡ B → STypeEq A B

  L=→cc : ∀{G₁ G₂ T} → L STypeEq G₁ G₂ T → Conc G₁ T × Conc G₂ T
  L=→cc (leftp x x₁ (stype-eq refl)) = ⟨ x , x₁ ⟩

  cc→L= : ∀{G₁ G₂ T} → Conc G₁ T → Conc G₂ T → L STypeEq G₁ G₂ T
  cc→L= g1t g2t = leftp g1t g2t (stype-eq refl)

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


{-

    Coordinate Concretization and Abstraction

   -}
{-
  data Conc2 : Type → Type → SType → SType → Set where
    conc2 : ∀{G₁ G₂ : Type} { T₁ T₂ : SType}
          → Conc G₁ T₁ → Conc G₂ T₂
            -----------------------
          → Conc2 G₁ G₂ T₁ T₂

  data Proj₁ {n m : Level} (P : SType → SType → Set n)
             (P₁ : SType → Set m) : Set (Agda.Primitive._⊔_ n m) where
    proj-1 : 
        (∀{T₁} → P₁ T₁ → Σ[ T₂ ∈ SType ] P T₁ T₂)
      → (∀{T₁ T₂} → P T₁ T₂ → P₁ T₁)
        -----------------------------------------
      → Proj₁ P P₁

  data Proj₂ {n m : Level} (P : SType → SType → Set n)
             (P₂ : SType → Set m) : Set (Agda.Primitive._⊔_ n m) where
    proj-2 : 
        (∀{T₂} → P₂ T₂ → Σ[ T₁ ∈ SType ] P T₁ T₂)
      → (∀{T₁ T₂} → P T₁ T₂ → P₂ T₂)
        -----------------------------------------
      → Proj₂ P P₂

  data Abs2 {n : Level} (P : SType → SType → Set n)
            : Type → Type → Set (lsuc n) where
    abs2 : ∀ {P₁ P₂} {G₁ G₂}
         → Proj₁ P P₁  →  Abs P₁ G₁
         → Proj₂ P P₂  →  Abs P₂ G₂
           ------------------------
         → Abs2 P G₁ G₂

  data And {n m : Level } (P : Set n) (Q : Set m)
           : Set (Agda.Primitive._⊔_ n m) where
    mkAnd : P → Q → And P Q

  conc2p : {n : Level} → (SType → SType → Set n) → Type → Type
         → SType → SType → Set n
  conc2p P G₁ G₂ S₁ S₂ = And (Conc2 G₁ G₂ S₁ S₂) (P S₁ S₂)

  data Interior' {n : Level} (P : SType → SType → Set n)
               : Type → Type → Type → Type → Set (lsuc n) where
    inter : ∀{G₁ G₂ G₃ G₄}
          → Abs2 (conc2p P G₁ G₂) G₃ G₄
            ---------------------------
          → Interior' P G₁ G₂ G₃ G₄


  I= : Type → Type → Type → Type → Set₁ 
  I= = Interior' STypeEq

  conc2= : Type → Type → SType → SType → Set
  conc2= G₁ G₂ S₁ S₂ = And (Conc2 G₁ G₂ S₁ S₂) (STypeEq S₁ S₂)

{-
  p1-conc2= : Type → SType → Set
  p1-conc2= G₁ S₁ = And (Conc G₁ S₁) (STypeEq S₁ S₂)
-}

  conc2ii : ∀{ι} → Conc2 (` ι) (` ι) (` ι) (` ι)
  conc2ii {ι} = conc2 c-base c-base

  stypeii : ∀{ι} → STypeEq (` ι) (` ι)
  stypeii {ι} = stype-eq refl

  conc2=ii : ∀{ι} → conc2= (` ι) (` ι) (` ι) (` ι)
  conc2=ii {ι} = mkAnd conc2ii stypeii

{-
  data IsBase (ι : Base) : SType → Set where
    eq-base : ∀{A : SType} → A ≡ ` ι → IsBase ι A 

  I=ii : ∀ {ι} → I= (` ι) (` ι) (` ι) (` ι)
  I=ii {ι} = inter (abs2 (proj-1 {!!} {!!})
                         (abs-base {!!})
                         (proj-2 {!!} {!!})
                         (abs-base {!!}))

  prop-16 : ∀ {G₁ G₂} → (c : G₁ ~ G₂) → I= G₁ G₂ ((G₁ ⊔ G₂){c}) ((G₁ ⊔ G₂){c})
  prop-16 unk~L = {!!}
  prop-16 unk~R = {!!}
  prop-16 (base~ {ι}) = inter (abs2 (proj-1 {!!} {!!}) (abs-base {!!})
                                    (proj-2 {!!} {!!}) (abs-base {!!}))
  prop-16 (fun~ c c₁) = {!!}
  prop-16 (pair~ c c₁) = {!!}
  prop-16 (sum~ c c₁) = {!!}
-}
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


