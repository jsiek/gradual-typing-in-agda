module AGT where

  open import Types
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contradiction)

  data SType : Set where
    SNat : SType
    SBool : SType
    _⇒_ : SType → SType → SType
    _`×_ : SType → SType → SType
    _`⊎_ : SType → SType → SType

  data _⌢_ : SType → SType → Set where
    nat⌢ : SNat ⌢ SNat
    bool⌢ : SBool ⌢ SBool
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
    c-nat : Conc Nat SNat
    c-bool : Conc 𝔹 SBool
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
  conc ⋆ = ⟨ SBool , c-unk ⟩
  conc Nat = ⟨ SNat , c-nat ⟩
  conc 𝔹 = ⟨ SBool , c-bool ⟩
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
  prec-unk-inv {Nat} (prec f) with f {SBool} c-unk
  ... | ()
  prec-unk-inv {𝔹} (prec f) with f {SNat} c-unk
  ... | ()
  prec-unk-inv {A ⇒ A₁} (prec f) with f {SNat} c-unk
  ... | ()
  prec-unk-inv {A `× A₁} (prec f) with f {SNat} c-unk
  ... | ()
  prec-unk-inv {A `⊎ A₁} (prec f) with f {SNat} c-unk
  ... | ()

  prec-nat-inv : ∀{A}
    → Nat `⊑ A
      ---------------
    → A ≡ Nat ⊎ A ≡ ⋆
  prec-nat-inv {⋆} (prec f) = inj₂ refl
  prec-nat-inv {Nat} (prec f) = inj₁ refl
  prec-nat-inv {𝔹} (prec f) with f {SNat} c-nat
  ... | ()
  prec-nat-inv {A ⇒ A₁} (prec f) with f {SNat} c-nat
  ... | ()
  prec-nat-inv {A `× A₁} (prec f) with f {SNat} c-nat
  ... | ()
  prec-nat-inv {A `⊎ A₁} (prec f) with f {SNat} c-nat
  ... | ()

  prec-bool-inv : ∀{A}
    → 𝔹 `⊑ A
      ---------------
    → A ≡ 𝔹 ⊎ A ≡ ⋆
  prec-bool-inv {⋆} (prec f) = inj₂ refl
  prec-bool-inv {Nat} (prec f) with f {SBool} c-bool
  ... | ()
  prec-bool-inv {𝔹} (prec f) = inj₁ refl
  prec-bool-inv {A ⇒ A₁} (prec f) with f {SBool} c-bool
  ... | ()
  prec-bool-inv {A `× A₁} (prec f) with f {SBool} c-bool
  ... | ()
  prec-bool-inv {A `⊎ A₁} (prec f) with f {SBool} c-bool
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
  prec-left-fun-inv {A₁} {A₂} {Nat} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-fun ca1 ca2)
  ... | ()
  prec-left-fun-inv {A₁} {A₂} {𝔹} (prec f)
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
  prec-left-pair-inv {A₁} {A₂} {Nat} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-pair ca1 ca2)
  ... | ()
  prec-left-pair-inv {A₁} {A₂} {𝔹} (prec f)
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
  prec-left-sum-inv {A₁} {A₂} {Nat} (prec f)
      with conc A₁ | conc A₂
  ... | ⟨ A₁' , ca1 ⟩ | ⟨ A₂' , ca2 ⟩
      with f (c-sum ca1 ca2)
  ... | ()
  prec-left-sum-inv {A₁} {A₂} {𝔹} (prec f)
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
  le-implies-prec nat⊑ = prec (λ {S} z → z)
  le-implies-prec bool⊑ = prec (λ {S} z → z)
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
  prec-implies-le {Nat} {B} (prec f) with prec-nat-inv (prec f)
  ... | inj₁ eq rewrite eq = nat⊑
  ... | inj₂ eq rewrite eq = unk⊑
  prec-implies-le {𝔹} {B} (prec f) with prec-bool-inv (prec f)
  ... | inj₁ eq rewrite eq = bool⊑
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
  cons-implies-ceq nat~ = cons c-nat c-nat
  cons-implies-ceq bool~ = cons c-bool c-bool
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
    abs-nat : ∀{P : SType → Set}
      → (∀{T : SType} → P T → T ≡ SNat)
        -------------------------------
      → Abs P Nat
    abs-bool : ∀{P : SType → Set}
      → (∀{T : SType} → P T → T ≡ SBool)
        --------------------------------
      → Abs P 𝔹
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
  conc-abs-sound (abs-nat p-nat) {T} pt
    rewrite p-nat {T} pt = c-nat
  conc-abs-sound (abs-bool p-bool) {T} pt
    rewrite p-bool {T} pt = c-bool
  conc-abs-sound (abs-fun allfun dom-p abs-a cod-p abs-b) pt
      with allfun
  ... | funs af
      with af pt
  ... | ⟨ T₁ , ⟨ T₂ , eq ⟩ ⟩ rewrite eq =
        let ih1 = conc-abs-sound abs-a in
        let ih2 = conc-abs-sound abs-b in
        c-fun (ih1 (dom-dom dom-p pt)) (ih2 (cod-cod cod-p pt))
  conc-abs-sound (abs-any a b c) pt = c-unk

  c-any-nat  : ∀{A}
     → Conc A SNat
     → A ≡ Nat ⊎ A ≡ ⋆
  c-any-nat c-nat = inj₁ refl
  c-any-nat c-unk = inj₂ refl

  c-any-bool  : ∀{A}
     → Conc A SBool
     → A ≡ 𝔹 ⊎ A ≡ ⋆
  c-any-bool c-bool = inj₁ refl
  c-any-bool c-unk = inj₂ refl

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
  conc-sh-cons c-nat c-nat = inj₂ nat⌢
  conc-sh-cons c-bool c-bool = inj₂ bool⌢
  conc-sh-cons (c-fun a-t1 a-t3) (c-fun a-t2 a-t4) = inj₂ fun⌢
  conc-sh-cons (c-pair a-t1 a-t3) (c-pair a-t2 a-t4) = inj₂ pair⌢
  conc-sh-cons (c-sum a-t1 a-t3) (c-sum a-t2 a-t4) = inj₂ sum⌢
  conc-sh-cons c-unk a-t2 = inj₁ refl

  abs-optimal : ∀ {P : SType → Set} {A A' : Type}
    → (Σ[ T ∈ SType ] P T)
    → P ⊆ Conc A  →  Abs P A'
      -------------------------
    → A ⊑ A'
  abs-optimal ⟨ T , pt ⟩ p-ca (abs-nat all-nat)
      with pt
  ... | pt'
      rewrite all-nat pt
      with c-any-nat (p-ca pt') 
  ... | inj₁ eq rewrite eq = Refl⊑
  ... | inj₂ eq rewrite eq = unk⊑
  abs-optimal ⟨ T , pt ⟩ p-ca (abs-bool all-bool)
      with pt
  ... | pt'
      rewrite all-bool pt
      with c-any-bool (p-ca pt') 
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
