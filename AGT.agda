module AGT where

  open import Types
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

  data SType : Set where
    SNat : SType
    SBool : SType
    _⇒_ : SType → SType → SType
    _`×_ : SType → SType → SType
    _`⊎_ : SType → SType → SType

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

  
