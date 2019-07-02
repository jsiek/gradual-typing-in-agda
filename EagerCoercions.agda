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

  {-

     n ::= 
                      I!
               n → n
               n → n; I!
               n → n; ⊥
                 ι
           I? 
           I?;        ⊥
           I?;        I!
           I?; n → n
           I?; n → n; I!
           I?; n → n; ⊥ 


   -}


  infix 7 _↣_
  infix 5 _⨟!
  infix 5 _??_⨟_

  data gCast : Type → Set
  data iCast : Type → Set
  data nCast : Type → Set
  data Cast : Type → Set

  data gCast where
    idι : ∀ {ι : Base} → gCast ((` ι) ⇒ (` ι))
    _↣_ : ∀ {A B A' B'}
      → (c : nCast (B ⇒ A)) → (d : nCast (A' ⇒ B'))
        -----------------------------------------
      → gCast ((A ⇒ A') ⇒ (B ⇒ B'))
    _×'_ : ∀ {A B A' B'}
      → (c : nCast (A ⇒ B)) → (d : nCast (A' ⇒ B'))
        -----------------------------------------
      → gCast ((A `× A') ⇒ (B `× B'))
    _+'_ : ∀ {A B A' B'}
      → (c : nCast (A ⇒ B)) → (d : nCast (A' ⇒ B'))
        -----------------------------------------
      → gCast ((A `⊎ A') ⇒ (B `⊎ B'))

  data iCast where
    _⨟! : ∀{A} {G : Type}
       → gCast (A ⇒ G)
         ------------------------
       → iCast (A ⇒ ⋆)
    `_ : ∀{A B}
       → gCast (A ⇒ B)
       → iCast (A ⇒ B)
    cfail : ∀{A B} (G : Type) → (H : Type) → Label → {a : A ≢ ⋆}
       → iCast (A ⇒ B)

  data nCast where
    id★ : nCast (⋆ ⇒ ⋆)
    _??_⨟_ : ∀{B}
       → (G : Type) → Label → iCast (G ⇒ B)
         ----------------------------------
       → nCast (⋆ ⇒ B)
    _⨟! : ∀{A} {G : Type}
       → gCast (A ⇒ G)
         ------------------------
       → nCast (A ⇒ ⋆)
    `_ : ∀{A B}
       → gCast (A ⇒ B)
       → nCast (A ⇒ B)
    gfail : ∀{A B} → (C : Type) → Label
       → gCast (A ⇒ B)
       → nCast (A ⇒ C)

  data Cast where
    `_ : ∀{A B}
       → nCast (A ⇒ B)
       → Cast (A ⇒ B)
    cfail : ∀{A B} (G : Type) → (H : Type) → Label → {a : A ≢ ⋆}
       → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc


{-
  import ParamCastReduction
  module PCR = ParamCastReduction Cast Inert Active ActiveOrInert
  open PCR
-}
