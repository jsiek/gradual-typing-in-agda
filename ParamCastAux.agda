open import Types
open import PreCastStructure
open import Labels
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)

{-

  This modules defines reduction for the Parameterized Cast Calculus
  and provides a proof of progress. Preservation is guaranteed in the
  way the reduction relation is defined and checked by Agda.

-}


module ParamCastAux (pcs : PreCastStruct) where

  open PreCastStruct pcs
  
  import ParamCastCalculus
  open ParamCastCalculus Cast

  {-

  Before defining reduction, we first need to define Value.  In cast
  calculi, whether a cast forms a value or not depends on the shape of
  the cast. But here we have parameterized over casts.  So we must add
  more parameters to tell us whether a cast is a value-forming cast or
  not. So we add the parameter Inert to identify the later, and the
  parameter Active to identify casts that need to be reduced. Further,
  we require that all casts (at least, all the well-typed ones) can be
  categorized one of these two ways, which is given by the
  ActiveOrInert parameter.

  The following is the definition of Value. The case for casts, M ⟨ c ⟩,
  requires M to be a value and c to be an inert cast.

  -}
  data Value : ∀ {Γ A} → Γ ⊢ A → Set where

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        -----------
      → Value (ƛ N)

    V-const : ∀ {Γ} {A : Type} {k : rep A} {f : Prim A}
        ------------------------
      → Value {Γ} {A} (($ k){f})

    V-pair : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        -----------------
      → Value (cons V W)

    V-inl : ∀ {Γ A B} {V : Γ ⊢ A}
      → Value V
        --------------------------
      → Value {Γ} {A `⊎ B} (inl V)

    V-inr : ∀ {Γ A B} {V : Γ ⊢ B}
      → Value V
        --------------------------
      → Value {Γ} {A `⊎ B} (inr V)

    V-cast : ∀ {Γ : Context} {A B : Type} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        {i : Inert c}
      → Value V
        ---------------
      → Value (V ⟨ c ⟩)


  {-

  A value of type ⋆ must be of the form M ⟨ c ⟩ where c is inert cast.

  -}
  canonical⋆ : ∀ {Γ} → (M : Γ ⊢ ⋆) → (Value M)
             → Σ[ A ∈ Type ] Σ[ M' ∈ (Γ ⊢ A) ] Σ[ c ∈ (Cast (A ⇒ ⋆)) ]
               Inert c × (M ≡ (M' ⟨ c ⟩))
  canonical⋆ .($ _) (V-const {k = ()})  
  canonical⋆ .(_ ⟨ _ ⟩) (V-cast{Γ}{A}{B}{V}{c}{i} v) =
      ⟨ A , ⟨ V , ⟨ c , ⟨ i , refl ⟩ ⟩ ⟩ ⟩

  {-

   We shall use a kind of shallow evaluation context, called a Frame,
   to collapse all of the ξ rules into a single rule.

  -}

  data Frame : {Γ : Context} → Type → Type → Set where

    F-·₁ : ∀ {Γ A B}
      → Γ ⊢ A
      → Frame {Γ} (A ⇒ B) B

    F-·₂ : ∀ {Γ A B}
      → (M : Γ ⊢ A ⇒ B) → ∀{v : Value {Γ} M}
      → Frame {Γ} A B

    F-if : ∀ {Γ A}
      → Γ ⊢ A
      → Γ ⊢ A    
      → Frame {Γ} (` 𝔹) A

    F-×₁ : ∀ {Γ A B}
      → Γ ⊢ A
      → Frame {Γ} B (A `× B)

    F-×₂ : ∀ {Γ A B}
      → Γ ⊢ B
      → Frame {Γ} A (A `× B)

    F-fst : ∀ {Γ A B}
      → Frame {Γ} (A `× B) A

    F-snd : ∀ {Γ A B}
      → Frame {Γ} (A `× B) B

    F-inl : ∀ {Γ A B}
      → Frame {Γ} A (A `⊎ B)

    F-inr : ∀ {Γ A B}
      → Frame {Γ} B (A `⊎ B)

    F-case : ∀ {Γ A B C}
      → Γ ⊢ A ⇒ C
      → Γ ⊢ B ⇒ C
      → Frame {Γ} (A `⊎ B) C

    F-cast : ∀ {Γ A B}
      → Cast (A ⇒ B)
      → Frame {Γ} A B

  {-

  The plug function inserts an expression into the hole of a frame.

  -}

  plug : ∀{Γ A B} → Γ ⊢ A → Frame {Γ} A B → Γ ⊢ B
  plug L (F-·₁ M)      = L · M
  plug M (F-·₂ L)      = L · M
  plug L (F-if M N)    = if L M N
  plug L (F-×₁ M)      = cons M L
  plug M (F-×₂ L)      = cons M L
  plug M (F-fst)      = fst M
  plug M (F-snd)      = snd M
  plug M (F-inl)      = inl M
  plug M (F-inr)      = inr M
  plug L (F-case M N) = case L M N
  plug M (F-cast c) = M ⟨ c ⟩

  eta⇒ : ∀ {Γ A B C D} → (M : Γ ⊢ A ⇒ B) 
       → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D)))
       → (x : Cross c)
       → Γ ⊢ C ⇒ D
  eta⇒ M c x =
     ƛ (((rename S_ M) · ((` Z) ⟨ dom c x ⟩)) ⟨ cod c x ⟩)

  eta× : ∀ {Γ A B C D} → (M : Γ ⊢ A `× B)
       → (c : Cast ((A `× B) ⇒ (C `× D)))
       → (x : Cross c)
       → Γ ⊢ C `× D
  eta× M c x =
     cons (fst M ⟨ fstC c x ⟩) (snd M ⟨ sndC c x ⟩)

  eta⊎ : ∀ {Γ A B C D} → (M : Γ ⊢ A `⊎ B)
       → (c : Cast ((A `⊎ B) ⇒ (C `⊎ D)))
       → (x : Cross c)
       → Γ ⊢ C `⊎ D
  eta⊎ M c x =
     let l = inl ((` Z) ⟨ inlC c x ⟩) in
     let r = inr ((` Z) ⟨ inrC c x ⟩) in
     case M (ƛ l) (ƛ r)
