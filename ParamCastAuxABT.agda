open import Types
open import PreCastStructure
open import Labels
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Empty using (⊥; ⊥-elim)

open import Syntax using (Sig; Rename; _•_; id; ↑; ⇑)

{-

  This modules defines reduction for the Parameterized Cast Calculus
  and provides a proof of progress. Preservation is guaranteed in the
  way the reduction relation is defined and checked by Agda.

-}


module ParamCastAuxABT (pcs : PreCastStruct) where

  open PreCastStruct pcs

  open import ParamCastCalculusABT pcs


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
  data Value : ∀ Term → Set where

    V-ƛ : ∀ {A} {N : Term}
        -----------
      → Value (ƛ A ˙ N)

    V-const : ∀ {A} {r : rep A} {p : Prim A}
        ------------------------
      → Value ($ r # p)

    V-pair : ∀ {V W : Term}
      → Value V → Value W
        -----------------
      → Value ⟦ V , W ⟧

    V-inl : ∀ {B} {V : Term}
      → Value V
        --------------------------
      → Value (inl V other B)

    V-inr : ∀ {A} {W : Term}
      → Value W
        --------------------------
      → Value (inr W other A)

    V-wrap : ∀ {A B} {V : Term} {c : Cast (A ⇒ B)}
      → Value V → (i : Inert c)
        ---------------
      → Value (V ⟨ c ₍ i ₎⟩)

  {-
    A value of type ⋆ must be of the form M ⟨ c ⟩ where c is inert cast.
  -}
  canonical⋆ : ∀ {Γ} {V : Term}
    → (⊢V : Γ ⊢ V ⦂ ⋆) → (Value V)
      --------------------------
    → ∃[ A ] ∃[ V′ ] (Σ[ c ∈ Cast (A ⇒ ⋆) ] Σ[ i ∈ Inert c ] (V ≡ (V′ ⟨ c ₍ i ₎⟩)))
  canonical⋆ ⊢lit (V-const {r = ()})
  canonical⋆ (⊢wrap tV .c .i) (V-wrap {A} {.⋆} {V} {c} v i) = ⟨ A , ⟨ V , ⟨ c , ⟨ i , refl ⟩ ⟩ ⟩ ⟩

  {-
    We shall use a kind of shallow evaluation context, called a Frame,
    to collapse all of the ξ rules into a single rule.
  -}
  data Frame : Set where

    -- □ · M
    F-·₁ : ∀ (M : Term) → Frame

    -- V · □
    F-·₂ : ∀ (V : Term) → Value V → Frame

    -- if □ M N
    F-if : ∀ (M N : Term) → Frame

    -- ⟨ V , □ ⟩
    F-×₁ : ∀ (V : Term) → Value V → Frame

    -- ⟨ □ , M ⟩
    F-×₂ : ∀ (M : Term) → Frame

    -- fst □
    F-fst : Frame

    -- snd □
    F-snd : Frame

    -- inl □ other B
    F-inl : ∀ (B : Type) → Frame

    -- inr □ other A
    F-inr : ∀ (A : Type) → Frame

    -- case □ of A ⇒ M | B ⇒ N
    F-case : ∀ (A B : Type) (M N : Term) → Frame

    -- □ ⟨ c ⟩
    F-cast : ∀ {A B} → Cast (A ⇒ B) → Frame

    {-
      In order to satisfy progress, we need to consider the case M ⟨ c ₍ i ₎⟩
      when M is not a Value.

      □ ⟨ c ₍ i ₎⟩
    -}
    F-wrap : ∀ {A B} → (c : Cast (A ⇒ B)) → Inert c → Frame

  {-
    The plug function inserts an expression into the hole of a frame.
  -}
  plug : Term → Frame → Term
  -- □ · M
  plug L (F-·₁ M)         = L · M
  -- V · □
  plug M (F-·₂ V v)       = V · M
  -- if □ M N
  plug L (F-if M N)       = if L then M else N endif
  -- ⟨ V , □ ⟩
  plug M (F-×₁ V v)       = ⟦ V , M ⟧
  -- ⟨ □ , M ⟩
  plug L (F-×₂ M)         = ⟦ L , M ⟧
  -- fst □
  plug M (F-fst)          = fst M
  -- snd □
  plug M (F-snd)          = snd M
  -- inl □ other B
  plug M (F-inl B)        = inl M other B
  -- inr □ other A
  plug M (F-inr A)        = inr M other A
  -- case □ of A ⇒ M | B ⇒ N
  plug L (F-case A B M N) = case L of A ⇒ M ∣ B ⇒ N
  -- □ ⟨ c ⟩
  plug M (F-cast c)       = M ⟨ c ⟩
  -- □ ⟨ c ₍ i ₎⟩
  plug M (F-wrap c i)     = M ⟨ c ₍ i ₎⟩

  eta⇒ : ∀ {A B C D} → (M : Term)
       → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D)))
       → (x : Cross c)
       → Term
  eta⇒ {A} {B} {C} {D} M c x = ƛ C ˙ (((rename ⇑ M) · (` 0 ⟨ dom c x ⟩)) ⟨ cod c x ⟩)

  -- eta⇒-wt : ∀ {Γ A B C D} → (M : Term)
  --   → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D))) → {x : Cross c}
  --   → Γ ⊢ M ⦂ A ⇒ B
  --     -------------------------
  --   → Γ ⊢ eta⇒ M c x ⦂ C ⇒ D

  eta× : ∀ {A B C D} → (M : Term)
       → (c : Cast ((A `× B) ⇒ (C `× D)))
       → (x : Cross c)
       → Term
  eta× M c x = ⟦ fst M ⟨ fstC c x ⟩ , snd M ⟨ sndC c x ⟩ ⟧

  eta⊎ : ∀ {A B C D} → (M : Term)
       → (c : Cast ((A `⊎ B) ⇒ (C `⊎ D)))
       → (x : Cross c)
       → Term
  eta⊎ {A} {B} {C} {D} M c x =
    case M of A ⇒ inl (` 0 ⟨ inlC c x ⟩) other D
            ∣ B ⇒ inr (` 0 ⟨ inrC c x ⟩) other C
