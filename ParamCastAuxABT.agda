open import Data.Nat
open import Data.List hiding ([_])
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Function using (case_of_; case_return_of_)

open import Types
open import Labels
open import PreCastStructure

open import Syntax


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
    → ∃[ A ] ∃[ V′ ] (Σ[ c ∈ Cast (A ⇒ ⋆) ] Σ[ i ∈ Inert c ] (Γ ⊢ V′ ⦂ A) × (V ≡ (V′ ⟨ c ₍ i ₎⟩)))
  canonical⋆ (⊢$ () p refl) V-const
  canonical⋆ (⊢ƛ A ⊢N ()) V-ƛ
  canonical⋆ (⊢cons ⊢M ⊢N ()) (V-pair v w)
  canonical⋆ (⊢inl B ⊢M ()) (V-inl v)
  canonical⋆ (⊢inr A ⊢M ()) (V-inr v)
  canonical⋆ (⊢wrap c i ⊢M 𝐶⊢-wrap) (V-wrap v i) = ⟨ _ , ⟨ _ , ⟨ _ , ⟨ i , ⟨ ⊢M , refl ⟩ ⟩ ⟩ ⟩ ⟩

  {-
    We shall use a kind of shallow evaluation context, called a Frame,
    to collapse all of the ξ rules into a single rule.
  -}
  data Frame : ∀ (A B : Type) → Set where

    -- □ · M
    F-·₁ : ∀ {A B} (M : Term) → [] ⊢ M ⦂ A → Frame (A ⇒ B) B

    -- V · □
    F-·₂ : ∀ {A B} (V : Term) → [] ⊢ V ⦂ A ⇒ B → Value V → Frame A B

    -- if □ M N
    F-if : ∀ {A} (M N : Term) → [] ⊢ M ⦂ A → [] ⊢ N ⦂ A → Frame (` 𝔹) A

    -- ⟨ V , □ ⟩
    F-×₁ : ∀ {A B} (V : Term) → [] ⊢ V ⦂ A → Value V → Frame B (A `× B)

    -- ⟨ □ , M ⟩
    F-×₂ : ∀ {A B} (M : Term) → [] ⊢ M ⦂ B → Frame A (A `× B)

    -- fst □
    F-fst : ∀ {A B} → Frame (A `× B) A

    -- snd □
    F-snd : ∀ {A B} → Frame (A `× B) B

    -- inl □ other B
    F-inl : ∀ {A} (B : Type) → Frame A (A `⊎ B)

    -- inr □ other A
    F-inr : ∀ {B} (A : Type) → Frame B (A `⊎ B)

    -- case □ of A ⇒ M | B ⇒ N
    F-case : ∀ {C} (A B : Type) (M N : Term)
      → A ∷ [] ⊢ M ⦂ C → B ∷ [] ⊢ N ⦂ C → Frame (A `⊎ B) C

    -- □ ⟨ c ⟩
    F-cast : ∀ {A B} → Cast (A ⇒ B) → Frame A B

    {-
      In order to satisfy progress, we need to consider the case M ⟨ c ₍ i ₎⟩
      when M is not a Value.

      □ ⟨ c ₍ i ₎⟩
    -}
    F-wrap : ∀ {A B} → (c : Cast (A ⇒ B)) → Inert c → Frame A B

  {-
    The plug function inserts an expression into the hole of a frame.
  -}
  plug : ∀ {A B} → Term → Frame A B → Term
  -- □ · M
  plug L (F-·₁ M ⊢M)            = L · M
  -- V · □
  plug M (F-·₂ V ⊢V v)          = V · M
  -- if □ M N
  plug L (F-if M N ⊢M ⊢N)       = if L then M else N endif
  -- ⟨ V , □ ⟩
  plug M (F-×₁ V ⊢V v)          = ⟦ V , M ⟧
  -- ⟨ □ , M ⟩
  plug L (F-×₂ M ⊢M)            = ⟦ L , M ⟧
  -- fst □
  plug M (F-fst)                = fst M
  -- snd □
  plug M (F-snd)                = snd M
  -- inl □ other B
  plug M (F-inl B)              = inl M other B
  -- inr □ other A
  plug M (F-inr A)              = inr M other A
  -- case □ of A ⇒ M | B ⇒ N
  plug L (F-case A B M N ⊢M ⊢N) = case L of A ⇒ M ∣ B ⇒ N
  -- □ ⟨ c ⟩
  plug M (F-cast c)             = M ⟨ c ⟩
  -- □ ⟨ c ₍ i ₎⟩
  plug M (F-wrap c i)           = M ⟨ c ₍ i ₎⟩

  plug-wt : ∀ {A B}
    → (M : Term)
    → [] ⊢ M ⦂ A
    → (F : Frame A B)
      --------------------
    → [] ⊢ plug M F ⦂ B
  plug-wt L ⊢L (F-·₁ M ⊢M) = ⊢· ⊢L ⊢M 𝐶⊢-·
  plug-wt M ⊢M (F-·₂ V ⊢V v) = ⊢· ⊢V ⊢M 𝐶⊢-·
  plug-wt L ⊢L (F-if M N ⊢M ⊢N) = ⊢if ⊢L ⊢M ⊢N 𝐶⊢-if
  plug-wt M ⊢M (F-×₁ V ⊢V v) = ⊢cons ⊢V ⊢M 𝐶⊢-cons
  plug-wt L ⊢L (F-×₂ M ⊢M) = ⊢cons ⊢L ⊢M 𝐶⊢-cons
  plug-wt M ⊢M F-fst = ⊢fst ⊢M 𝐶⊢-fst
  plug-wt M ⊢M F-snd = ⊢snd ⊢M 𝐶⊢-snd
  plug-wt M ⊢M (F-inl B) = ⊢inl B ⊢M 𝐶⊢-inl
  plug-wt M ⊢M (F-inr A) = ⊢inr A ⊢M 𝐶⊢-inr
  plug-wt L ⊢L (F-case A B M N ⊢M ⊢N) = ⊢case A B ⊢L ⊢M ⊢N 𝐶⊢-case
  plug-wt M ⊢M (F-cast c) = ⊢cast c ⊢M 𝐶⊢-cast
  plug-wt M ⊢M (F-wrap c i) = ⊢wrap c i ⊢M 𝐶⊢-wrap

  {-
    Auxiliary lemmas about `plug`.
    First we define a datatype that characterizes terms
    that can be produced by plugging into a frame:
  -}
  data Plugged : Term → Set where
    plugged-app  : ∀ {L M} → Plugged (L · M)
    plugged-if   : ∀ {L M N} → Plugged (if L then M else N endif)
    plugged-pair : ∀ {L M} → Plugged (⟦ L , M ⟧)
    plugged-fst  : ∀ {M} → Plugged (fst M)
    plugged-snd  : ∀ {M} → Plugged (snd M)
    plugged-inl  : ∀ {B M} → Plugged (inl M other B)
    plugged-inr  : ∀ {A M} → Plugged (inr M other A)
    plugged-case : ∀ {A B L M N} → Plugged (case L of A ⇒ M ∣ B ⇒ N)
    plugged-cast : ∀ {A B} {M} {c : Cast (A ⇒ B)} → Plugged (M ⟨ c ⟩)
    plugged-wrap : ∀ {A B} {M} {c : Cast (A ⇒ B)} {i : Inert c}
      → Plugged (M ⟨ c ₍ i ₎⟩)

  is-plugged : ∀ {A B} {F : Frame A B} {N : Term}
    → (M : Term)
    → plug N F ≡ M
    → Plugged M
  is-plugged {F = F-·₁ M ⊢M} _ refl = plugged-app
  is-plugged {F = F-·₂ V ⊢V v} _ refl = plugged-app
  is-plugged {F = F-if M N ⊢M ⊢N} _ refl = plugged-if
  is-plugged {F = F-×₁ V ⊢V v} _ refl = plugged-pair
  is-plugged {F = F-×₂ M ⊢M} _ refl = plugged-pair
  is-plugged {F = F-fst} _ refl = plugged-fst
  is-plugged {F = F-snd} _ refl = plugged-snd
  is-plugged {F = F-inl B} _ refl = plugged-inl
  is-plugged {F = F-inr A} _ refl = plugged-inr
  is-plugged {F = F-case A B M N ⊢M ⊢N} _ refl = plugged-case
  is-plugged {F = F-cast i} _ refl = plugged-cast
  is-plugged {F = F-wrap c i} _ refl = plugged-wrap

  not-plugged : ∀ {A B} {F : Frame A B} {N : Term}
    → (M : Term)
    → ¬ (Plugged M)
    → ¬ (plug N F ≡ M)
  not-plugged M not-plugged eq = contradiction (is-plugged M eq) not-plugged

  var-not-plug : ∀ {A B} {x : Var} {N : Term} {F : Frame A B}
    → plug N F ≢ ` x
  var-not-plug {x = x} = not-plugged (` x) λ ()

  const-not-plug : ∀ {X Y A} {r : rep A} {p : Prim A} {M : Term} {F : Frame X Y}
    → plug M F ≢ $ r # p
  const-not-plug {r = r} {p} = not-plugged ($ r # p) λ ()

  ƛ-not-plug : ∀ {X Y A} {M N : Term} {F : Frame X Y}
    → plug M F ≢ ƛ A ˙ N
  ƛ-not-plug {A = A} {N = N} = not-plugged (ƛ A ˙ N) λ ()

  blame-not-plug : ∀ {X Y A ℓ} {M : Term} {F : Frame X Y}
    → plug M F ≢ blame A ℓ
  blame-not-plug {A = A} {ℓ} = not-plugged (blame A ℓ) λ ()

  value-plug : ∀ {A B} {F : Frame A B} {M} → Value (plug M F) → Value M
  value-plug {F = F-×₁ _ _ _} (V-pair v w) = w
  value-plug {F = F-×₂ _ _}   (V-pair v w) = v
  value-plug {F = F-inl _}    (V-inl v)    = v
  value-plug {F = F-inr _}    (V-inr v)    = v
  value-plug {F = F-wrap _ _} (V-wrap v _) = v


  eta⇒ : ∀ {A B C D} → (M : Term)
       → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D)))
       → (x : Cross c)
       → Term
  eta⇒ {A} {B} {C} {D} M c x =
    ƛ C ˙ (((rename ⇑ M) · (` 0 ⟨ dom c x ⟩)) ⟨ cod c x ⟩)

  eta⇒-wt : ∀ {Γ A B C D} → (M : Term)
    → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D))) → {x : Cross c}
    → Γ ⊢ M ⦂ A ⇒ B
      -------------------------
    → Γ ⊢ eta⇒ M c x ⦂ C ⇒ D
  eta⇒-wt M c {x} ⊢M =
    ⊢ƛ _ (⊢cast (cod c x)
                (⊢· (preserve-rename M ⊢M λ ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩)
                    (⊢cast (dom c x) (⊢` refl) 𝐶⊢-cast) 𝐶⊢-·) 𝐶⊢-cast) 𝐶⊢-ƛ

  eta× : ∀ {A B C D} → (M : Term)
       → (c : Cast ((A `× B) ⇒ (C `× D)))
       → (x : Cross c)
       → Term
  eta× M c x = ⟦ fst M ⟨ fstC c x ⟩ , snd M ⟨ sndC c x ⟩ ⟧

  eta×-wt : ∀ {Γ A B C D} → (M : Term)
    → (c : Cast ((A `× B) ⇒ (C `× D))) → {x : Cross c}
    → Γ ⊢ M ⦂ A `× B
      -------------------------
    → Γ ⊢ eta× M c x ⦂ C `× D
  eta×-wt M c {x} ⊢M =
    ⊢cons (⊢cast (fstC c x) (⊢fst ⊢M 𝐶⊢-fst) 𝐶⊢-cast)
          (⊢cast (sndC c x) (⊢snd ⊢M 𝐶⊢-snd) 𝐶⊢-cast) 𝐶⊢-cons

  eta⊎ : ∀ {A B C D} → (M : Term)
       → (c : Cast ((A `⊎ B) ⇒ (C `⊎ D)))
       → (x : Cross c)
       → Term
  eta⊎ {A} {B} {C} {D} M c x =
    case M of A ⇒ inl (` 0 ⟨ inlC c x ⟩) other D
            ∣ B ⇒ inr (` 0 ⟨ inrC c x ⟩) other C

  eta⊎-wt : ∀ {Γ A B C D} → (M : Term)
    → (c : Cast ((A `⊎ B) ⇒ (C `⊎ D))) → {x : Cross c}
    → Γ ⊢ M ⦂ A `⊎ B
      -------------------------
    → Γ ⊢ eta⊎ M c x ⦂ C `⊎ D
  eta⊎-wt M c {x} ⊢M =
    ⊢case _ _ ⊢M (⊢inl _ (⊢cast (inlC c x) (⊢` refl) 𝐶⊢-cast) 𝐶⊢-inl)
                 (⊢inr _ (⊢cast (inrC c x) (⊢` refl) 𝐶⊢-cast) 𝐶⊢-inr) 𝐶⊢-case

  lookup-unique : ∀ {Γ} {A B : Type}
    → (x : Var)
    → Γ ∋ x ⦂ A
    → Γ ∋ x ⦂ B
      ----------
    → A ≡ B
  lookup-unique {_ ∷ Γ} 0 refl refl = refl
  lookup-unique {_ ∷ Γ} (suc x) x⦂A x⦂B = lookup-unique {Γ} x x⦂A x⦂B

  uniqueness : ∀ {Γ} {A B : Type} {M}
    → Γ ⊢ M ⦂ A
    → Γ ⊢ M ⦂ B
      ----------
    → A ≡ B
  uniqueness {Γ} {M = ` x} (⊢` x⦂A) (⊢` x⦂B) = lookup-unique {Γ} x x⦂A x⦂B
  uniqueness {Γ} (⊢ƛ A ⊢N₁ 𝐶⊢-ƛ) (⊢ƛ A ⊢N₂ 𝐶⊢-ƛ) =
    case uniqueness {A ∷ Γ} ⊢N₁ ⊢N₂ of λ where
      refl → refl
  uniqueness (⊢· ⊢L₁ _ 𝐶⊢-·) (⊢· ⊢L₂ _ 𝐶⊢-·) =
    case uniqueness ⊢L₁ ⊢L₂ of λ where
      refl → refl
  uniqueness (⊢$ r p 𝐶⊢-$) (⊢$ r p 𝐶⊢-$) = refl
  uniqueness (⊢if _ ⊢M₁ _ 𝐶⊢-if) (⊢if _ ⊢M₂ _ 𝐶⊢-if) =
    uniqueness ⊢M₁ ⊢M₂
  uniqueness (⊢cons ⊢M₁ ⊢N₁ 𝐶⊢-cons) (⊢cons ⊢M₂ ⊢N₂ 𝐶⊢-cons) =
    case ⟨ uniqueness ⊢M₁ ⊢M₂ , uniqueness ⊢N₁ ⊢N₂ ⟩ of λ where
      ⟨ refl , refl ⟩ → refl
  uniqueness (⊢fst ⊢M₁ 𝐶⊢-fst) (⊢fst ⊢M₂ 𝐶⊢-fst) =
    case uniqueness ⊢M₁ ⊢M₂ of λ where
      refl → refl
  uniqueness (⊢snd ⊢M₁ 𝐶⊢-snd) (⊢snd ⊢M₂ 𝐶⊢-snd) =
    case uniqueness ⊢M₁ ⊢M₂ of λ where
      refl → refl
  uniqueness (⊢inl B ⊢M₁ 𝐶⊢-inl) (⊢inl B ⊢M₂ 𝐶⊢-inl) =
    case uniqueness ⊢M₁ ⊢M₂ of λ where
      refl → refl
  uniqueness (⊢inr A ⊢M₁ 𝐶⊢-inr) (⊢inr A ⊢M₂ 𝐶⊢-inr) =
    case uniqueness ⊢M₁ ⊢M₂ of λ where
      refl → refl
  uniqueness (⊢case A B ⊢L₁ ⊢M₁ ⊢N₁ 𝐶⊢-case) (⊢case A B ⊢L₂ ⊢M₂ ⊢N₂ 𝐶⊢-case) =
    uniqueness ⊢M₁ ⊢M₂
  uniqueness (⊢cast c ⊢M₁ 𝐶⊢-cast) (⊢cast c ⊢M₂ 𝐶⊢-cast) = refl
  uniqueness (⊢wrap c i ⊢M₁ 𝐶⊢-wrap) (⊢wrap c i ⊢M₂ 𝐶⊢-wrap) = refl
  uniqueness (⊢blame A ℓ 𝐶⊢-blame) (⊢blame A ℓ 𝐶⊢-blame) = refl
