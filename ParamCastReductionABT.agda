open import Types
open import PreCastStructure
open import CastStructureABT
open import Labels
open import Data.Nat
open import Data.Product
  using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Data.Maybe
open import Data.List using (List; _∷_; [])
open import Variables
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  renaming (subst to subst-eq)
open import Data.Empty using (⊥; ⊥-elim)
open import Utils

open import Syntax using (Var; Sig; Rename; _•_; id; ↑; ⇑)


{-
  This modules defines reduction for the Parameterized Cast Calculus
  and provides proofs of both progress and preservation.
-}


module ParamCastReductionABT (cs : CastStruct) where

  open CastStruct cs

  open import ParamCastCalculusABT precast
  open import ParamCastAuxABT precast

  {-
    The following defines the reduction relation for the
    Parameterized Cast Calulus.  The reductions involving casts
    simply dispatch to the appropriate parameters of this
    module. This includes the cast, fun-cast, fst-cast, snd-cast,
    and case-cast rules. To propagate blame to the top of the
    program, we have the ξ-blame rule. All of the usual congruence
    rules are instances of the one ξ rule with the appropriate
    choice of frame. The remaining rules are the usual β and δ
    reduction rules of the STLC.
  -}

  infix 2 _—→_

  data _—→_ : Term → Term → Set where

    ξ : ∀ {M M′ : Term} {F : Frame}
      → M —→ M′
        ---------------------
      → plug M F —→ plug M′ F

    ξ-blame : ∀ {F : Frame} {ℓ}
        ---------------------------
      → plug (blame ℓ) F —→ blame ℓ

    β : ∀ {A} {N : Term} {W : Term}
      → Value W
        --------------------
      → (ƛ A ˙ N) · W —→ N [ W ]

    δ : ∀ {A B} {f : rep A → rep B} {k : rep A}
          {ab : Prim (A ⇒ B)} {a : Prim A} {b : Prim B}
        ---------------------------------------------------
      → ($ f # ab) · ($ k # a) —→ ($ f k # b)

    β-if-true :  ∀ {M N : Term} {p : Prim (` 𝔹)}
        -------------------------------------------
      → if ($ true # p) then M else N endif —→ M

    β-if-false :  ∀ {M N : Term} {p : Prim (` 𝔹)}
        ------------------------------------------
      → if ($ false # p) then M else N endif —→ N

    β-fst :  ∀ {V W : Term}
      → Value V → Value W
        --------------------
      → fst ⟦ V , W ⟧ —→ V

    β-snd :  ∀ {V W : Term}
      → Value V → Value W
        --------------------
      → snd ⟦ V , W ⟧ —→ W

    β-caseL : ∀ {A B} {V M N : Term}
      → Value V
        --------------------------
      → case (inl V other B) of A ⇒ M ∣ B ⇒ N —→ M [ V ]

    β-caseR : ∀ {A B} {V M N : Term}
      → Value V
        --------------------------
      → case (inr V other A) of A ⇒ M ∣ B ⇒ N —→ N [ V ]

    cast : ∀ {A B} {V : Term} {c : Cast (A ⇒ B)}
      → (v : Value V) → {a : Active c}
        ------------------------------
      → V ⟨ c ⟩ —→ applyCast V v c {a}

    wrap : ∀ {A B} {V : Term} {c : Cast (A ⇒ B)}
      → (v : Value V) → {i : Inert c}
        ------------------------------
      → V ⟨ c ⟩ —→ V ⟨ c ₍ i ₎⟩

    -- Fire the following rules when the cast is both cross and inert.
    fun-cast : ∀ {A B C D} {V W : Term} {c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}
      → Value V → Value W
      → {x : Cross c} → {i : Inert c}
        --------------------------------------------------
      → V ⟨ c ₍ i ₎⟩ · W —→ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩

    fst-cast : ∀ {A B C D} {V : Term} {c : Cast ((A `× B) ⇒ (C `× D))}
      → Value V
      → {x : Cross c} → {i : Inert c}
        -------------------------------------
      → fst (V ⟨ c ₍ i ₎⟩) —→ (fst V) ⟨ fstC c x ⟩

    snd-cast : ∀ {A B C D} {V : Term} {c : Cast ((A `× B) ⇒ (C `× D))}
      → Value V
      → {x : Cross c} → {i : Inert c}
        -------------------------------------
      → snd (V ⟨ c ₍ i ₎⟩) —→ (snd V) ⟨ sndC c x ⟩

    case-cast : ∀ {A B C D} {V M N : Term} {c : Cast (A `⊎ B ⇒ C `⊎ D)}
      → Value V
      → {x : Cross c} → {i : Inert c}
        --------------------------------------------
      → case (V ⟨ c ₍ i ₎⟩) of C ⇒ M ∣ D ⇒ N
           —→
         case V of A ⇒ (rename ⇑ M [ ` 0 ⟨ inlC c x ⟩ ])
                 ∣ B ⇒ (rename ⇑ N [ ` 0 ⟨ inrC c x ⟩ ])

  infix  2 _—↠_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  data _—↠_ : Term → Term → Set where
    _∎ : ∀ (M : Term)
        ---------
      → M —↠ M

    _—→⟨_⟩_ : ∀ (L : Term) → {M N : Term}
      → L —→ M
      → M —↠ N
        ---------
      → L —↠ N

  data Observe : Set where
    O-const : ∀{A} → rep A → Observe
    O-fun : Observe
    O-pair : Observe
    O-sum : Observe
    O-blame : Label → Observe

  observe : ∀ (V : Term) → Value V → Observe
  observe _ V-ƛ = O-fun
  observe ($ r # p) (V-const {A}) = O-const {A} r
  observe _ (V-pair v v₁) = O-pair
  observe _ (V-inl v) = O-sum
  observe _ (V-inr v) = O-sum
  observe (V ⟨ c ₍ i ₎⟩) (V-wrap v .i) = observe V v

  data Eval : Term → Observe → Set where
    eval : ∀ {M V}
         → M —↠ V
         → (v : Value V)
         → Eval M (observe V v)

  {-
    The Progress data type has an additional error case to
    allow for cast errors, i.e., blame. We use the follow
    Error data type to help express the error case.
  -}

  data Error : Term → Set where
    E-blame : ∀ {ℓ} → Error (blame ℓ)

  data Progress (M : Term) : Set where

    step : ∀ {N : Term}
      → M —→ N
        -------------
      → Progress M

    done :
        Value M
        ----------
      → Progress M

    error :
        Error M
        ----------
      → Progress M

  {-
    The proof of progress follows the same structure as the one for
    the STLC, by induction on the structure of the expression (or
    equivalently, the typing derivation). In the following, we
    discuss the extra cases that are needed for this cast calculus.

    Each recursive call to progress may result in an error,
    in which case the current expression can take a step
    via the ξ-blame rule with an appropriate frame.

    On the other hand, if the recusive call produces a value, the
    value may be a cast that is inert. In the case for function
    application, the expression takes a step via the fun-cast rule
    (which uses the funCast parameter).  In the case for fst and snd,
    the expression takes a step via fst-cast or snd-cast
    respectively. Regarding the case form, the expression takes a
    step via case-cast.

    Of course, we must add a case for the cast form.
    If the recursive call produces a step, then we step via ξ.
    Likewise, if the recursive call produces an error, we step via ξ-blame.
    Otherwise, the recursive call produces a value.
    We make use of the ActiveOrInert parameter to see which
    kind of cast we are dealing with. If it is active, we reduce
    via the cast rule. Otherwise we form a value using V-cast.

    We must also consider the situations where the subexpression is
    of base type: the argument of a primitive operator and the
    condition of 'if'. In these two cases, the baseNotInert parameter
    ensures that the value not a cast, it is a constant.
  -}

  progress : ∀ {A} → (M : Term) → [] ⊢ M ⦂ A → Progress M
  progress (` x) (⊢` ())
  progress ($ r # p) ⊢M = done V-const
  progress (ƛ A ˙ M) ⊢M = done V-ƛ
  progress (M₁ · M₂) (⊢· ⊢M₁ ⊢M₂ refl) =
    case progress M₁ ⊢M₁ of λ where
      (step R) → step (ξ {F = F-·₁ M₂} R)
      (error E-blame) → step (ξ-blame {F = F-·₁ M₂})
      (done v₁) →
        case progress M₂ ⊢M₂ of λ where
          (step R′) → step (ξ {F = F-·₂ M₁ v₁} R′)
          (error E-blame) → step (ξ-blame {F = F-·₂ M₁ v₁})
          (done v₂) →
            case ⟨ v₁ , ⊢M₁ ⟩ of λ where
              ⟨ V-ƛ , ⊢ƛ _ _ _ ⟩ → step (β v₂)
              ⟨ V-wrap v i , ⊢wrap c .i ⊢M (⟨ refl , refl ⟩) ⟩ →
                case Inert-Cross⇒ c i of λ where
                  ⟨ x , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ → step (fun-cast v v₂ {x})
              ⟨ V-const , ⊢$ r₁ p₁ refl ⟩ →
                case ⟨ v₂ , ⊢M₂ ⟩ of λ where
                  ⟨ V-const , ⊢$ r₂ p₂ refl ⟩ → step (δ {ab = p₁} {p₂} {P-Fun2 p₁})
                  ⟨ V-ƛ , ⊢ƛ _ _ (⟨ refl , refl ⟩) ⟩ → contradiction p₁ ¬P-Fun
                  ⟨ V-pair v w , ⊢cons _ _ refl ⟩ → contradiction p₁ ¬P-Pair
                  ⟨ V-inl v , ⊢inl _ _ refl ⟩ → contradiction p₁ ¬P-Sum
                  ⟨ V-inr v , ⊢inr _ _ refl ⟩ → contradiction p₁ ¬P-Sum
                  ⟨ V-wrap {c = c} w i , ⊢wrap .c .i _ (⟨ refl , refl ⟩) ⟩ →
                    let G : Prim (_ ⇒ _) → ¬ Inert c
                        G = λ { (P-Fun _) ic → baseNotInert c ic } in
                      contradiction i (G p₁)
              ⟨ V-pair _ _ , ⊢cons _ _ () ⟩
              ⟨ V-inl _ , ⊢inl _ _ () ⟩
              ⟨ V-inr _ , ⊢inr _ _ () ⟩
  progress (if L then M else N endif) (⊢if ⊢L ⊢M ⊢N (⟨ ⟨ refl , refl ⟩ , refl ⟩)) =
    case progress L ⊢L of λ where
      (step R) → step (ξ {F = F-if M N} R)
      (error E-blame) → step (ξ-blame {F = F-if M N})
      (done v) →
        case ⟨ v , ⊢L ⟩ of λ where
          ⟨ V-const , ⊢$ true _ refl ⟩ → step β-if-true
          ⟨ V-const , ⊢$ false _ refl ⟩ → step β-if-false
          ⟨ V-wrap v i , ⊢wrap c .i _ (⟨ refl , refl ⟩) ⟩ → contradiction i (baseNotInert c)
          ⟨ V-ƛ , ⊢ƛ _ _ () ⟩
          ⟨ V-inl _ , ⊢inl _ _ () ⟩
          ⟨ V-inr _ , ⊢inr _ _ () ⟩
          ⟨ V-pair _ _ , ⊢cons _ _ () ⟩
  progress (M ⟨ c ⟩) (⊢cast .c ⊢M (⟨ refl , refl ⟩)) =
    case progress M ⊢M of λ where
      (step {N} R) → step (ξ{F = F-cast c} R)
      (error E-blame) → step (ξ-blame{F = F-cast c})
      (done v) →
        case ActiveOrInert c of λ where
          (inj₁ a) → step (cast v {a})
          (inj₂ i) → step (wrap v {i})
  progress (M ⟨ c ₍ i ₎⟩) (⊢wrap .c .i ⊢M (⟨ refl , refl ⟩)) =
    case progress M ⊢M of λ where
      (step R) → step (ξ {F = F-wrap c i} R)
      (error E-blame) → step (ξ-blame {F = F-wrap c i})
      (done v) → done (V-wrap v i)
  progress ⟦ M₁ , M₂ ⟧ (⊢cons ⊢M₁ ⊢M₂ refl) =
    case progress M₁ ⊢M₁ of λ where
      (step R) → step (ξ {F = F-×₂ M₂} R)
      (error E-blame) → step (ξ-blame {F = F-×₂ M₂})
      (done V) →
        case progress M₂ ⊢M₂ of λ where
          (step R′) → step (ξ {F = F-×₁ M₁ V} R′)
          (done V′) → done (V-pair V V′)
          (error E-blame) → step (ξ-blame {F = F-×₁ M₁ V})
  progress (fst M) (⊢fst ⊢M (⟨ B , refl ⟩)) =
    case progress M ⊢M of λ where
      (step R) → step (ξ {F = F-fst} R)
      (error E-blame) → step (ξ-blame {F = F-fst})
      (done v) →
        case ⟨ v , ⊢M ⟩ of λ where
          ⟨ V-const , ⊢$ () p refl ⟩
          ⟨ V-pair {V = V₁} v w , ⊢cons _ _ refl ⟩ → step {N = V₁} (β-fst v w)
          ⟨ V-wrap v i , ⊢wrap c .i _ (⟨ refl , refl ⟩)⟩ →
            case Inert-Cross× c i of λ where
              ⟨ x , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ → step (fst-cast {c = c} v {x})
          ⟨ V-ƛ , ⊢ƛ _ _ () ⟩
          ⟨ V-inl _ , ⊢inl _ _ () ⟩
          ⟨ V-inr _ , ⊢inr _ _ () ⟩
  progress (snd M) (⊢snd ⊢M (⟨ A , refl ⟩)) =
    case progress M ⊢M of λ where
      (step R) → step (ξ {F = F-snd} R)
      (error E-blame) → step (ξ-blame {F = F-snd})
      (done v) →
        case ⟨ v , ⊢M ⟩ of λ where
          ⟨ V-const , ⊢$ () p refl ⟩
          ⟨ V-pair {W = V₂} v w , ⊢cons _ _ refl ⟩ → step {N = V₂} (β-snd v w)
          ⟨ V-wrap v i , ⊢wrap c .i _ (⟨ refl , refl ⟩)⟩ →
            case Inert-Cross× c i of λ where
              ⟨ x , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ → step (snd-cast {c = c} v {x})
          ⟨ V-ƛ , ⊢ƛ _ _ () ⟩
          ⟨ V-inl _ , ⊢inl _ _ () ⟩
          ⟨ V-inr _ , ⊢inr _ _ () ⟩
  progress (inl M other B) (⊢inl .B ⊢M refl) =
    case progress M ⊢M of λ where
      (step R) → step (ξ {F = F-inl B} R)
      (error E-blame) → step (ξ-blame {F = F-inl B})
      (done V) → done (V-inl V)
  progress (inr M other A) (⊢inr .A ⊢M refl) =
    case progress M ⊢M of λ where
      (step R) → step (ξ {F = F-inr A} R)
      (error E-blame) → step (ξ-blame {F = F-inr A})
      (done V) → done (V-inr V)
  progress (case L of A ⇒ M ∣ B ⇒ N)
           (⊢case .A .B ⊢L ⊢M ⊢N (⟨ ⟨ refl , refl ⟩ , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩)) =
    case progress L ⊢L of λ where
      (step R) → step (ξ {F = F-case A B M N} R)
      (error E-blame) → step (ξ-blame {F = F-case A B M N})
      (done v) →
        case ⟨ v , ⊢L ⟩ of λ where
          ⟨ V-const , ⊢$ () p refl ⟩
          ⟨ V-inl v , ⊢inl _ _ refl ⟩ → step (β-caseL v)
          ⟨ V-inr v , ⊢inr _ _ refl ⟩ → step (β-caseR v)
          ⟨ V-wrap v i , ⊢wrap c .i _ (⟨ refl , refl ⟩) ⟩ →
            case Inert-Cross⊎ c i of λ where
              ⟨ x , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ → step (case-cast {c = c} v {x})
          ⟨ V-ƛ , ⊢ƛ _ _ () ⟩
          ⟨ V-pair _ _ , ⊢cons _ _ () ⟩
  progress (blame ℓ) (⊢blame .ℓ tt) = error E-blame

  {- *Auxiliary lemmas* -}
  plug-not-var : ∀ {x : Var} {M : Term} {F : Frame}
    → plug M F ≢ ` x
  plug-not-var {x} {M} {F} = case F return (λ F → plug M F ≢ ` x) of
    λ { (F-·₁ _) → λ () ; (F-·₂ _ _) → λ () ; (F-if _ _) → λ () ;
        (F-×₁ _ _) → λ () ; (F-×₂ _) → λ () ; F-fst → λ () ; F-snd → λ () ;
        (F-inl _) → λ () ; (F-inr _) → λ () ; (F-case _ _ _ _) → λ () ;
        (F-cast _) → λ () ; (F-wrap _ _) → λ () }

  plug-not-ƛ : ∀ {A} {M N : Term} {F : Frame}
    → plug M F ≢ ƛ A ˙ N
  plug-not-ƛ {A} {M} {N} {F} = case F return (λ F → plug M F ≢ ƛ A ˙ N) of
    λ { (F-·₁ _) → λ () ; (F-·₂ _ _) → λ () ; (F-if _ _) → λ () ;
        (F-×₁ _ _) → λ () ; (F-×₂ _) → λ () ; F-fst → λ () ; F-snd → λ () ;
        (F-inl _) → λ () ; (F-inr _) → λ () ; (F-case _ _ _ _) → λ () ;
        (F-cast _) → λ () ; (F-wrap _ _) → λ () }

  plug-not-blame : ∀ {ℓ} {M : Term} {F : Frame}
    → plug M F ≢ blame ℓ
  plug-not-blame {ℓ} {M} {F} = case F return (λ F → plug M F ≢ blame ℓ) of
    λ { (F-·₁ _) → λ () ; (F-·₂ _ _) → λ () ; (F-if _ _) → λ () ;
        (F-×₁ _ _) → λ () ; (F-×₂ _) → λ () ; F-fst → λ () ; F-snd → λ () ;
        (F-inl _) → λ () ; (F-inr _) → λ () ; (F-case _ _ _ _) → λ () ;
        (F-cast _) → λ () ; (F-wrap _ _) → λ () }

  var⌿→ : ∀ {x : Var} {M N : Term}
    → M ≡ ` x
      -------------
    → ¬ (M —→ N)
  var⌿→ eq (ξ R) = contradiction eq plug-not-var
  var⌿→ eq ξ-blame = contradiction eq plug-not-var

  ƛ⌿→ : ∀ {A} {M M₁ N : Term}
    → M ≡ ƛ A ˙ M₁
      -------------
    → ¬ (M —→ N)
  ƛ⌿→ eq (ξ R) = contradiction eq plug-not-ƛ
  ƛ⌿→ eq ξ-blame = contradiction eq plug-not-ƛ

  blame⌿→ : ∀ {ℓ} {M N : Term}
    → M ≡ blame ℓ
      -------------
    → ¬ (M —→ N)
  blame⌿→ eq (ξ R) = contradiction eq plug-not-blame
  blame⌿→ eq ξ-blame = contradiction eq plug-not-blame

  -- Values do not reduce.
  V⌿→ : ∀ {M N : Term}
      → Value M
      → ¬ (M —→ N)
  V⌿→ V-ƛ R = {!!}
  V⌿→ V-const R = {!!}
  V⌿→ (V-pair v w) R = {!!}
  V⌿→ (V-inl v) R = {!!}
  V⌿→ (V-inr v) R = {!!}
  V⌿→ (V-wrap v i) R = {!!}

  preservation : ∀ {Γ A} {M N : Term}
    → Γ ⊢ M ⦂ A
    → M —→ N
      -------------
    → Γ ⊢ N ⦂ A
  preservation (⊢` ∋x) R = contradiction R (var⌿→ refl)
  preservation (⊢$ r p eq) R = contradiction R (V⌿→ V-const)
  preservation (⊢ƛ A ⊢N eq) R = contradiction R (V⌿→ V-ƛ)
  preservation (⊢· ⊢L ⊢M eq) R = {!!}
  preservation (⊢if ⊢L ⊢M ⊢N eq) R = {!!}
  preservation (⊢cons ⊢M ⊢N eq) R = {!!}
  preservation (⊢fst ⊢M eq) R = {!!}
  preservation (⊢snd ⊢M eq) R = {!!}
  preservation (⊢inl B ⊢M eq) R = {!!}
  preservation (⊢inr A ⊢M eq) R = {!!}
  preservation (⊢case A B ⊢L ⊢M ⊢N eq) R = {!!}
  preservation (⊢cast c ⊢M eq) R = {!!}
  preservation (⊢wrap c i ⊢M eq) R = {!!}
  preservation (⊢blame ℓ eq) R = {!!}
