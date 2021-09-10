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
-- open import Variables
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  renaming (subst to subst-eq)
open import Data.Empty using (⊥; ⊥-elim)
open import Utils

open import Syntax using (Var; Sig; Rename; _•_; id; ext; ↑; ⇑; _∋_⦂_)


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
         case V of A ⇒ ((rename (ext ⇑) M) [ ` 0 ⟨ inlC c x ⟩ ])
                 ∣ B ⇒ ((rename (ext ⇑) N) [ ` 0 ⟨ inrC c x ⟩ ])

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

  plug-not-const : ∀ {A} {r : rep A} {p : Prim A} {M : Term} {F : Frame}
    → plug M F ≢ $ r # p
  plug-not-const {A} {r} {p} {M} {F} = case F return (λ F → plug M F ≢ $ r # p) of
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

  const⌿→ : ∀ {A} {r : rep A} {p : Prim A} {M N : Term}
    → M ≡ $ r # p
    → ¬ (M —→ N)
  const⌿→ eq (ξ R) = contradiction eq plug-not-const
  const⌿→ eq ξ-blame = contradiction eq plug-not-const

  blame⌿→ : ∀ {ℓ} {M N : Term}
    → M ≡ blame ℓ
      -------------
    → ¬ (M —→ N)
  blame⌿→ eq (ξ R) = contradiction eq plug-not-blame
  blame⌿→ eq ξ-blame = contradiction eq plug-not-blame

  -- Values do not reduce.
  postulate
    Value⌿→ : ∀ {M N : Term}
      → Value M
      → ¬ (M —→ N)
  -- Value⌿→ V-ƛ R = contradiction R (ƛ⌿→ refl)
  -- Value⌿→ V-const R = contradiction R (const⌿→ refl)
  -- Value⌿→ (V-pair v w) R = {!!}
  -- Value⌿→ (V-inl v) R = {!!}
  -- Value⌿→ (V-inr v) R = {!!}
  -- Value⌿→ (V-wrap v i) R = {!!}

  plug-inversion : ∀ {Γ M F A}
    → Γ ⊢ plug M F ⦂ A
      -------------------------------------------------------------
    → ∃[ B ] Γ ⊢ M ⦂ B × (∀ M' → Γ ⊢ M' ⦂ B → Γ ⊢ plug M' F ⦂ A)
  plug-inversion {M = L} {F-·₁ M} {A} (⊢·-refl ⊢L ⊢M) =
    ⟨ _ ⇒ A , ⟨ ⊢L , (λ M' ⊢M' → ⊢·-refl ⊢M' ⊢M) ⟩ ⟩
  plug-inversion {M = M} {F-·₂ V v} (⊢·-refl ⊢V ⊢M) =
    ⟨ _ , ⟨ ⊢M , (λ M' ⊢M' → ⊢·-refl ⊢V ⊢M') ⟩ ⟩
  plug-inversion {M = L} {F-if M N} (⊢if-refl ⊢L ⊢M ⊢N) =
    ⟨ _ , ⟨ ⊢L , (λ M' ⊢M' → ⊢if-refl ⊢M' ⊢M ⊢N) ⟩ ⟩
  plug-inversion {F = F-×₁ V v} (⊢cons-refl ⊢M ⊢N) =
    ⟨ _ , ⟨ ⊢N , (λ M' ⊢M' → ⊢cons-refl ⊢M ⊢M') ⟩ ⟩
  plug-inversion {F = F-×₂ M} (⊢cons-refl ⊢M ⊢N) =
    ⟨ _ , ⟨ ⊢M , (λ M' ⊢M' → ⊢cons-refl ⊢M' ⊢N) ⟩ ⟩
  plug-inversion {F = F-fst} (⊢fst-refl ⊢M) =
    ⟨ _ , ⟨ ⊢M , (λ M' ⊢M' → ⊢fst-refl ⊢M') ⟩ ⟩
  plug-inversion {F = F-snd} (⊢snd-refl ⊢M) =
    ⟨ _ , ⟨ ⊢M , (λ M' ⊢M' → ⊢snd-refl ⊢M') ⟩ ⟩
  plug-inversion {F = F-inl B} (⊢inl-refl .B ⊢M) =
    ⟨ _ , ⟨ ⊢M , (λ M' ⊢M' → ⊢inl-refl B ⊢M') ⟩ ⟩
  plug-inversion {F = F-inr A} (⊢inr-refl .A ⊢M) =
    ⟨ _ , ⟨ ⊢M , (λ M' ⊢M' → ⊢inr-refl A ⊢M') ⟩ ⟩
  plug-inversion {F = F-case A B M N} (⊢case-refl .A .B ⊢L ⊢M ⊢N) =
    ⟨ _ , ⟨ ⊢L , (λ M' ⊢M' → ⊢case-refl A B ⊢M' ⊢M ⊢N) ⟩ ⟩
  plug-inversion {F = F-cast c} (⊢cast-refl .c ⊢M) =
    ⟨ _ , ⟨ ⊢M , (λ M' ⊢M' → ⊢cast-refl c ⊢M') ⟩ ⟩
  plug-inversion {F = F-wrap c i} (⊢wrap-refl .c .i ⊢M) =
    ⟨ _ , ⟨ ⊢M , (λ M' ⊢M' → ⊢wrap-refl c i ⊢M') ⟩ ⟩

  preserve : ∀ {Γ A} {M N : Term}
    → Γ ⊢ M ⦂ A
    → M —→ N
      -------------
    → Γ ⊢ N ⦂ A
  {- casing on the reduction step and then inversion on the derivation of M. -}
  preserve ⊢M (ξ R) =
    case plug-inversion ⊢M of λ where
      ⟨ _ , ⟨ ⊢M' , plug-wt ⟩ ⟩ → plug-wt _ {- M' -} (preserve ⊢M' R)
  preserve ⊢M ξ-blame = ⊢blame-refl _
  preserve (⊢·-refl (⊢ƛ-refl _ ⊢N) ⊢M) (β v) = preserve-substitution _ _ ⊢N ⊢M
  preserve (⊢·-refl (⊢$-refl f _) (⊢$-refl k _)) δ = ⊢$-refl (f k) _
  preserve (⊢·-refl (⊢wrap-refl c i ⊢M) ⊢N) (fun-cast v w) =
    ⊢cast-refl (cod c _) (⊢·-refl ⊢M (⊢cast-refl (dom c _) ⊢N))
  preserve (⊢if-refl ⊢L ⊢M ⊢N) β-if-true = ⊢M
  preserve (⊢if-refl ⊢L ⊢M ⊢N) β-if-false = ⊢N
  preserve (⊢fst-refl (⊢cons-refl ⊢M ⊢N)) (β-fst v w) = ⊢M
  preserve (⊢fst-refl (⊢wrap-refl c i ⊢M)) (fst-cast v) =
    ⊢cast-refl (fstC c _) (⊢fst-refl ⊢M)
  preserve (⊢snd-refl (⊢cons-refl ⊢M ⊢N)) (β-snd v w) = ⊢N
  preserve (⊢case-refl A B (⊢inl-refl _ ⊢L) ⊢M ⊢N) (β-caseL v) =
    preserve-substitution _ _ ⊢M ⊢L
  preserve (⊢case-refl A B (⊢inr-refl _ ⊢L) ⊢M ⊢N) (β-caseR v) =
    preserve-substitution _ _ ⊢N ⊢L
  preserve {Γ} (⊢case-refl C D (⊢wrap-refl c i ⊢L) ⊢M ⊢N) (case-cast {A} {B} {C} {D} {V} {M} {N} v {x}) =
    ⊢case-refl A B ⊢L
      (preserve-substitution _ _ (preserve-rename M ⊢M (λ { {zero}  ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩ ;
                                                            {suc x} ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩ }))
                                 (⊢cast-refl (inlC c x) (⊢` refl)))
      (preserve-substitution _ _ (preserve-rename N ⊢N (λ { {zero}  ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩ ;
                                                            {suc x} ∋x → ⟨ _ , ⟨ ∋x , refl ⟩ ⟩ }))
                                 (⊢cast-refl (inrC c x) (⊢` refl)))
  preserve (⊢cast-refl c ⊢M) (wrap v {i}) = ⊢wrap-refl c i ⊢M
