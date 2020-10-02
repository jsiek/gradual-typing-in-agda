open import Types
open import PreCastStructure
open import CastStructure
open import Labels
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Data.Maybe
open import Variables
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app) renaming (subst to subst-eq)
open import Data.Empty using (⊥; ⊥-elim)

{-

  This modules defines reduction for the Parameterized Cast Calculus
  and provides a proof of progress. Preservation is guaranteed in the
  way the reduction relation is defined and checked by Agda.

-}


module ParamCastReduction (cs : CastStruct) where

  open CastStruct cs
  
  import ParamCastCalculus
  open ParamCastCalculus Cast


  import ParamCastAux
  open ParamCastAux precast


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

    The reduction relation has a very specific type signature,
    mapping only well-typed terms to well-typed terms, so
    preservation is guaranteed by construction.

   -}

  infix 2 _—→_
  data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    ξ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B}
      → M —→ M′
        ---------------------
      → plug M F —→ plug M′ F

    ξ-blame : ∀ {Γ A B} {F : Frame {Γ} A B} {ℓ}
        ---------------------------
      → plug (blame ℓ) F —→ blame ℓ

    β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
      → Value W
        --------------------
      → (ƛ N) · W —→ N [ W ]

    δ : ∀ {Γ : Context} {A B} {f : rep A → rep B} {k : rep A} {ab} {a} {b}
        ---------------------------------------------------
      → ($_ {Γ}{A ⇒ B} f {ab}) · (($ k){a}) —→ ($ (f k)){b}

    β-if-true :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
        -------------------------
      → if (($ true){f}) M N —→ M

    β-if-false :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
        --------------------------
      → if (($ false){f}) M N —→ N

    β-fst :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        --------------------
      → fst (cons V W) —→ V

    β-snd :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        --------------------
      → snd (cons V W) —→ W

    β-caseL : ∀ {Γ A B C} {V : Γ ⊢ A} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
      → Value V
        --------------------------
      → case (inl V) L M —→ L · V

    β-caseR : ∀ {Γ A B C} {V : Γ ⊢ B} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
      → Value V
        --------------------------
      → case (inr V) L M —→ M · V

    cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
      → (v : Value V) → {a : Active c}
        ------------------------------
      → V ⟨ c ⟩ —→ applyCast V v c {a}

    fun-cast : ∀ {Γ A' B' A₁ A₂} {V : Γ ⊢ A₁ ⇒ A₂} {W : Γ ⊢ A'}
        {c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))}
      → (v : Value V) → Value W → {x : Cross c}
        --------------------------------------------------
      → (V ⟨ c ⟩) · W —→ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩

    fst-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
        {c : Cast ((A `× B) ⇒ (A' `× B'))}
      → Value V → {x : Cross c}
        -------------------------------------
      → fst (V ⟨ c ⟩) —→ (fst V) ⟨ fstC c x ⟩

    snd-cast : ∀ {Γ A B A' B'} {V : Γ ⊢ A `× B}
        {c : Cast ((A `× B) ⇒ (A' `× B'))}
      → Value V → {x : Cross c}
        -------------------------------------
      → snd (V ⟨ c ⟩) —→ (snd V) ⟨ sndC c x ⟩

    case-cast : ∀ {Γ A B A' B' C} {V : Γ ⊢ A `⊎ B}
        {W₁ : Γ ⊢ A' ⇒ C } {W₂ : Γ ⊢ B' ⇒ C}
        {c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))}
      → Value V → {x : Cross c}
        --------------------------------------------
      → case (V ⟨ c ⟩) W₁ W₂ —→
        case V (ƛ ((rename S_ W₁) · ((` Z) ⟨ inlC c x ⟩ )))
               (ƛ ((rename S_ W₂) · ((` Z) ⟨ inrC c x ⟩ )))

  infix  2 _—↠_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  data _—↠_ : ∀{Γ}{A} → Γ ⊢ A → Γ ⊢ A → Set where
    _∎ : ∀ {Γ}{A} (M : Γ ⊢ A)
        ---------
      → M —↠ M

    _—→⟨_⟩_ : ∀ {Γ}{A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
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

  observe : ∀ {Γ A} → (V : Γ ⊢ A) → Value V → Observe
  observe .(ƛ _) V-ƛ = O-fun
  observe {A = A} ($ k) V-const = O-const {A} k
  observe .(cons _ _) (V-pair v v₁) = O-pair
  observe .(inl _) (V-inl v) = O-sum
  observe .(inr _) (V-inr v) = O-sum
  observe (V ⟨ c ⟩) (V-cast v) = observe V v

  data Eval : ∀ {Γ A} → (Γ ⊢ A) → Observe → Set where
    eval : ∀{Γ}{A}{M V : Γ ⊢ A}
         → M —↠ V
         → (v : Value V)
         → Eval M (observe V v)

  {-

   The Progress data type has an additional error case to
   allow for cast errors, i.e., blame. We use the follow
   Error data type to help express the error case.

   -}

  data Error : ∀ {Γ A} → Γ ⊢ A → Set where

    E-blame : ∀ {Γ}{A}{ℓ}
        ---------------------
      → Error{Γ}{A} (blame ℓ)

  data Progress {A} (M : ∅ ⊢ A) : Set where

    step : ∀ {N : ∅ ⊢ A}
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

  progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
  progress (` ())
  progress (ƛ M) = done V-ƛ
  progress (_·_ {∅}{A}{B} M₁ M₂)
      with progress M₁
  ... | step R = step (ξ {F = F-·₁ M₂} R)
  ... | error E-blame = step (ξ-blame {F = F-·₁ M₂})
  ... | done V₁
          with progress M₂
  ...     | step R' = step (ξ {F = (F-·₂ M₁){V₁}} R')
  ...     | error E-blame = step (ξ-blame {F = (F-·₂ M₁){V₁}})
  ...     | done V₂ with V₁
  ...         | V-ƛ = step (β V₂)
  ...         | V-cast {∅}{A = A'}{B = A ⇒ B}{V}{c}{i} v
              with Inert-Cross⇒ c i
  ...         | ⟨ x , ⟨ A₁' , ⟨ A₂' , refl ⟩ ⟩ ⟩ =
                  step (fun-cast v V₂ {x})
  progress (_·_ {∅}{A}{B} M₁ M₂) | done V₁ | done V₂
              | V-const {k = k₁} {f = f₁} with V₂
  ...             | V-const {k = k₂} {f = f₂} =
                    step (δ {ab = f₁} {a = f₂} {b = P-Fun2 f₁})
  ...             | V-ƛ = contradiction f₁ ¬P-Fun
  ...             | V-pair v w = contradiction f₁ ¬P-Pair
  ...             | V-inl v = contradiction f₁ ¬P-Sum
  ...             | V-inr v = contradiction f₁ ¬P-Sum
  ...             | V-cast {∅}{A'}{A}{W}{c}{i} w =
                     contradiction i (G f₁)
                     where G : Prim (A ⇒ B) → ¬ Inert c
                           G (P-Fun f₁) ic = baseNotInert c ic
  progress ($ k) = done V-const
  progress (if L M N) with progress L
  ... | step {L'} R = step (ξ{F = F-if M N} R)
  ... | error E-blame = step (ξ-blame{F = F-if M N})
  ... | done (V-const {k = true}) = step β-if-true
  ... | done (V-const {k = false}) = step β-if-false
  ... | done (V-cast {c = c} {i = i} v) =
          contradiction i (baseNotInert c)

  progress (_⟨_⟩ {∅}{A}{B} M c) with progress M
  ... | step {N} R = step (ξ{F = F-cast c} R)
  ... | error E-blame = step (ξ-blame{F = F-cast c})
  ... | done v with ActiveOrInert c
  ...    | inj₁ a = step (cast v {a})
  ...    | inj₂ i = done (V-cast {c = c} {i = i} v)
  progress {C₁ `× C₂} (cons M₁ M₂) with progress M₁
  ... | step {N} R = step (ξ {F = F-×₂ M₂} R)
  ... | error E-blame = step (ξ-blame {F = F-×₂ M₂})
  ... | done V with progress M₂
  ...    | step {N} R' = step (ξ {F = F-×₁ M₁} R')
  ...    | done V' = done (V-pair V V')
  ...    | error E-blame = step (ξ-blame{F = F-×₁ M₁})
  progress (fst {Γ}{A}{B} M) with progress M
  ... | step {N} R = step (ξ {F = F-fst} R)
  ... | error E-blame = step (ξ-blame{F = F-fst})
  ... | done V
          with V
  ...     | V-pair {V = V₁}{W = V₂} v w = step {N = V₁} (β-fst v w)
  ...     | V-const {k = ()}
  ...     | V-cast {c = c} {i = i} v
              with Inert-Cross× c i
  ...         | ⟨ x , ⟨ A₁' , ⟨ A₂' , refl ⟩ ⟩ ⟩ =
                step (fst-cast {c = c} v {x})
  progress (snd {Γ}{A}{B} M) with progress M
  ... | step {N} R = step (ξ {F = F-snd} R)
  ... | error E-blame = step (ξ-blame{F = F-snd})
  ... | done V with V
  ...     | V-pair {V = V₁}{W = V₂} v w = step {N = V₂} (β-snd v w)
  ...     | V-const {k = ()}
  ...     | V-cast {c = c} {i = i} v
              with Inert-Cross× c i
  ...         | ⟨ x , ⟨ A₁' , ⟨ A₂' , refl ⟩ ⟩ ⟩ =
                step (snd-cast {c = c} v {x})
  progress (inl M) with progress M
  ... | step R = step (ξ {F = F-inl} R)
  ... | error E-blame = step (ξ-blame {F = F-inl})
  ... | done V = done (V-inl V)

  progress (inr M) with progress M
  ... | step R = step (ξ {F = F-inr} R)
  ... | error E-blame = step (ξ-blame {F = F-inr})
  ... | done V = done (V-inr V)

  progress (case L M N) with progress L
  ... | step R = step (ξ {F = F-case M N} R)
  ... | error E-blame = step (ξ-blame {F = F-case M N})
  ... | done V with V
  ...    | V-const {k = ()}
  ...    | V-inl v = step (β-caseL v)
  ...    | V-inr v = step (β-caseR v)
  ...    | V-cast {c = c} {i = i} v
              with Inert-Cross⊎ c i
  ...         | ⟨ x , ⟨ A₁' , ⟨ A₂' , refl ⟩ ⟩ ⟩ =
                step (case-cast {c = c} v {x})
  progress (blame ℓ) = error E-blame


  -- There is no way to plug into a frame and get a blame.
  plug-not-blame : ∀ {Γ A B} {M : Γ ⊢ A} {F : Frame {Γ} A B} {ℓ}
    → plug M F ≢ blame ℓ
  plug-not-blame {F = ParamCastAux.F-·₁ _} ()
  plug-not-blame {F = ParamCastAux.F-·₂ _} ()
  plug-not-blame {F = ParamCastAux.F-if _ _} ()
  plug-not-blame {F = ParamCastAux.F-×₁ _} ()
  plug-not-blame {F = ParamCastAux.F-×₂ _} ()
  plug-not-blame {F = ParamCastAux.F-fst} ()
  plug-not-blame {F = ParamCastAux.F-snd} ()
  plug-not-blame {F = ParamCastAux.F-inl} ()
  plug-not-blame {F = ParamCastAux.F-inr} ()
  plug-not-blame {F = ParamCastAux.F-case _ _} ()
  plug-not-blame {F = ParamCastAux.F-cast _} ()

  plug-not-ƛ : ∀ {Γ A B C} {M : Γ ⊢ A} {F : Frame {Γ} A (C ⇒ B)} {N : Γ , C ⊢ B}
    → plug M F ≢ ƛ N
  plug-not-ƛ {F = ParamCastAux.F-·₁ _} ()
  plug-not-ƛ {F = ParamCastAux.F-·₂ _} ()
  plug-not-ƛ {F = ParamCastAux.F-if _ _} ()
  plug-not-ƛ {F = ParamCastAux.F-fst} ()
  plug-not-ƛ {F = ParamCastAux.F-snd} ()
  plug-not-ƛ {F = ParamCastAux.F-case _ _} ()
  plug-not-ƛ {F = ParamCastAux.F-cast _} ()

  plug-not-const : ∀ {Γ A B} {M : Γ ⊢ A} {F : Frame {Γ} A B} {k : rep B} {f : Prim B}
    → plug M F ≢ (($ k) {f})
  plug-not-const {F = ParamCastAux.F-·₁ _} = λ ()
  plug-not-const {F = ParamCastAux.F-·₂ _} = λ ()
  plug-not-const {F = ParamCastAux.F-if _ _} = λ ()
  plug-not-const {F = ParamCastAux.F-fst} = λ ()
  plug-not-const {F = ParamCastAux.F-snd} = λ ()
  plug-not-const {F = ParamCastAux.F-case _ _} = λ ()
  plug-not-const {F = ParamCastAux.F-cast _} = λ ()

  -- Blame is not a value.
  blame-not-value : ∀ {Γ A} {ℓ}
    → ¬ Value (blame {Γ} {A} ℓ)
  blame-not-value ()

  private
    blame⌿→-aux : ∀ {Γ A} {M′ M : Γ ⊢ A} {ℓ}
      → M′ —→ M
      → M′ ≡ blame ℓ
      → Data.Empty.⊥
    blame⌿→-aux (ξ rd) eq = plug-not-blame eq
    blame⌿→-aux ξ-blame eq = plug-not-blame eq

  -- Blame does not reduce.
  blame⌿→ : ∀ {Γ A} {M : Γ ⊢ A} {ℓ}
    → ¬ (blame {Γ} {A} ℓ —→ M)
  blame⌿→ rd = blame⌿→-aux rd refl

  -- Values do not reduce.
  V⌿→ : ∀ {Γ A} {M N : Γ ⊢ A}
    → Value M
    → ¬ (M —→ N)
  private
    V-pair⌿→ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B} {M′ M}
      → M′ —→ M → M′ ≡ cons V W → Value M′ → Data.Empty.⊥
    V-ƛ⌿→ : ∀ {Γ A B} {N : Γ , A ⊢ B} {M′ M}
      → M′ —→ M → M′ ≡ ƛ N → Data.Empty.⊥
    V-const⌿→ : ∀ {Γ A} {k : rep A} {f : Prim A} {M′ M : Γ ⊢ A}
      → M′ —→ M → M′ ≡ (($ k) {f}) → Data.Empty.⊥
    V-inl⌿→ : ∀ {Γ A B} {V : Γ ⊢ A} {M′ M : Γ ⊢ A `⊎ B}
      → M′ —→ M → M′ ≡ inl V → Value M′ → Data.Empty.⊥
    V-inr⌿→ : ∀ {Γ A B} {V : Γ ⊢ B} {M′ M : Γ ⊢ A `⊎ B}
      → M′ —→ M → M′ ≡ inr V → Value M′ → Data.Empty.⊥
    V-cast⌿→ : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)} {M′ M}
      → M′ —→ M → M′ ≡ V ⟨ c ⟩ → Value M′ → Data.Empty.⊥
  V-pair⌿→ (ξ {F = F-×₁ _} rd) refl (V-pair vV vW) = V⌿→ vW rd
  V-pair⌿→ (ξ {F = F-×₂ _} rd) refl (V-pair vV vW) = V⌿→ vV rd
  V-pair⌿→ (ξ-blame {F = F-×₁ _}) refl (V-pair vV vW) = contradiction vW blame-not-value
  V-pair⌿→ (ξ-blame {F = F-×₂ _}) refl (V-pair vV vW) = contradiction vV blame-not-value
  V-ƛ⌿→ (ξ rd) eq = plug-not-ƛ eq
  V-ƛ⌿→ ξ-blame eq = plug-not-ƛ eq
  V-const⌿→ (ξ rd) eq = plug-not-const eq
  V-const⌿→ ξ-blame eq = plug-not-const eq
  V-inl⌿→ (ξ {F = F-inl} rd) refl (V-inl v) = V⌿→ v rd
  V-inl⌿→ (ξ-blame {F = F-inl}) refl (V-inl v) = contradiction v blame-not-value
  V-inr⌿→ (ξ {F = F-inr} rd) refl (V-inr v) = V⌿→ v rd
  V-inr⌿→ (ξ-blame {F = F-inr}) refl (V-inr v) = contradiction v blame-not-value
  V-cast⌿→ (ξ {F = F-cast _} rd) refl (V-cast v) = V⌿→ v rd
  V-cast⌿→ (ξ-blame {F = F-cast _}) refl (V-cast v) = contradiction v blame-not-value
  -- Here we need a proof that a cast cannot be both active and inert at the same time.
  V-cast⌿→ (cast _ {a}) refl (V-cast {i = i} v) = ActiveNotInert a i

  V⌿→ V-ƛ rd = V-ƛ⌿→ rd refl
  V⌿→ V-const rd = V-const⌿→ rd refl
  V⌿→ (V-pair vV vW) rd = V-pair⌿→ rd refl (V-pair vV vW)
  V⌿→ (V-inl v) rd = V-inl⌿→ rd refl (V-inl v)
  V⌿→ (V-inr v) rd = V-inr⌿→ rd refl (V-inr v)
  V⌿→ (V-cast {i = i} v) rd = V-cast⌿→ rd refl (V-cast {i = i} v)
