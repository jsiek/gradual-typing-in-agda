open import Types
open import PreCastStructure
open import CastStructure
open import Labels
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Data.Maybe
open import Variables
open import Relation.Nullary using (¬_)
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

  open import ParamCastSubtyping precast


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


  {- NOTE:
     The props below are for blame-subtyping.
  -}
  plug-blame-allsafe-inv : ∀ {Γ A B} {F : Frame {Γ = Γ} A B} {ℓ ℓ′}
    → CastsAllSafe (plug (blame ℓ′) F) ℓ
      -------------------------------------
    → ℓ ≢ ℓ′
  plug-blame-allsafe-inv {F = F-·₁ _} (allsafe-· (allsafe-blame-diff-ℓ ℓ≢ℓ′) _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-·₂ _} (allsafe-· _ (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-if _ _} (allsafe-if (allsafe-blame-diff-ℓ ℓ≢ℓ′) _ _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-×₁ _} (allsafe-cons _ (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-×₂ _} (allsafe-cons (allsafe-blame-diff-ℓ ℓ≢ℓ′) _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-fst} (allsafe-fst (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-snd} (allsafe-snd (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-inl} (allsafe-inl (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-inr} (allsafe-inr (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-case _ _} (allsafe-case (allsafe-blame-diff-ℓ ℓ≢ℓ′) _ _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-cast _} (allsafe-cast-same-ℓ _ _ (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
  plug-blame-allsafe-inv {F = F-cast _} (allsafe-cast-diff-ℓ _ (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′

  preserve-allsafe-plug : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B} {ℓ}
    → CastsAllSafe (plug M F) ℓ
    → M —→ M′
      -----------------------------
    → CastsAllSafe (plug M′ F) ℓ

  preserve-allsafe : ∀ {Γ A} {M M′ : Γ ⊢ A} {ℓ}
    → CastsAllSafe M ℓ
    → M —→ M′
      --------------------
    → CastsAllSafe M′ ℓ

  preserve-allsafe-plug {M = L} {L′} {F = F-·₁ M} (allsafe-· allsafe-L allsafe-M) rd = allsafe-· (preserve-allsafe allsafe-L rd) allsafe-M
  preserve-allsafe-plug {F = F-·₂ L {v}} (allsafe-· allsafe-L allsafe-M) rd = allsafe-· allsafe-L (preserve-allsafe allsafe-M rd)
  preserve-allsafe-plug {F = F-if M N} (allsafe-if allsafe-L allsafe-M allsafe-N) rd = allsafe-if (preserve-allsafe allsafe-L rd ) allsafe-M allsafe-N
  preserve-allsafe-plug {F = F-×₁ M} (allsafe-cons allsafe-M allsafe-N) rd = allsafe-cons allsafe-M (preserve-allsafe allsafe-N rd)
  preserve-allsafe-plug {F = F-×₂ N} (allsafe-cons allsafe-M allsafe-N) rd = allsafe-cons (preserve-allsafe allsafe-M rd) allsafe-N
  preserve-allsafe-plug {F = F-fst} (allsafe-fst allsafe-M) rd = allsafe-fst (preserve-allsafe allsafe-M rd)
  preserve-allsafe-plug {F = F-snd} (allsafe-snd allsafe-M) rd = allsafe-snd (preserve-allsafe allsafe-M rd)
  preserve-allsafe-plug {F = F-inl} (allsafe-inl allsafe-M) rd = allsafe-inl (preserve-allsafe allsafe-M rd)
  preserve-allsafe-plug {F = F-inr} (allsafe-inr allsafe-M) rd = allsafe-inr (preserve-allsafe allsafe-M rd)
  preserve-allsafe-plug {F = F-case M N} (allsafe-case allsafe-L allsafe-M allsafe-N) rd = allsafe-case (preserve-allsafe allsafe-L rd) allsafe-M allsafe-N
  preserve-allsafe-plug {F = F-cast c} (allsafe-cast-same-ℓ safe eq allsafe-M) rd = allsafe-cast-same-ℓ safe eq (preserve-allsafe allsafe-M rd)
  preserve-allsafe-plug {F = F-cast c} (allsafe-cast-diff-ℓ neq allsafe-M) rd = allsafe-cast-diff-ℓ neq (preserve-allsafe allsafe-M rd)

  preserve-allsafe allsafe (ξ rd) = preserve-allsafe-plug allsafe rd
  preserve-allsafe allsafe ξ-blame = allsafe-blame-diff-ℓ (plug-blame-allsafe-inv allsafe)
  -- Need to prove substitution preserves `CR<:` .
  preserve-allsafe (allsafe-· (allsafe-ƛ allsafe-N) allsafe-W) (β v) = substitution-allsafe allsafe-N allsafe-W
  preserve-allsafe allsafe δ = allsafe-prim
  preserve-allsafe (allsafe-if _ allsafe-M _) β-if-true = allsafe-M
  preserve-allsafe (allsafe-if _ _ allsafe-M′) β-if-false = allsafe-M′
  preserve-allsafe (allsafe-fst (allsafe-cons allsafe-M _)) (β-fst _ _) = allsafe-M
  preserve-allsafe (allsafe-snd (allsafe-cons _ allsafe-N)) (β-snd _ _) = allsafe-N
  preserve-allsafe (allsafe-case (allsafe-inl allsafe) allsafe-M _) (β-caseL x) = allsafe-· allsafe-M allsafe
  preserve-allsafe (allsafe-case (allsafe-inr allsafe) _ allsafe-N) (β-caseR x) = allsafe-· allsafe-N allsafe
  preserve-allsafe (allsafe-cast-same-ℓ safe eq allsafe) (cast v {a}) = applyCast-pres-allsafe-same-ℓ a eq safe allsafe
  preserve-allsafe (allsafe-cast-diff-ℓ neq allsafe) (cast v {a}) = applyCast-pres-allsafe-diff-ℓ a neq allsafe
  -- CR<: (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩
  preserve-allsafe (allsafe-· (allsafe-cast-same-ℓ safe eq allsafe-V) allsafe-W) (fun-cast {c = c} vV vW {x}) =
    -- Here we expect a proof that `labC c ≡ labC (dom c x)` , where `c` is a function cast.
    let dom-eq = subst-eq (λ □ → □ ≡ just _) (domLabEq c x) eq in
    let cod-eq = subst-eq (λ □ → □ ≡ just _) (codLabEq c x) eq in
      allsafe-cast-same-ℓ (codSafe safe x) cod-eq (allsafe-· allsafe-V (allsafe-cast-same-ℓ (domSafe safe x) dom-eq allsafe-W))
  preserve-allsafe (allsafe-· (allsafe-cast-diff-ℓ neq allsafe-V) allsafe-W) (fun-cast {c = c} vV vW {x}) =
    let dom-neq = subst-eq (λ □ → □ ≢ just _) (domLabEq c x) neq in
    let cod-neq = subst-eq (λ □ → □ ≢ just _) (codLabEq c x) neq in
      allsafe-cast-diff-ℓ cod-neq (allsafe-· allsafe-V (allsafe-cast-diff-ℓ dom-neq allsafe-W))
  preserve-allsafe (allsafe-fst (allsafe-cast-same-ℓ safe eq allsafe-V)) (fst-cast {c = c} vV {x}) =
    let fst-eq = subst-eq (λ □ → □ ≡ just _) (fstLabEq c x) eq in
      allsafe-cast-same-ℓ (fstSafe safe x) fst-eq (allsafe-fst allsafe-V)
  preserve-allsafe (allsafe-fst (allsafe-cast-diff-ℓ neq allsafe-V)) (fst-cast {c = c} vV {x}) =
    let fst-neq = subst-eq (λ □ → □ ≢ just _) (fstLabEq c x) neq in
      allsafe-cast-diff-ℓ fst-neq (allsafe-fst allsafe-V)
  preserve-allsafe (allsafe-snd (allsafe-cast-same-ℓ safe eq allsafe-V)) (snd-cast {c = c} vV {x}) =
    let snd-eq = subst-eq (λ □ → □ ≡ just _) (sndLabEq c x) eq in
      allsafe-cast-same-ℓ (sndSafe safe x) snd-eq (allsafe-snd allsafe-V)
  preserve-allsafe (allsafe-snd (allsafe-cast-diff-ℓ neq allsafe-V)) (snd-cast {c = c} vV {x}) =
    let snd-neq = subst-eq (λ □ → □ ≢ just _) (sndLabEq c x) neq in
      allsafe-cast-diff-ℓ snd-neq (allsafe-snd allsafe-V)
  preserve-allsafe (allsafe-case (allsafe-cast-same-ℓ safe eq allsafe-V) allsafe-W₁ allsafe-W₂) (case-cast {c = c} vV {x}) =
    let inl-eq = subst-eq (λ □ → □ ≡ just _) (inlLabEq c x) eq in
    let inr-eq = subst-eq (λ □ → □ ≡ just _) (inrLabEq c x) eq in
      allsafe-case allsafe-V (allsafe-ƛ (allsafe-· (rename-pres-allsafe S_ allsafe-W₁) (allsafe-cast-same-ℓ (inlSafe safe x) inl-eq allsafe-var)))
                             (allsafe-ƛ (allsafe-· (rename-pres-allsafe S_ allsafe-W₂) (allsafe-cast-same-ℓ (inrSafe safe x) inr-eq allsafe-var)))
  preserve-allsafe (allsafe-case (allsafe-cast-diff-ℓ neq allsafe-V) allsafe-W₁ allsafe-W₂) (case-cast {c = c} vV {x}) =
    let inl-neq = subst-eq (λ □ → □ ≢ just _) (inlLabEq c x) neq in
    let inr-neq = subst-eq (λ □ → □ ≢ just _) (inrLabEq c x) neq in
      allsafe-case allsafe-V (allsafe-ƛ (allsafe-· (rename-pres-allsafe S_ allsafe-W₁) (allsafe-cast-diff-ℓ inl-neq allsafe-var)))
                             (allsafe-ƛ (allsafe-· (rename-pres-allsafe S_ allsafe-W₂) (allsafe-cast-diff-ℓ inr-neq allsafe-var)))
