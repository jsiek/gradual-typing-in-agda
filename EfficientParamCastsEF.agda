open import Types
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

  This module provides an alternative reduction relation for the
  Parameterized Cast Calculus that ensures space efficiency.  It
  accomplishes this by merging adjacent casts using a compose
  operation that must be provided by the client of the module.

  This version uses mutually-recursive evaluation contexts, E and F,
  to ensure the merging of casts happens at the right time.

-}

module EfficientParamCastsEF
  (Cast : Type → Set)
  (Inert : ∀{A} → Cast A → Set)
  (Active : ∀{A} → Cast A → Set)  
  (ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c)
  where

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  {-

   The notion of Value changes to only allow a single cast in a value.
   So a value is a simple value (no cast) with an optional cast around it.

  -}

  data Value : ∀ {Γ A} → Γ ⊢ A → Set
  
  data SimpleValue : ∀ {Γ A} → Γ ⊢ A → Set where

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        -----------------
      → SimpleValue (ƛ N)

    V-const : ∀ {Γ} {A : Type} {k : rep A} {f : Prim A}
        ------------------------------
      → SimpleValue {Γ} {A} (($ k){f})

    V-pair : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V → Value W
        ----------------------
      → SimpleValue (cons V W)

    V-inl : ∀ {Γ A B} {V : Γ ⊢ A}
      → Value V
        --------------------------------
      → SimpleValue {Γ} {A `⊎ B} (inl V)

    V-inr : ∀ {Γ A B} {V : Γ ⊢ B}
      → Value V
        --------------------------------
      → SimpleValue {Γ} {A `⊎ B} (inr V)


  data Value where
    S-val : ∀ {Γ A}{V : Γ ⊢ A}
      → SimpleValue V
        -------------
      → Value V

    V-cast : ∀ {Γ : Context} {A B : Type} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        {i : Inert c}
      → SimpleValue V
        ---------------
      → Value (V ⟨ c ⟩)

  simple⋆ : ∀ {Γ A} → (M : Γ ⊢ A) → (SimpleValue M) → A ≢ ⋆
  simple⋆ .(ƛ _) V-ƛ = λ ()
  simple⋆ ((ParamCastCalculus.$ k) {P-Base}) V-const = λ ()
  simple⋆ ((ParamCastCalculus.$ k) {P-Fun f}) V-const = λ ()
  simple⋆ .(cons _ _) (V-pair x x₁) = λ ()
  simple⋆ .(inl _) (V-inl x) = λ ()
  simple⋆ .(inr _) (V-inr x) = λ ()

  canonical⋆ : ∀ {Γ} → (M : Γ ⊢ ⋆) → (Value M)
             → Σ[ A ∈ Type ] Σ[ M' ∈ (Γ ⊢ A) ] Σ[ c ∈ (Cast (A ⇒ ⋆)) ]
                 Inert c × (M ≡ (M' ⟨ c ⟩)) × A ≢ ⋆
  canonical⋆ .($ _) (S-val (V-const {f = ()}))
  canonical⋆ (M ⟨ _ ⟩) (V-cast{A = A}{B = B}{V = V}{c = c}{i = i} v) =
    ⟨ A , ⟨ V , ⟨ c , ⟨ i , ⟨ refl , simple⋆ M v ⟩ ⟩ ⟩ ⟩ ⟩

  simple-base : ∀ {Γ ι} → (M : Γ ⊢ ` ι) → SimpleValue M 
     → Σ[ k ∈ rep-base ι ] Σ[ f ∈ Prim (` ι) ] M ≡ ($ k){f}
  simple-base (($ k){f}) V-const = ⟨ k , ⟨ f , refl ⟩ ⟩
  
  {-

   The Reduction inner module has an additional parameter, the compose
   function.

   -}

  module Reduction
    (applyCast : ∀{Γ A B} → (M : Γ ⊢ A) → Value M → (c : Cast (A ⇒ B))
               → ∀ {a : Active c} → Γ ⊢ B)
{-
    (funCast : ∀{Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
             → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B')
-}
    (funSrc : ∀{A A' B' Γ}
            → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → (M : Γ ⊢ A) → SimpleValue M
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂)
    (dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁))
    (cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B'))
    (fstCast : ∀{Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
             → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A')
    (sndCast : ∀{Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
             → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B')
    (caseCast : ∀{Γ A A' B' C} → (L : Γ ⊢ A) → SimpleValue L
              → (c : Cast (A ⇒ (A' `⊎ B')))
              → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C)
    (baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → A ≢ ⋆ → ¬ Inert c)
    (compose : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
             → Cast (A ⇒ C))
    where

    {-


    -}

    data ECtx : {Γ : Context} → Type → Type → Set 
    data FCtx : {Γ : Context} → Type → Type → Set 
    
    data ECtx where

      E-F : ∀{Γ}{A B} → FCtx {Γ} A B → ECtx {Γ} A B
      {- todo: restrict cast to be identity free -}
      E-Cast : ∀{Γ}{A B C}
        → Cast (A ⇒ B)
        → FCtx {Γ} B C
        → ECtx {Γ} A C


    data FCtx where

      F-hole : ∀{Γ}{A} → FCtx {Γ} A A

      F-·₁ : ∀ {Γ A B C}
        → Γ ⊢ A
        → ECtx {Γ} B C
        → FCtx {Γ} (A ⇒ B) C

      F-·₂ : ∀ {Γ A B C}
        → (M : Γ ⊢ A ⇒ B) → ∀{v : Value {Γ} M}
        → ECtx {Γ} B C
        → FCtx {Γ} A C

      F-if : ∀ {Γ A B}
        → Γ ⊢ A
        → Γ ⊢ A
        → ECtx {Γ} A B
        → FCtx {Γ} (` 𝔹) B

      F-×₁ : ∀ {Γ A B C}
        → Γ ⊢ A
        → ECtx {Γ} (A `× B) C
        → FCtx {Γ} B C

      F-×₂ : ∀ {Γ A B C}
        → Γ ⊢ B
        → ECtx {Γ} (A `× B) C
        → FCtx {Γ} A C

      F-fst : ∀ {Γ A B C}
        → ECtx {Γ} A C
        → FCtx {Γ} (A `× B) C

      F-snd : ∀ {Γ A B C}
        → ECtx {Γ} B C
        → FCtx {Γ} (A `× B) C

      F-inl : ∀ {Γ A B C}
        → ECtx {Γ} (A `⊎ B) C
        → FCtx {Γ} A C

      F-inr : ∀ {Γ A B C}
        → ECtx {Γ} (A `⊎ B) C
        → FCtx {Γ} B C

      F-case : ∀ {Γ A B C D}
        → Γ ⊢ A ⇒ C
        → Γ ⊢ B ⇒ C
        → ECtx {Γ} C D
        → FCtx {Γ} (A `⊎ B) D


    plug-f : ∀{Γ A B} → Γ ⊢ A → FCtx {Γ} A B → Γ ⊢ B
    
    plug : ∀{Γ A B} → Γ ⊢ A → ECtx {Γ} A B → Γ ⊢ B
    plug M (E-F F) = plug-f M F
    plug M (E-Cast c F) = plug-f (M ⟨ c ⟩) F

    plug-f L (F-hole)        = L
    plug-f L (F-·₁ M E)      = plug (L · M) E
    plug-f M (F-·₂ L E)      = plug (L · M) E
    plug-f L (F-if M N E)    = plug (if L M N) E
    plug-f L (F-×₁ M E)      = plug (cons M L) E
    plug-f M (F-×₂ L E)      = plug (cons M L) E
    plug-f M (F-fst E)      = plug (fst M) E
    plug-f M (F-snd E)      = plug (snd M) E
    plug-f M (F-inl E)      = plug (inl M) E
    plug-f M (F-inr E)      = plug (inr M) E
    plug-f L (F-case M N E) = plug (case L M N) E

    infix 2 _—→E_
    data _—→E_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

      β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
        → Value W
          -------------------------------
        → (ƛ N) · W —→E N [ W ]

      δ : ∀ {Γ : Context} {A B} {f : rep A → rep B} {k : rep A} {ab} {a} {b}
          --------------------------------------------------------------
        → ($_ {Γ}{A ⇒ B} f {ab}) · (($ k){a}) —→E ($ (f k)){b}

      β-if-true : ∀{Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
          --------------------------------------
        → if (($ true){f}) M N —→E M

      β-if-false : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}
          ---------------------
        → if (($ false){f}) M N —→E N

      β-fst : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
        → Value V → Value W
          --------------------
        → fst (cons V W) —→E V

      β-snd :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
        → Value V → Value W
          --------------------
        → snd (cons V W) —→E W

      β-caseL : ∀ {Γ A B C} {V : Γ ⊢ A} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
        → Value V
          --------------------------
        → case (inl V) L M —→E L · V

      β-caseR : ∀ {Γ A B C} {V : Γ ⊢ B} {L : Γ ⊢ A ⇒ C} {M : Γ ⊢ B ⇒ C}
        → Value V
          --------------------------
        → case (inr V) L M —→E M · V

      fun-cast : ∀ {Γ A' B' A₁ A₂} {V : Γ ⊢ A₁ ⇒ A₂} {W : Γ ⊢ A'}
          {c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))}
        → (v : SimpleValue V) → Value W → {i : Inert c}
          -------------------------------------------------------------
        → (V ⟨ c ⟩) · W —→E (V · (W ⟨ dom c i ⟩)) ⟨ cod c i ⟩

      fst-cast : ∀ {Γ A A' B'} {V : Γ ⊢ A}
          {c : Cast (A ⇒ (A' `× B'))}
        → (v : SimpleValue V) → {i : Inert c}
          --------------------------------------------
        → fst (V ⟨ c ⟩) —→E fstCast V v c {i}

      snd-cast : ∀ {Γ A A' B'} {V : Γ ⊢ A}
          {c : Cast (A ⇒ (A' `× B'))}
        → (v : SimpleValue V) → {i : Inert c}
          ---------------------------------------------
        → snd (V ⟨ c ⟩) —→E sndCast V v c {i}

      case-cast : ∀ { Γ A A' B' C} {V : Γ ⊢ A}
          {W : Γ ⊢ A' ⇒ C } {W' : Γ ⊢ B' ⇒ C}
          {c : Cast (A ⇒ (A' `⊎ B'))}
        → (v : SimpleValue V) → {i : Inert c}
          ---------------------------------------------------------
        → case (V ⟨ c ⟩) W W' —→E caseCast V v c {i} W W'


    infix 2 _—→F_
    data _—→F_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
    
      cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
        → (v : Value V) → {a : Active c}
          ----------------------------
        → V ⟨ c ⟩ —→F applyCast V v c {a}

      compose-casts : ∀{Γ A B C} {M : Γ ⊢ A }
          {c : Cast (A ⇒ B)} {d : Cast (B ⇒ C)}
          ------------------------------------------
        → (M ⟨ c ⟩) ⟨ d ⟩ —→F M ⟨ compose c d ⟩


    infix 2 _—→_
    data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

      ξ-F : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : FCtx A B}
        → M —→F M′
          --------------------------
        → plug-f M F —→ plug-f M′ F

      ξ-E : ∀ {Γ A B} {M M′ : Γ ⊢ A} {E : ECtx A B}
        → M —→E M′
          --------------------------
        → plug M E —→ plug M′ E

      ξ-blame : ∀ {Γ A B} {E : ECtx {Γ} A B} {ℓ}
          ---------------------------
        → plug (blame ℓ) E —→ blame ℓ

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

    extend-ctx-e : ∀{Γ}{A B C} → ECtx {Γ} A B → FCtx {Γ} B C → ECtx {Γ} A C
    extend-ctx-f : ∀{Γ}{A B C} → FCtx {Γ} A B → FCtx {Γ} B C → FCtx {Γ} A C

    extend-ctx-e (E-F F) F′ =
      let F′′ = extend-ctx-f F F′ in E-F F′′
    extend-ctx-e (E-Cast c F) F′ =
      let F′′ = extend-ctx-f F F′ in E-Cast c F′′
    
    extend-ctx-f F-hole F′ = F′
    extend-ctx-f (F-·₁ M E) F′ =
      let E′ = extend-ctx-e E F′ in F-·₁ M E′
    extend-ctx-f (F-·₂ L {v} E) F′ =
      let E′ = extend-ctx-e E F′ in F-·₂ L {v} E′
    extend-ctx-f (F-if M N E) F′ =
      let E′ = extend-ctx-e E F′ in F-if M N E′
    extend-ctx-f (F-×₁ M E) F′ =
      let E′ = extend-ctx-e E F′ in F-×₁ M E′
    extend-ctx-f (F-×₂ M E) F′ =
      let E′ = extend-ctx-e E F′ in F-×₂ M E′
    extend-ctx-f (F-fst E) F′ =
       let E′ = extend-ctx-e E F′ in F-fst E′
    extend-ctx-f (F-snd E) F′ =
       let E′ = extend-ctx-e E F′ in F-snd E′
    extend-ctx-f (F-inl E) F′ =
       let E′ = extend-ctx-e E F′ in F-inl E′
    extend-ctx-f (F-inr E) F′ =
       let E′ = extend-ctx-e E F′ in F-inr E′
    extend-ctx-f (F-case M N E) F′ =
       let E′ = extend-ctx-e E F′ in F-case M N E′

    extend-plug-e : ∀{Γ}{A B C} {M : Γ ⊢ A} {E : ECtx {Γ} A B}{F : FCtx {Γ}B C}
       → plug M (extend-ctx-e E F) ≡ plug-f (plug M E) F
    extend-plug-f : ∀{Γ}{A B C}{M : Γ ⊢ A} {F₁ : FCtx {Γ} A B}{F₂ : FCtx {Γ}B C}
       → plug-f M (extend-ctx-f F₁ F₂) ≡ plug-f (plug-f M F₁) F₂
                  
    extend-plug-e {M = M} {E-F F′}{F} =
       extend-plug-f {M = M} {F′} {F}
    extend-plug-e {M = M} {E-Cast c F′}{F} =
       extend-plug-f {M = M ⟨ c ⟩} {F′} {F}

    extend-plug-f {M = M} {F-hole} {F₂} = refl
    extend-plug-f {M = M} {F-·₁ N E} {F₂} =
       extend-plug-e {M = M · N} {E} {F₂}
    extend-plug-f {M = M} {F-·₂ L {v} E} {F₂} =
       extend-plug-e {M = L · M} {E} {F₂}
    extend-plug-f {M = M} {F-if L N E} {F₂} =
       extend-plug-e {M = if M L N} {E} {F₂}
    extend-plug-f {M = M} {F-×₁ N E} {F₂} =
       extend-plug-e {M = cons N M} {E} {F₂}
    extend-plug-f {M = M} {F-×₂ N E} {F₂} =
       extend-plug-e {M = cons M N} {E} {F₂}
    extend-plug-f {M = M} {F-fst E} {F₂} =
       extend-plug-e {M = fst M} {E} {F₂}
    extend-plug-f {M = M} {F-snd E} {F₂} =
       extend-plug-e {M = snd M} {E} {F₂}
    extend-plug-f {M = M} {F-inl E} {F₂} =
       extend-plug-e {M = inl M} {E} {F₂}
    extend-plug-f {M = M} {F-inr E} {F₂} =
       extend-plug-e {M = inr M} {E} {F₂}
    extend-plug-f {M = M} {F-case L N E} {F₂} =
       extend-plug-e {M = case M L N} {E} {F₂}

    decompose : ∀{B} → (M : ∅ ⊢ B)
       → ((Σ[ A ∈ Type ] Σ[ E ∈ ECtx A B ] Σ[ L ∈ (∅ ⊢ A) ]
            ((M ≡ plug L E) × (Σ[ N ∈ (∅ ⊢ A) ] (L —→E N))))
           ⊎ (Σ[ A ∈ Type ] Σ[ F ∈ FCtx A B ] Σ[ L ∈ (∅ ⊢ A) ]
            ((M ≡ plug-f L F) × (Σ[ N ∈ (∅ ⊢ A) ] (L —→F N)))))
         ⊎ ((Σ[ A ∈ Type ] Σ[ E ∈ ECtx A B ] Σ[ ℓ ∈ Label ]
             (M ≡ plug (blame ℓ) E))
           ⊎ Value M)
    decompose (ƛ M) = inj₂ (inj₂ (S-val V-ƛ))
    decompose (M₁ · M₂)
        with decompose M₁
    ... | inj₁ (inj₁ (⟨ A , (⟨ E , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-·₁ M₂ (E-F F-hole) in
          let eq = extend-plug-e {M = L}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₁ (inj₁ (⟨ A , (⟨ E′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₁ (inj₂ (⟨ A , (⟨ F , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-·₁ M₂ (E-F F-hole) in
          let eq = extend-plug-f {M = L}{F}{F′} in
          let F′′ = extend-ctx-f F F′ in
          inj₁ (inj₂ (⟨ A , (⟨ F′′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    decompose (M₁ · M₂) | inj₂ (inj₁ (⟨ A , (⟨ E , (⟨ ℓ , eq ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-·₁ M₂ (E-F F-hole) in
          let eq = extend-plug-e {M = blame ℓ}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₂ (inj₁ (⟨ A , (⟨ E′ , ⟨ ℓ , sym eq ⟩ ⟩) ⟩))
    decompose {B} (M₁ · M₂) | inj₂ (inj₂ vM₁)
        with decompose M₂
    ... | inj₁ (inj₁ (⟨ A , (⟨ E , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-·₂ M₁ {vM₁} (E-F F-hole) in
          let eq = extend-plug-e {M = L}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₁ (inj₁ (⟨ A , (⟨ E′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₁ (inj₂ (⟨ A , (⟨ F , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-·₂ M₁ {vM₁} (E-F F-hole) in
          let eq = extend-plug-f {M = L}{F}{F′} in
          let F′′ = extend-ctx-f F F′ in
          inj₁ (inj₂ (⟨ A , (⟨ F′′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₂ (inj₁ (⟨ A , (⟨ E , (⟨ ℓ , eq ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-·₂ M₁ {vM₁} (E-F F-hole) in
          let eq = extend-plug-e {M = blame ℓ}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₂ (inj₁ (⟨ A , (⟨ E′ , ⟨ ℓ , sym eq ⟩ ⟩) ⟩))
    decompose {B} (M₁ · M₂) | inj₂ (inj₂ vM₁) | inj₂ (inj₂ vM₂)
        with vM₁
    ... | S-val (V-ƛ {N = N}) =
          inj₁ (inj₁ (⟨ B , (⟨ E-F F-hole , (⟨ M₁ · M₂ , (⟨ refl ,
               (⟨ N [ M₂ ] , β vM₂ ⟩) ⟩) ⟩) ⟩) ⟩))
    ... | V-cast {V = V}{c}{i} v
        with funSrc c i V v
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ =
          inj₁ (inj₁ (⟨ B , (⟨ E-F F-hole , (⟨ M₁ · M₂ , (⟨ refl ,
               (⟨ (V · M₂ ⟨ dom c i ⟩) ⟨ cod c i ⟩ ,
                  fun-cast v vM₂ {i} ⟩) ⟩) ⟩) ⟩) ⟩))
    decompose {B} (M₁ · M₂) | inj₂ (inj₂ vM₁) | inj₂ (inj₂ vM₂)
        | S-val (V-const {A = A₁ ⇒ B}{k = k₁}{f = f₁})
        with vM₂
    ... | S-val (V-const {k = k₂} {f = f₂}) =
          inj₁ (inj₁ (⟨ B , (⟨ E-F F-hole , (⟨ M₁ · M₂ , (⟨ refl ,
               (⟨ $ k₁ k₂ , δ {ab = f₁}{a = f₂}{b = P-Fun2 f₁} ⟩) ⟩) ⟩) ⟩) ⟩))
    ... | V-cast {V = W}{c}{i} v = contradiction i (G f₁)
        where G : Prim (A₁ ⇒ B) → ¬ Inert c
              G (P-Fun f) ic = baseNotInert c (simple⋆ W v) ic


    decompose ($ k) = inj₂ (inj₂ (S-val V-const))
    decompose (if M₀ M₁ M₂) = {!!}
    decompose (cons M₀ M₁) = {!!}
    decompose {B₀} (fst {∅}{B₀}{B₁} M₀)
        with decompose M₀
    ... | inj₁ (inj₁ (⟨ A , (⟨ E , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-fst (E-F F-hole) in
          let eq = extend-plug-e {M = L}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₁ (inj₁ (⟨ A , (⟨ E′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₁ (inj₂ (⟨ A , (⟨ F , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-fst (E-F F-hole) in
          let eq = extend-plug-f {M = L}{F}{F′} in
          let F′′ = extend-ctx-f F F′ in
          inj₁ (inj₂ (⟨ A , (⟨ F′′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    decompose {B} (fst {∅}{B}{B₁} M)
        | inj₂ (inj₁ (⟨ A , (⟨ E , (⟨ ℓ , eq ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-fst (E-F F-hole) in
          let eq = extend-plug-e {M = blame ℓ}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₂ (inj₁ (⟨ A , (⟨ E′ , ⟨ ℓ , sym eq ⟩ ⟩) ⟩))
    decompose {B} (fst M) | inj₂ (inj₂ vM)
        with vM 
    ... | S-val (V-pair {V = L} vL vN) =
          inj₁ (inj₁ (⟨ B , (⟨ E-F F-hole , (⟨ fst M ,
                                  (⟨ refl , (⟨ L , β-fst vL vN ⟩) ⟩) ⟩) ⟩) ⟩))
    ... | V-cast {V = V}{c = c}{i = i} sv =
          let red = fst-cast {c = c} sv {i} in
          inj₁ (inj₁ (⟨ B , (⟨ E-F F-hole , (⟨ fst M ,
             (⟨ refl , (⟨ fstCast V sv c , red ⟩) ⟩) ⟩) ⟩) ⟩))
    decompose {B₁} (snd {∅}{B₀}{B₁} M₀)
        with decompose M₀
    ... | inj₁ (inj₁ (⟨ A , (⟨ E , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-snd (E-F F-hole) in
          let eq = extend-plug-e {M = L}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₁ (inj₁ (⟨ A , (⟨ E′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₁ (inj₂ (⟨ A , (⟨ F , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-snd (E-F F-hole) in
          let eq = extend-plug-f {M = L}{F}{F′} in
          let F′′ = extend-ctx-f F F′ in
          inj₁ (inj₂ (⟨ A , (⟨ F′′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    decompose {B₁} (snd {∅}{B}{B₁} M)
        | inj₂ (inj₁ (⟨ A , (⟨ E , (⟨ ℓ , eq ⟩) ⟩) ⟩))
          rewrite eq =
          let F′ = F-snd (E-F F-hole) in
          let eq = extend-plug-e {M = blame ℓ}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₂ (inj₁ (⟨ A , (⟨ E′ , ⟨ ℓ , sym eq ⟩ ⟩) ⟩))
    decompose {B} (snd M) | inj₂ (inj₂ vM)
        with vM 
    ... | S-val (V-pair {W = L} vL vN) =
          inj₁ (inj₁ (⟨ B , (⟨ E-F F-hole , (⟨ snd M ,
                                  (⟨ refl , (⟨ L , β-snd vL vN ⟩) ⟩) ⟩) ⟩) ⟩))
    ... | V-cast {V = V}{c = c}{i = i} sv =
          let red = snd-cast {c = c} sv {i} in
          inj₁ (inj₁ (⟨ B , (⟨ E-F F-hole , (⟨ snd M ,
             (⟨ refl , (⟨ sndCast V sv c , red ⟩) ⟩) ⟩) ⟩) ⟩))
    decompose (inl M₀)
        with decompose M₀
    ... | inj₁ (inj₁ (⟨ A , (⟨ E , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
        rewrite eq =
          let F′ = F-inl (E-F F-hole) in
          let eq = extend-plug-e {M = L}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₁ (inj₁ (⟨ A , (⟨ E′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₁ (inj₂ (⟨ A , (⟨ F , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
        rewrite eq =
          let F′ = F-inl (E-F F-hole) in
          let eq = extend-plug-f {M = L}{F}{F′} in
          let F′′ = extend-ctx-f F F′ in
          inj₁ (inj₂ (⟨ A , (⟨ F′′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₂ (inj₁ (⟨ A , (⟨ E , (⟨ ℓ , eq ⟩) ⟩) ⟩))
        rewrite eq =
          let F′ = F-inl (E-F F-hole) in
          let eq = extend-plug-e {M = blame ℓ}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₂ (inj₁ (⟨ A , (⟨ E′ , ⟨ ℓ , sym eq ⟩ ⟩) ⟩))
    ... | inj₂ (inj₂ vM) = inj₂ (inj₂ (S-val (V-inl vM)))
    decompose (inr M₀)
        with decompose M₀
    ... | inj₁ (inj₁ (⟨ A , (⟨ E , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
        rewrite eq =
          let F′ = F-inr (E-F F-hole) in
          let eq = extend-plug-e {M = L}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₁ (inj₁ (⟨ A , (⟨ E′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₁ (inj₂ (⟨ A , (⟨ F , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
        rewrite eq =
          let F′ = F-inr (E-F F-hole) in
          let eq = extend-plug-f {M = L}{F}{F′} in
          let F′′ = extend-ctx-f F F′ in
          inj₁ (inj₂ (⟨ A , (⟨ F′′ , (⟨ L , ⟨ sym eq , ⟨ N , M—→N ⟩ ⟩ ⟩) ⟩) ⟩))
    ... | inj₂ (inj₁ (⟨ A , (⟨ E , (⟨ ℓ , eq ⟩) ⟩) ⟩))
        rewrite eq =
          let F′ = F-inr (E-F F-hole) in
          let eq = extend-plug-e {M = blame ℓ}{E}{F′} in
          let E′ = extend-ctx-e E F′ in
          inj₂ (inj₁ (⟨ A , (⟨ E′ , ⟨ ℓ , sym eq ⟩ ⟩) ⟩))
    ... | inj₂ (inj₂ vM) = inj₂ (inj₂ (S-val (V-inr vM)))
    decompose (case M₀ M₁ M₂) = {!!}
    decompose (M ⟨ c ⟩) {- UNDER CONSTRUCTION -Jeremy -}
        with decompose M
    ... | inj₁ (inj₁ (⟨ B , (⟨ E , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          {!!}
    ... | inj₁ (inj₂ (⟨ B , (⟨ F , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          {!!}
    ... | inj₂ (inj₁ (⟨ B , (⟨ E , (⟨ ℓ , eq ⟩) ⟩) ⟩))
          rewrite eq =
          {!!}
    ... | inj₂ (inj₂ vM) = {!!}
    decompose {A} (blame ℓ) =
       inj₂ (inj₁ (⟨ A , (⟨ (E-F F-hole) , (⟨ ℓ , refl ⟩) ⟩) ⟩))
    

    progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
    progress {A} M
        with decompose M
    ... | inj₁ (inj₁ (⟨ B , (⟨ E , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          step (ξ-E {E = E} M—→N)
    progress {A} M |
          inj₁ (inj₂ (⟨ B , (⟨ F , (⟨ L , (⟨ eq , (⟨ N , M—→N ⟩) ⟩) ⟩) ⟩) ⟩))
          rewrite eq =
          step (ξ-F {F = F} M—→N)    
    progress {A} M | inj₂ (inj₁ (⟨ B , (⟨ E , (⟨ ℓ , eq ⟩) ⟩) ⟩))
          rewrite eq =
          step (ξ-blame {∅}{B}{A}{E}{ℓ})
    progress {A} M | inj₂ (inj₂ vM) = done vM
    
