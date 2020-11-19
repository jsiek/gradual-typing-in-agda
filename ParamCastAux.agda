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

{-

  This modules defines reduction for the Parameterized Cast Calculus
  and provides a proof of progress. Preservation is guaranteed in the
  way the reduction relation is defined and checked by Agda.

-}


module ParamCastAux (pcs : PreCastStruct) where

  open PreCastStruct pcs
  
  import ParamCastCalculus
  open ParamCastCalculus Cast Inert

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

    -- A normal cast like M ⟨ c ⟩ cannot be a value. Only a wrap V ⟨ i ⟩ is, when V is Value.
    V-wrap : ∀ {Γ : Context} {A B : Type} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
      → Value V → (i : Inert c)
        ---------------
      → Value (V ⟪ i ⟫)


  {-

  A value of type ⋆ must be of the form M ⟨ c ⟩ where c is inert cast.

  -}
  canonical⋆ : ∀ {Γ}
    → (V : Γ ⊢ ⋆) → (Value V)
      --------------------------
    → ∃[ A ] ∃[ V′ ] (Σ[ c ∈ Cast (A ⇒ ⋆) ] Σ[ i ∈ Inert c ] (V ≡ (V′ ⟪ i ⟫)))
  canonical⋆ _ (V-const {k = ()})
  canonical⋆ _ (V-wrap {Γ} {A} {B} {V} {c} v i) = ⟨ A , ⟨ V , ⟨ c , ⟨ i , refl ⟩ ⟩ ⟩ ⟩

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
      In order to satisfy progress, we need to consider the case M ⟪ i ⟫
      when M is not a Value.
    -}
    F-wrap : ∀ {Γ A B} {c : Cast (A ⇒ B)}
      → (i : Inert c)
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
  plug M (F-wrap i) = M ⟪ i ⟫

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

  {- Here are a few inversion lemmas for `plug` : -}
  plug-inv-fst : ∀ {Γ A B C} {M : Γ ⊢ A `× B} {N : Γ ⊢ C}
    → (F : Frame C A)
    → plug N F ≡ fst M
      ----------------------------------------------------------
    → Σ[ eq ∈ C ≡ A `× B ] (subst-eq (λ □ → Frame □ A) eq F ≡ F-fst) × (subst-eq (λ □ → Γ ⊢ □) eq N ≡ M)
  plug-inv-fst F-fst refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

  plug-inv-snd : ∀ {Γ A B C} {M : Γ ⊢ A `× B} {N : Γ ⊢ C}
    → (F : Frame C B)
    → plug N F ≡ snd M
      ----------------------------------------------------------
    → Σ[ eq ∈ C ≡ A `× B ] (subst-eq (λ □ → Frame □ B) eq F ≡ F-snd) × (subst-eq (λ □ → Γ ⊢ □) eq N ≡ M)
  plug-inv-snd F-snd refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

  plug-inv-cons₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {L L′ : Γ ⊢ B}
    → plug L (F-×₁ M) ≡ cons M′ L′
      -----------------------------
    → (L ≡ L′) × (M ≡ M′)
  plug-inv-cons₁ refl = ⟨ refl , refl ⟩

  plug-inv-cons₂ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {L L′ : Γ ⊢ B}
    → plug M (F-×₂ L) ≡ cons M′ L′
      -----------------------------
    → (L ≡ L′) × (M ≡ M′)
  plug-inv-cons₂ refl = ⟨ refl , refl ⟩

  plug-inv-inl : ∀ {Γ A B} {M M′ : Γ ⊢ A}
    → plug M F-inl ≡ inl {B = B} M′
      ------------------------------
    → M ≡ M′
  plug-inv-inl refl = refl

  plug-inv-inr : ∀ {Γ A B} {M M′ : Γ ⊢ B}
    → plug M F-inr ≡ inr {A = A} M′
      ------------------------------
    → M ≡ M′
  plug-inv-inr refl = refl

  plug-inv-if : ∀ {Γ A} {L Lᵒ : Γ ⊢ ` 𝔹} {M Mᵒ N Nᵒ : Γ ⊢ A}
    → plug L (F-if M N) ≡ if Lᵒ Mᵒ Nᵒ
      --------------------------------
    → (L ≡ Lᵒ) × (M ≡ Mᵒ) × (N ≡ Nᵒ)
  plug-inv-if refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

  {-
    Note that in the first lemma the source type can be different (A might not be the same as Aᵒ).
    When used, first perform inversion by the 1st lemma using with-abstraction and then the 2nd.
  -}
  plug-inv-wrap-M : ∀ {Γ A Aᵒ B} {M : Γ ⊢ A} {Mᵒ : Γ ⊢ Aᵒ} {c : Cast (A ⇒ B)} {cᵒ : Cast (Aᵒ ⇒ B)} {i : Inert c} {iᵒ : Inert cᵒ}
    → plug M (F-wrap i) ≡ Mᵒ ⟪ iᵒ ⟫
      -----------------------------------------------------
    → Σ[ eqA ∈ A ≡ Aᵒ ] subst-eq (λ A → Γ ⊢ A) eqA M ≡ Mᵒ
  plug-inv-wrap-M refl = ⟨ refl , refl ⟩

  plug-inv-wrap-i : ∀ {Γ A B} {M Mᵒ : Γ ⊢ A} {c cᵒ : Cast (A ⇒ B)} {i : Inert c} {iᵒ : Inert cᵒ}
    → plug M (F-wrap i) ≡ Mᵒ ⟪ iᵒ ⟫
      -------------------------------------------------------
    → Σ[ eqc ∈ c ≡ cᵒ ] subst-eq (λ c → Inert c) eqc i ≡ iᵒ
  plug-inv-wrap-i refl = ⟨ refl , refl ⟩
