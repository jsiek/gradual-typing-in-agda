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


  {- Lemmas about renaming and substitution: -}
  {- Two renamings ρ , ω satisfy `RenameIso` means that two isomorphic DeBruijn indices
     after renaming are also isomorphic. -}
  RenameIso : ∀ {Γ Γ′ Δ Δ′} → (ρ : Rename Γ Δ) → (ω : Rename Γ′ Δ′) → Set
  RenameIso {Γ} {Γ′} {Δ} {Δ′} ρ ω =
    ∀ {A B} {x : Γ ∋ A} {y : Γ′ ∋ B} → ∋→ℕ x ≡ ∋→ℕ y → ∋→ℕ (ρ x) ≡ ∋→ℕ (ω y)

  S-iso : ∀ {Γ Γ′ A A′}
    → RenameIso {Γ} {Γ′} {Γ , A} {Γ′ , A′} S_ S_
  S-iso eq = cong suc eq

  open import Data.Nat.Properties using (suc-injective)
  -- Extending two related renamings ρ , ω preserves `RenameIso`.
  ext-pres-RenameIso : ∀ {Γ Γ′ Δ Δ′} {B B′} {ρ : Rename Γ Δ} {ω : Rename Γ′ Δ′}
    → RenameIso ρ ω
      -----------------------------------------------------------
    → RenameIso {Γ , B} {Γ′ , B′} {Δ , B}  {Δ′ , B′} (ext ρ) (ext ω)
  ext-pres-RenameIso f {x = Z} {Z} eq = refl
  ext-pres-RenameIso f {x = S x} {S y} eq = let ρx≡ωy = f (suc-injective eq) in cong suc ρx≡ωy

  private
    data _≈_ : ∀ {Γ Δ} → Rename Γ Δ → Subst Δ Γ → Set where

      ≈-base : ∀ {Γ A} → _≈_ {Γ , A} {Γ , A , A} (ext S_) (subst-zero (` Z))

      ≈-ext : ∀ {Γ Δ B} {ρ : Rename Γ Δ} {σ : Subst Δ Γ}
        → ρ ≈ σ
          ------------------
        → _≈_ {Γ , B} {Δ , B} (ext ρ) (exts σ)

    ≈-var-id : ∀ {Γ Δ X} {ρ : Rename Γ Δ} {σ : Subst Δ Γ}
      → (x : Γ ∋ X)
      → ρ ≈ σ
        ---------------
      → ` x ≡ σ (ρ x)
    ≈-var-id Z ≈-base = refl
    ≈-var-id (S x) ≈-base = refl
    ≈-var-id Z (≈-ext r) = refl
    ≈-var-id (S x) (≈-ext r) = cong (λ M → rename S_ M) (≈-var-id x r)

    cong₃ : ∀ {A B C X : Set} (f : A → B → C → X) {u v w x y z}
      → u ≡ x → v ≡ y → w ≡ z → f u v w ≡ f x y z
    cong₃ f refl refl refl = refl

    {- If renaming ρ and substitution σ satisfy ρ ≈ σ, then M ≡ σ (ρ M) . -}
    subst-var-eq : ∀ {Γ Δ X} {ρ : Rename Γ Δ} {σ : Subst Δ Γ}
      → (M : Γ ⊢ X)
      → ρ ≈ σ
        --------------------------
      → M ≡ subst σ (rename ρ M)
    subst-var-eq (` x) r = ≈-var-id x r
    subst-var-eq (ƛ M) r = cong ƛ_ (subst-var-eq M (≈-ext r))
    subst-var-eq (M · N) r = cong₂ _·_ (subst-var-eq M r) (subst-var-eq N r)
    subst-var-eq ($ x) r = refl
    subst-var-eq (if L M N) r = cong₃ if (subst-var-eq L r) (subst-var-eq M r) (subst-var-eq N r)
    subst-var-eq (cons M N) r = cong₂ cons (subst-var-eq M r) (subst-var-eq N r)
    subst-var-eq (fst M) r = cong fst (subst-var-eq M r)
    subst-var-eq (snd M) r = cong snd (subst-var-eq M r)
    subst-var-eq (inl M) r = cong inl (subst-var-eq M r)
    subst-var-eq (inr M) r = cong inr (subst-var-eq M r)
    subst-var-eq (case L M N) r = cong₃ case (subst-var-eq L r) (subst-var-eq M (≈-ext r)) (subst-var-eq N (≈-ext r))
    subst-var-eq (M ⟨ c ⟩) r = cong (λ □ → □ ⟨ c ⟩) (subst-var-eq M r)
    subst-var-eq (M ⟪ i ⟫) r = cong (λ □ → □ ⟪ i ⟫) (subst-var-eq M r)
    subst-var-eq (blame ℓ) r = refl

  substitution-Z-eq : ∀ {Γ A B}
    → (M : Γ , A ⊢ B)
      --------------------------------
    → M ≡ rename (ext S_) M [ ` Z ]
  substitution-Z-eq M = subst-var-eq M ≈-base

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
      → (M : Γ ⊢ A)
      → Value M
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
      → Γ , A ⊢ C
      → Γ , B ⊢ C
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
  plug L (F-×₁ M vM)   = cons M L
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
       case M l r


  {- Plug inversion lemmas: -}
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


  plug-inv-cons₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {L L′ : Γ ⊢ B}{vM : Value M}
    → plug L (F-×₁ M vM) ≡ cons M′ L′
      -----------------------------
    → (L ≡ L′) × (M ≡ M′)
  plug-inv-cons₁ refl = ⟨ refl , refl ⟩

  plug-inv-cons₂ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {L L′ : Γ ⊢ B}
    → plug M (F-×₂ L) ≡ cons M′ L′
      -----------------------------
    → (L ≡ L′) × (M ≡ M′)
  plug-inv-cons₂ refl = ⟨ refl , refl ⟩

  plug-inv-app₁ : ∀ {Γ A Aᵒ B} {L : Γ ⊢ A ⇒ B} {Lᵒ : Γ ⊢ Aᵒ ⇒ B} {M : Γ ⊢ A} {Mᵒ : Γ ⊢ Aᵒ}
    → plug L (F-·₁ M) ≡ Lᵒ · Mᵒ
      --------------------------
    → Σ[ eqA ∈ A ≡ Aᵒ ] (subst-eq (λ A → Γ ⊢ A ⇒ B) eqA L ≡ Lᵒ) × (subst-eq (λ A → Γ ⊢ A) eqA M ≡ Mᵒ)
  plug-inv-app₁ refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

  plug-inv-app₂ : ∀ {Γ A Aᵒ B} {L : Γ ⊢ A ⇒ B} {Lᵒ : Γ ⊢ Aᵒ ⇒ B} {M : Γ ⊢ A} {Mᵒ : Γ ⊢ Aᵒ} {vL : Value L}
    → plug M (F-·₂ L {vL}) ≡ Lᵒ · Mᵒ
      --------------------------
    → Σ[ eqA ∈ A ≡ Aᵒ ] (subst-eq (λ A → Γ ⊢ A ⇒ B) eqA L ≡ Lᵒ) × (subst-eq (λ A → Γ ⊢ A) eqA M ≡ Mᵒ)
  plug-inv-app₂ refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

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

  plug-inv-case : ∀ {Γ A A† B B† C} {L : Γ ⊢ A `⊎ B} {L† : Γ ⊢ A† `⊎ B†}
                                    {M : Γ , A ⊢ C} {M† : Γ , A† ⊢ C}
                                    {N : Γ , B ⊢ C} {N† : Γ , B† ⊢ C}
    → plug L (F-case M N) ≡ case L† M† N†
      ----------------------------------
    → Σ[ eqA ∈ A ≡ A† ] Σ[ eqB ∈ B ≡ B† ] (subst₂-eq (λ A B → Γ ⊢ A `⊎ B) eqA eqB L ≡ L†) ×
                                           (subst-eq (λ A → Γ , A ⊢ C) eqA M ≡ M†) ×
                                           (subst-eq (λ B → Γ , B ⊢ C) eqB N ≡ N†)
  plug-inv-case refl = ⟨ refl , ⟨ refl , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩

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

  plug-inv-cast : ∀ {Γ A Aᵒ B} {M : Γ ⊢ A} {Mᵒ : Γ ⊢ Aᵒ} {cᵒ : Cast (Aᵒ ⇒ B)}
    → (F : Frame A B)
    → plug M F ≡ Mᵒ ⟨ cᵒ ⟩
      -----------------------------------------------------------------------------------------------------
    → Σ[ eq ∈ A ≡ Aᵒ ] ((subst-eq (λ A → Γ ⊢ A) eq M ≡ Mᵒ) × (subst-eq (λ A → Frame A B) eq F ≡ F-cast cᵒ))
  plug-inv-cast (F-cast c) refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩
