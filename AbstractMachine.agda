open import Types
open import Labels
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)

module AbstractMachine
  (Cast : Type → Set)
  (Inert : ∀{A} → Cast A → Set)
  (Active : ∀{A} → Cast A → Set)  
  (ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c)
  where

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  data Value : Type → Set
  Env : Context → Set
  
  data SimpleValue : Type → Set where

    V-ƛ : ∀ {Γ A B}
      → (N : Γ , A ⊢ B) → (ρ : Env Γ)
        -----------------------------
      → SimpleValue (A ⇒ B)

    V-const : ∀ {A}
      → (k : rep A) → {f : Prim A}
        ----------------------
      → SimpleValue A

    V-pair : ∀ {A B}
      → Value A → Value B
        --------------------
      → SimpleValue (A `× B)

    V-inl : ∀ {A B}
      → Value A
        --------------------
      → SimpleValue (A `⊎ B)

    V-inr : ∀ {A B}
      → Value B
        --------------------
      → SimpleValue (A `⊎ B)


  data Value where
    S-val : ∀ {A}
      → SimpleValue A
        -------------
      → Value A

    V-cast : ∀ {A B : Type}
      → SimpleValue A
      → (c : Cast (A ⇒ B))
      → {i : Inert c}
        ------------------
      → Value B

  Env Γ = ∀{A} → (x : Γ ∋ A) → Value A

  `∅ : Env ∅
  `∅ ()

  _`,_ : ∀ {Γ A} → Env Γ → Value A → Env (Γ , A)
  (γ `, v) Z = v
  (γ `, v) (S x) = γ x

  data Frame : {Γ : Context} → Type → Type → Set where

    F-·₁ : ∀ {Γ A B}
      → Γ ⊢ A
      → Frame {Γ} (A ⇒ B) B

    F-·₁v : ∀ {Γ A B}
      → Value A
      → Frame {Γ} (A ⇒ B) B

    F-·₂ : ∀ {Γ A B}
      → Γ ⊢ A ⇒ B
      → Frame {Γ} A B

    F-·₂v : ∀ {Γ A B}
      → Value (A ⇒ B)
      → Frame {Γ} A B

    F-if : ∀ {Γ A}
      → Γ ⊢ A
      → Γ ⊢ A
      → Frame {Γ} (` 𝔹) A

    F-×₁ : ∀ {Γ A B}
      → Value A
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

  data EvalContext : Context → Type → Type → Set where
    empty : ∀{Γ A} → EvalContext Γ A A
    extCtx : ∀{Γ A B C} → Frame {Γ} A B → EvalContext Γ B C
           → EvalContext Γ A C

  data Dump : Type → Type → Set where
    empty : ∀{A} → Dump A A
    push : ∀{Γ A B C} → EvalContext Γ A B → Env Γ → Dump B C
         → Dump A C

  module Machine
    (applyCast : ∀{A B} → Value A → (c : Cast (A ⇒ B)) → Active c
               → Value B ⊎ Label)
    (funSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' ⇒ B'))) → (i : Inert c)
            → SimpleValue A
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂)
    (dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         → Cast (A' ⇒ A₁))
    (cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Inert c
         →  Cast (A₂ ⇒ B'))
    (prodSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' `× B'))) → (i : Inert c)
            → SimpleValue A
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂)
    (cfst : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         → Cast (A₁ ⇒ A'))
    (csnd : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Inert c
         →  Cast (A₂ ⇒ B'))
    (sumSrc : ∀{A A' B'}
            → (c : Cast (A ⇒ (A' `⊎ B'))) → (i : Inert c)
            → SimpleValue A
            → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂)
    (cinl : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Inert c
         → Cast (A₁ ⇒ A'))
    (cinr : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Inert c
         →  Cast (A₂ ⇒ B'))
    (compose : ∀{A B C} → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
             → Cast (A ⇒ C))
    (baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c)
    where

    apply-cast : ∀{A B : Type} → (V : Value A) → Cast (A ⇒ B) → Value B ⊎ Label
    apply-cast (S-val V) c
        with ActiveOrInert c
    ... | inj₂ i = inj₁ (V-cast V c {i})
    ... | inj₁ a = applyCast (S-val V) c a
    apply-cast (V-cast V c₁) c₂
        with ActiveOrInert (compose c₁ c₂)
    ... | inj₂ i = inj₁ (V-cast V (compose c₁ c₂) {i})
    ... | inj₁ a = applyCast (S-val V) (compose c₁ c₂) a

    ret : ∀{Γ A B C} → Value A → Env Γ → EvalContext Γ A B → (d : Dump B C)
        → (Σ[ Γ' ∈ Context ] Σ[ A' ∈ Type ] Σ[ B' ∈ Type ] Σ[ C' ∈ Type ]
            Γ' ⊢ A' × Env Γ' × EvalContext Γ' A' B' × Dump B' C')
          ⊎ Label
          ⊎ Value C

    step : ∀{Γ A B C} → Γ ⊢ A → Env Γ → EvalContext Γ A B → Dump B C
        → (Σ[ Γ' ∈ Context ] Σ[ A' ∈ Type ] Σ[ B' ∈ Type ] Σ[ C' ∈ Type ]
            Γ' ⊢ A' × Env Γ' × EvalContext Γ' A' B' × Dump B' C')
          ⊎ Label
          ⊎ Value C
    step (` x) ρ E κ = ret (ρ x) ρ E κ
    step (ƛ M) ρ E κ = ret (S-val (V-ƛ M ρ)) ρ E κ
    step {Γ}{A}{B}{C} (_·_ {A = A'} L M) ρ E κ =
        inj₁ (⟨ Γ , ⟨ A' ⇒ A , ⟨ B , ⟨ C ,
              ⟨ L , ⟨ ρ , ⟨ extCtx (F-·₁ M) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step ($_ k {f}) ρ E κ = ret (S-val (V-const k {f})) ρ E κ
    step {Γ}{A}{B}{C} (if L M N) ρ E κ =
        inj₁ (⟨ Γ , ⟨ ` 𝔹 , ⟨ B , ⟨ C ,
              ⟨ L , ⟨ ρ , ⟨ extCtx (F-if M N) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step {Γ}{A₁ `× A₂}{B}{C} (cons M N) ρ E κ =
        inj₁ (⟨ Γ , ⟨ A₁ , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ extCtx (F-×₂ N) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step {Γ}{A₁}{B}{C} (fst{B = A₂} M) ρ E κ =
        inj₁ (⟨ Γ , ⟨ A₁ `× A₂ , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ extCtx F-fst E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step {Γ}{A₂}{B}{C} (snd{A = A₁} M) ρ E κ =
        inj₁ (⟨ Γ , ⟨ A₁ `× A₂ , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ extCtx F-snd E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step {Γ}{A}{B}{C} (inl{A = A'} M) ρ E κ =
        inj₁ (⟨ Γ , ⟨ A' , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ extCtx F-inl E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step {Γ}{A}{B}{C} (inr{B = B'} M) ρ E κ =
        inj₁ (⟨ Γ , ⟨ B' , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ extCtx F-inr E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step {Γ}{A}{B}{C} (case{A = A'}{B = B'} L M N) ρ E κ =
        inj₁ (⟨ Γ , ⟨ A' `⊎ B' , ⟨ B , ⟨ C ,
              ⟨ L , ⟨ ρ , ⟨ extCtx (F-case M N) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step {Γ}{A}{B}{C} (_⟨_⟩ {A = A'} M c) ρ E κ =
        inj₁ (⟨ Γ , ⟨ A' , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ extCtx (F-cast c) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    step (blame ℓ) ρ E κ = inj₂ (inj₁ ℓ)

    apply-sfun : ∀{Γ A A' B C} → SimpleValue (A ⇒ A') → Value A → Env Γ
        → EvalContext Γ A' B → Dump B C
        → (Σ[ Γ' ∈ Context ] Σ[ A' ∈ Type ] Σ[ B' ∈ Type ] Σ[ C' ∈ Type ]
            Γ' ⊢ A' × Env Γ' × EvalContext Γ' A' B' × Dump B' C')
          ⊎ Label
    apply-sfun {Γ} {A} {A'} {B} {C} (V-ƛ {Γ = Γ'} L ρ') V₂ ρ E κ
         with E
    ... | empty = {- Tail Call -}
        inj₁ (⟨ (Γ' , A) , ⟨ A' , ⟨ A' , ⟨ C ,
              ⟨ L , ⟨ (ρ' `, V₂) , ⟨ empty , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    ... | extCtx F E' = 
        inj₁ (⟨ (Γ' , A) , ⟨ A' , ⟨ A' , ⟨ C ,
              ⟨ L , ⟨ (ρ' `, V₂) , ⟨ empty , push E ρ κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    apply-sfun {Γ} {.(` ι)} {B} {C} {C'} (V-const f {P-Fun {ι} p})
                                         (S-val (V-const k)) ρ E κ =
        inj₁ (⟨ Γ , ⟨ B , ⟨ C , ⟨ C' ,
              ⟨ $_ (f k) {p} , ⟨ ρ , ⟨ E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    apply-sfun {Γ} {.(` ι)} {B} {C} (V-const f {P-Fun {ι} p})
                                    (V-cast x c {i}) ρ E κ =
        ⊥-elim (contradiction i (baseNotInert c))

    apply-fun : ∀{Γ A A' B C} → Value (A ⇒ A') → Value A → Env Γ
        → EvalContext Γ A' B → Dump B C
        → (Σ[ Γ' ∈ Context ] Σ[ A' ∈ Type ] Σ[ B' ∈ Type ] Σ[ C' ∈ Type ]
            Γ' ⊢ A' × Env Γ' × EvalContext Γ' A' B' × Dump B' C')
          ⊎ Label
    apply-fun {Γ} {A} {A'} {B} {C} (S-val V₁) V₂ ρ E κ =
        apply-sfun V₁ V₂ ρ E κ
    apply-fun {Γ} {A} {B} {C} (V-cast V₁ c {i}) V₂ ρ E κ
        with funSrc c i V₁
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩
        with apply-cast V₂ (dom c i)
    ... | inj₁ V₂' =
          apply-sfun V₁ V₂' ρ (extCtx (F-cast (cod c i)) E) κ 
    ... | inj₂ ℓ = inj₂ ℓ

    ret {Γ}{A}{B}{C} V ρ empty empty = inj₂ (inj₂ V)
    ret V ρ empty (push E ρ' κ) = ret V ρ' E κ
    ret {Γ}{A}{B}{C} V ρ (extCtx (F-·₁ {A = A'} M) E) κ =
        inj₁ (⟨ Γ , ⟨ A' , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ extCtx (F-·₂v V) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    ret {Γ}{A}{B}{C} V₁ ρ (extCtx (F-·₁v {A = A'} V₂) E) κ
        with apply-fun V₁ V₂ ρ E κ
    ... | inj₁ s = inj₁ s
    ... | inj₂ ℓ = inj₂ (inj₁ ℓ)
    ret {Γ}{A}{B}{C} V₂ ρ (extCtx (F-·₂{B = B'} L) E) κ =
        inj₁ (⟨ Γ , ⟨ A ⇒ B' , ⟨ B , ⟨ C ,
              ⟨ L , ⟨ ρ , ⟨ extCtx (F-·₁v V₂) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    ret {Γ}{A}{B}{C} V₂ ρ (extCtx (F-·₂v V₁) E) κ 
        with apply-fun V₁ V₂ ρ E κ
    ... | inj₁ s = inj₁ s
    ... | inj₂ ℓ = inj₂ (inj₁ ℓ)
    ret {Γ}{A}{B}{C} (S-val (V-const false)) ρ
        (extCtx {B = B'} (F-if M N) E) κ =
        inj₁ (⟨ Γ , ⟨ B' , ⟨ B , ⟨ C ,
              ⟨ N , ⟨ ρ , ⟨ E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    ret {Γ}{A}{B}{C} (S-val (V-const true)) ρ
        (extCtx {B = B'} (F-if M N) E) κ =
        inj₁ (⟨ Γ , ⟨ B' , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    ret (V-cast V c {i}) ρ (extCtx (F-if M N) E) κ =
        ⊥-elim (contradiction i (baseNotInert c))
    ret V₂ ρ (extCtx (F-×₁ V₁) E) κ = ret (S-val (V-pair V₁ V₂)) ρ E κ
    ret {Γ}{A}{B}{C} V₁ ρ (extCtx (F-×₂ {B = B'} N) E) κ =
        inj₁ (⟨ Γ , ⟨ B' , ⟨ B , ⟨ C ,
              ⟨ N , ⟨ ρ , ⟨ (extCtx (F-×₁ V₁) E) , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    ret (S-val (V-const ())) ρ (extCtx F-fst E) κ
    ret (S-val (V-pair V₁ V₂)) ρ (extCtx F-fst E) κ = ret V₁ ρ E κ
    ret (V-cast V c {i}) ρ (extCtx F-fst E) κ
        with prodSrc c i V
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩
        with V
    ... | V-const ()
    ... | V-pair V₁ V₂
        with apply-cast V₁ (cfst c i)
    ... | inj₁ V₁' = ret V₁' ρ E κ
    ... | inj₂ ℓ = inj₂ (inj₁ ℓ)
    ret (S-val (V-const ())) ρ (extCtx F-snd E) κ
    ret (S-val (V-pair V₁ V₂)) ρ (extCtx F-snd E) κ = ret V₂ ρ E κ
    ret (V-cast V c {i}) ρ (extCtx F-snd E) κ
        with prodSrc c i V
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩
        with V
    ... | V-const ()
    ... | V-pair V₁ V₂
        with apply-cast V₂ (csnd c i)
    ... | inj₁ V₂' = ret V₂' ρ E κ
    ... | inj₂ ℓ = inj₂ (inj₁ ℓ)
    ret V ρ (extCtx F-inl E) κ = ret (S-val (V-inl V)) ρ E κ
    ret V ρ (extCtx F-inr E) κ = ret (S-val (V-inr V)) ρ E κ
    ret (S-val (V-const ())) ρ (extCtx (F-case M N) E) κ
    ret {Γ}{A}{B}{C} (S-val (V-inl V)) ρ
        (extCtx (F-case {A = A'} {C = C'} M N) E) κ =
        inj₁ (⟨ Γ , ⟨ A' ⇒ C' , ⟨ B , ⟨ C ,
              ⟨ M , ⟨ ρ , ⟨ extCtx (F-·₁v V) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    ret {Γ}{A}{B}{C} (S-val (V-inr V)) ρ
        (extCtx (F-case {B = B'} {C = C'} M N) E) κ =
        inj₁ (⟨ Γ , ⟨ B' ⇒ C' , ⟨ B , ⟨ C ,
              ⟨ N , ⟨ ρ , ⟨ extCtx (F-·₁v V) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    ret (V-cast V c {i}) ρ (extCtx (F-case M N) E) κ
        with sumSrc c i V
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩
        with V
    ... | V-const ()
    ... | V-inl V₁
        with apply-cast V₁ (cinl c i)
    ... | inj₁ V₁' = ret V₁' ρ (extCtx (F-·₂ M) E) κ
    ... | inj₂ ℓ = inj₂ (inj₁ ℓ)
    ret (V-cast V c {i}) ρ (extCtx (F-case M N) E) κ | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩
        | V-inr V₂
        with apply-cast V₂ (cinr c i)
    ... | inj₁ V₂' = ret V₂' ρ (extCtx (F-·₂ N) E) κ
    ... | inj₂ ℓ = inj₂ (inj₁ ℓ)
    ret V ρ (extCtx (F-cast c) E) κ
        with apply-cast V c
    ... | inj₁ V' = ret V' ρ E κ
    ... | inj₂ ℓ = inj₂ (inj₁ ℓ)

