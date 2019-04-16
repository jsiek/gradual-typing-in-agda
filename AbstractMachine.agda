open import Types
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

  data Closure : Type → Set

  Env : Context → Set
  Env Γ = ∀{A} → (x : Γ ∋ A) → Closure A

  `∅ : Env ∅
  `∅ ()

  _`,_ : ∀ {Γ A} → Env Γ → Closure A → Env (Γ , A)
  (γ `, v) Z = v
  (γ `, v) (S x) = γ x

  data Closure where
    clos : ∀{Γ A} → (M : Γ ⊢ A) → Env Γ → {v : Value M} → Closure A

  data Frame : {Γ : Context} → Type → Type → Set where

    F-·₁ : ∀ {Γ A B}
      → Γ ⊢ A
      → Frame {Γ} (A ⇒ B) B

    F-·₂ : ∀ {Γ A B}
      → (M : Closure (A ⇒ B))
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

  data EvalContext : Context → Type → Type → Set where
    empty : ∀{Γ A} → EvalContext Γ A A
    extCtx : ∀{Γ A B C} → Frame {Γ} A B → EvalContext Γ B C
           → EvalContext Γ A C

  data Dump : Type → Type → Set where
    empty : ∀{A} → Dump A A
    push : ∀{Γ A B C} → EvalContext Γ A B → Env Γ → Dump B C
         → Dump A C
  
  ret : ∀{Γ A B C} → Closure A → Env Γ → EvalContext Γ A B → Dump B C
      → Σ[ Γ' ∈ Context ] Σ[ A' ∈ Type ] Σ[ B' ∈ Type ] Σ[ C' ∈ Type ]
         Γ' ⊢ A' × Env Γ' × EvalContext Γ' A' B' × Dump B' C'
         
  step : ∀{Γ A B C} → Γ ⊢ A → Env Γ → EvalContext Γ A B → Dump B C
      → Σ[ Γ' ∈ Context ] Σ[ A' ∈ Type ] Σ[ B' ∈ Type ] Σ[ C' ∈ Type ]
         Γ' ⊢ A' × Env Γ' × EvalContext Γ' A' B' × Dump B' C'
  step (` x) ρ E κ = ret (ρ x) ρ E κ
  step (ƛ M) ρ E κ = ret (clos (ƛ M) ρ {S-val V-ƛ}) ρ E κ
  step {Γ}{A}{B}{C} (_·_ {A = A'} L M) ρ E κ =
      ⟨ Γ , ⟨ A' ⇒ A , ⟨ B , ⟨ C ,
      ⟨ L , ⟨ ρ , ⟨ extCtx (F-·₁ M) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step ($_ x {f}) ρ E κ = ret (clos ($_ x {f}) ρ {S-val V-const}) ρ E κ
  step {Γ}{A}{B}{C} (if L M N) ρ E κ =
      ⟨ Γ , ⟨ ` 𝔹 , ⟨ B , ⟨ C ,
      ⟨ L , ⟨ ρ , ⟨ extCtx (F-if M N) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step {Γ}{A₁ `× A₂}{B}{C} (cons M N) ρ E κ =
      ⟨ Γ , ⟨ A₁ , ⟨ B , ⟨ C ,
      ⟨ M , ⟨ ρ , ⟨ extCtx (F-×₂ N) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step {Γ}{A₁}{B}{C} (fst{B = A₂} M) ρ E κ =
      ⟨ Γ , ⟨ A₁ `× A₂ , ⟨ B , ⟨ C ,
      ⟨ M , ⟨ ρ , ⟨ extCtx F-fst E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step {Γ}{A₂}{B}{C} (snd{A = A₁} M) ρ E κ =
      ⟨ Γ , ⟨ A₁ `× A₂ , ⟨ B , ⟨ C ,
      ⟨ M , ⟨ ρ , ⟨ extCtx F-snd E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step {Γ}{A}{B}{C} (inl{A = A'} M) ρ E κ =
      ⟨ Γ , ⟨ A' , ⟨ B , ⟨ C ,
      ⟨ M , ⟨ ρ , ⟨ extCtx F-inl E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step {Γ}{A}{B}{C} (inr{B = B'} M) ρ E κ =
      ⟨ Γ , ⟨ B' , ⟨ B , ⟨ C ,
      ⟨ M , ⟨ ρ , ⟨ extCtx F-inr E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step {Γ}{A}{B}{C} (case{A = A'}{B = B'} L M N) ρ E κ =
      ⟨ Γ , ⟨ A' `⊎ B' , ⟨ B , ⟨ C ,
      ⟨ L , ⟨ ρ , ⟨ extCtx (F-case M N) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step {Γ}{A}{B}{C} (_⟨_⟩ {A = A'} M c) ρ E κ =
      ⟨ Γ , ⟨ A' , ⟨ B , ⟨ C ,
      ⟨ M , ⟨ ρ , ⟨ extCtx (F-cast c) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  
  step (blame ℓ) ρ E κ = {!!}

  ret C ρ empty empty = {!!}
  ret C ρ empty (push E ρ' κ) = ret C ρ' E κ
  ret {Γ}{A}{B}{C} Lc ρ (extCtx (F-·₁ {A = A'} M) E) κ =
    ⟨ Γ , ⟨ A' , ⟨ B , ⟨ C ,
    ⟨ M , ⟨ ρ , ⟨ extCtx (F-·₂ Lc) E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  ret {Γ}{A}{B}{C} Mc ρ
      (extCtx (F-·₂ {B = B'} (clos {Γ = Γ'} (ƛ L) ρ' {S-val V-ƛ})) E)
      κ =
    ⟨ (Γ' , A) , ⟨ B' , ⟨ B' , ⟨ C ,
    ⟨ L , ⟨ (ρ' `, Mc) , ⟨ empty , push E ρ κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  ret Mc ρ (extCtx (F-·₂ (clos .($ _) ρ' {S-val V-const})) E) κ = {!!}
  ret Mc ρ (extCtx (F-·₂ (clos (L ⟨ c ⟩) ρ' {V-cast v})) E) κ = {!!}
  ret Lc ρ (extCtx (F-if M N) E) κ = {!!}
  ret Nc ρ (extCtx (F-×₁ Mc) E) κ = {!!}
  ret Mc ρ (extCtx (F-×₂ N) E) κ = {!!}
  ret Mc ρ (extCtx F-fst E) κ = {!!}
  ret Mc ρ (extCtx F-snd E) κ = {!!}
  ret Mc ρ (extCtx F-inl E) κ = {!!}
  ret Mc ρ (extCtx F-inr E) κ = {!!}
  ret Mc ρ (extCtx (F-case M N) E) κ = {!!}
  ret Mc ρ (extCtx (F-cast c) E) κ = {!!}
