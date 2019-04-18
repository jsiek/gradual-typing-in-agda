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

  data Dump : Type → Type → Set
  
  data PDump : Type → Type → Set where
    empty : ∀{A} → PDump A A
    push : ∀{Γ A B C} → EvalContext Γ A B → Env Γ → Dump B C
         → PDump A C

  data Dump where
    dump : ∀{A B} → PDump A B → Dump A B
    pushCast : ∀{A B C} → Cast (A ⇒ B) → PDump B C → Dump A C

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

    push-cast : ∀{A B C} → Cast (A ⇒ B) → Dump B C → Dump A C
    push-cast c (dump d) = pushCast c d
    push-cast c₁ (pushCast c₂ d) = pushCast (compose c₁ c₂) d

    TermConfig : Type → Set
    TermConfig C = (Σ[ Γ' ∈ Context ] Σ[ A' ∈ Type ] Σ[ B' ∈ Type ] 
                    Γ' ⊢ A' × Env Γ' × EvalContext Γ' A' B' × Dump B' C)

    ValueConfig : Type → Set
    ValueConfig C = (Σ[ Γ' ∈ Context ] Σ[ A' ∈ Type ] Σ[ B' ∈ Type ] 
                     Value A' × Env Γ' × EvalContext Γ' A' B' × Dump B' C)

    data Result : (C : Type) → Set where
       tc : ∀{C} → TermConfig C → Result C
       vc : ∀{C} → ValueConfig C → Result C
       err : ∀{C} → Label → Result C
       done : ∀{C} → Value C → Result C 

    ret-val : ∀{Γ A B C}
            → Value A → Env Γ → EvalContext Γ A B → Dump B C → Result C
    ret-val {Γ}{A}{B}{C} V ρ E κ =
      vc (⟨ Γ , ⟨ A , ⟨ B , ⟨ V , ⟨ ρ , ⟨ E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)

    next : ∀{Γ A B C} → Γ ⊢ A → Env Γ → EvalContext Γ A B → Dump B C → Result C
    next {Γ}{A}{B}{C} M ρ E κ =
        tc (⟨ Γ , ⟨ A , ⟨ B , 
              ⟨ M , ⟨ ρ , ⟨ E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)

    step : ∀{Γ A B C} → Γ ⊢ A → Env Γ → EvalContext Γ A B → Dump B C → Result C
    step (` x) ρ E κ = ret-val (ρ x) ρ E κ
    step (ƛ M) ρ E κ = ret-val (S-val (V-ƛ M ρ)) ρ E κ
    step {Γ}{A}{B}{C} (_·_ {A = A'} L M) ρ E κ =
        next L ρ (extCtx (F-·₁ M) E) κ
    step ($_ k {f}) ρ E κ = ret-val (S-val (V-const k {f})) ρ E κ
    step {Γ}{A}{B}{C} (if L M N) ρ E κ =
        next L ρ (extCtx (F-if M N) E) κ
    step {Γ}{A₁ `× A₂}{B}{C} (cons M N) ρ E κ =
        next M ρ (extCtx (F-×₂ N) E) κ
    step {Γ}{A₁}{B}{C} (fst{B = A₂} M) ρ E κ =
        next M ρ (extCtx F-fst E) κ
    step {Γ}{A₂}{B}{C} (snd{A = A₁} M) ρ E κ =
        next M ρ (extCtx F-snd E) κ
    step {Γ}{A}{B}{C} (inl{A = A'} M) ρ E κ =
        next M ρ (extCtx F-inl E) κ
    step {Γ}{A}{B}{C} (inr{B = B'} M) ρ E κ =
        next M ρ (extCtx F-inr E) κ
    step {Γ}{A}{B}{C} (case{A = A'}{B = B'} L M N) ρ E κ =
        next L ρ (extCtx (F-case M N) E) κ
    step {Γ}{A}{B}{C} (_⟨_⟩ {A = A'} M c) ρ E κ
        with E
    ... | empty =       {- Tail Cast -}
        next M ρ empty (push-cast c κ)
    ... | extCtx F E' = {- Regular Cast -}
        next M ρ (extCtx (F-cast c) E) κ
    step (blame ℓ) ρ E κ = err ℓ

    ret : ∀{Γ A B C} → Value A → Env Γ → EvalContext Γ A B → Dump B C → Result C

    {- End of program and returning from a procedure -}
    ret V ρ empty (dump empty) = done V
    ret V ρ empty (dump (push E ρ' κ)) =
        ret-val V ρ' E κ
    ret V ρ empty (pushCast c κ) =
        ret-val V ρ (extCtx (F-cast c) empty) (dump κ)

    {- Switch from evaluating operator to operand of application. -}
    ret {Γ}{A}{B}{C} V ρ (extCtx (F-·₁ {A = A'} M) E) κ =
        next M ρ (extCtx (F-·₂v V) E) κ
    ret {Γ}{A}{B}{C} V₁ ρ (extCtx (F-·₁v V₂) E) κ =
        ret-val V₂ ρ (extCtx (F-·₂v V₁) E) κ

    {- Switch from evaluating operand to operator of application.
       (Needed to handle case expressions.) -}
    ret {Γ}{A}{B}{C} V₂ ρ (extCtx (F-·₂{B = B'} L) E) κ =
        next L ρ (extCtx (F-·₁v V₂) E) κ

    {- Procedure call in tail position -}
    ret {Γ}{A}{B}{C} V₂ ρ (extCtx (F-·₂v (S-val (V-ƛ {Γ = Γ'} L ρ'))) empty) κ =
        next L (ρ' `, V₂) empty κ
    {- Procedure call -}
    ret {Γ}{A}{B}{C} V₂ ρ (extCtx (F-·₂v (S-val (V-ƛ {Γ = Γ'}{B = B'} L ρ')))
                          (extCtx F E')) κ =
        next L (ρ' `, V₂) empty (dump (push (extCtx F E') ρ κ))

    {- Primitive operator application -}
    ret {Γ} {` ι} {B} {C} (S-val (V-const k)) ρ
                       (extCtx (F-·₂v (S-val (V-const f {P-Fun {ι} p}))) E) κ =
        ret-val (S-val (V-const (f k) {p})) ρ E κ
    ret {Γ} {` ι} {B} {C} (V-cast x c {i}) ρ
                       (extCtx (F-·₂v (S-val (V-const f {P-Fun {ι} p}))) E) κ =
        ⊥-elim (contradiction i (baseNotInert c))

    {- Apply a wrapped procedure in tail position -} 
    ret {Γ}{A}{B}{C} V₂ ρ (extCtx (F-·₂v (V-cast V₁ c {i})) empty) κ
        with funSrc c i V₁
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ =
        ret-val V₂ ρ (extCtx (F-cast (dom c i))
                     (extCtx (F-·₂v (S-val V₁)) empty))
                     (push-cast (cod c i) κ)
    {- Apply a wrapped procedure -} 
    ret {Γ}{A}{B}{C} V₂ ρ (extCtx (F-·₂v (V-cast V₁ c {i})) (extCtx F E)) κ
        with funSrc c i V₁
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ =
        ret-val V₂ ρ (extCtx (F-cast (dom c i))
                     (extCtx (F-·₂v (S-val V₁))
                     (extCtx (F-cast (cod c i)) (extCtx F E)))) κ

    {- Dispatch to false branch of if expression. -}
    ret {Γ}{A}{B}{C} (S-val (V-const false)) ρ
        (extCtx {B = B'} (F-if M N) E) κ =
        next N ρ E κ
    {- Dispatch to true branch of if expression. -}
    ret {Γ}{A}{B}{C} (S-val (V-const true)) ρ
        (extCtx {B = B'} (F-if M N) E) κ =
        next M ρ E κ
    ret (V-cast V c {i}) ρ (extCtx (F-if M N) E) κ =
        ⊥-elim (contradiction i (baseNotInert c))

    {- Create a pair. -}
    ret V₂ ρ (extCtx (F-×₁ V₁) E) κ =
        ret-val (S-val (V-pair V₁ V₂)) ρ E κ
    ret {Γ}{A}{B}{C} V₁ ρ (extCtx (F-×₂ {B = B'} N) E) κ =
        next N ρ (extCtx (F-×₁ V₁) E) κ

    {- Take first element from pair. -}
    ret (S-val (V-const ())) ρ (extCtx F-fst E) κ
    ret (S-val (V-pair V₁ V₂)) ρ (extCtx F-fst E) κ =
        ret-val V₁ ρ E κ
    ret (V-cast V c {i}) ρ (extCtx F-fst E) κ
        with prodSrc c i V
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ =
        ret-val (S-val V) ρ (extCtx F-fst (extCtx (F-cast (cfst c i)) E)) κ

    {- Take second element from pair. -}
    ret (S-val (V-const ())) ρ (extCtx F-snd E) κ
    ret (S-val (V-pair V₁ V₂)) ρ (extCtx F-snd E) κ =
        ret-val V₂ ρ E κ
    ret (V-cast V c {i}) ρ (extCtx F-snd E) κ
        with prodSrc c i V
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ =
        ret-val (S-val V) ρ (extCtx F-snd (extCtx (F-cast (csnd c i)) E)) κ

    {- Inject left. -}
    ret V ρ (extCtx F-inl E) κ = ret-val (S-val (V-inl V)) ρ E κ
    {- Inject right. -}
    ret V ρ (extCtx F-inr E) κ = ret-val (S-val (V-inr V)) ρ E κ

    ret (S-val (V-const ())) ρ (extCtx (F-case M N) E) κ
    {- Dispatch to left branch of case expression. -}
    ret {Γ}{A}{B}{C} (S-val (V-inl V)) ρ
        (extCtx (F-case {A = A'} {C = C'} M N) E) κ =
        next M ρ (extCtx (F-·₁v V) E) κ
    {- Dispatch to right branch of case expression. -}
    ret {Γ}{A}{B}{C} (S-val (V-inr V)) ρ
        (extCtx (F-case {B = B'} {C = C'} M N) E) κ =
        next N ρ (extCtx (F-·₁v V) E) κ
    {- Dispatch on a wrapped value. -}
    ret (V-cast V c {i}) ρ (extCtx (F-case M N) E) κ
        with sumSrc c i V
    ... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩
        with V
    ... | V-const ()
    {- Cast and dispatch to left branch -}    
    ... | V-inl V₁ =
        ret-val V₁ ρ (extCtx (F-cast (cinl c i)) (extCtx (F-·₂ M) E)) κ 
    {- Cast and dispatch to right branch -}
    ret (V-cast V c {i}) ρ (extCtx (F-case M N) E) κ | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩
        | V-inr V₂ =
        ret-val V₂ ρ (extCtx (F-cast (cinr c i)) (extCtx (F-·₂ N) E)) κ

    ret V ρ (extCtx (F-cast c) E) κ
        with apply-cast V c
    ... | inj₁ V' = ret-val V' ρ E κ
    ... | inj₂ ℓ = err ℓ

    load : ∀{A} → ∅ ⊢ A → Result A
    load {A} M = next M `∅ empty (dump empty)

    exec : ∀{A} → ℕ → Result A → Value A ⊎ Label
    exec 0 R = inj₂ (pos 0)
    exec {A} (suc n) (tc (⟨ Γ , ⟨ A' , ⟨ B , ⟨ M , ⟨ ρ , ⟨ E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)) =
        exec n (step M ρ E κ)
    exec {A} (suc n) (vc (⟨ Γ , ⟨ A' , ⟨ B , ⟨ V , ⟨ ρ , ⟨ E , κ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)) =
        exec n (ret V ρ E κ)
    exec {A} (suc n) (err ℓ) = inj₂ ℓ
    exec {A} (suc n) (done V) = inj₁ V

    run : ∀{A} → ℕ → ∅ ⊢ A → Value A ⊎ Label
    run n M = exec n (load M)
