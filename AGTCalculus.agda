{-
open import Types
-}

open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality
   using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

module AGTCalculus
  (Type : Set)
  (convert : Type → Type → Set)
  (rep : Type → Set)
  (Prim : Type → Set)
  (prim-convert : ∀{A B} → convert A B → rep A → rep B)
  (dom : Type → Type)
  (cod : Type → Type)
  (fst-ty : Type → Type)
  (snd-ty : Type → Type)
  (inl-ty : Type → Type)
  (inr-ty : Type → Type)
  (join : Type → Type → Type)
  (Label : Set)
  (_⇒_ : Type → Type → Type)
  (_`×_ : Type → Type → Type)
  (_`⊎_ : Type → Type → Type)
  (𝔹 : Type)
  (dom-fun : ∀{A B} → dom (A ⇒ B) ≡ A)
  (cod-fun : ∀{A B} → cod (A ⇒ B) ≡ B)
  (fst-× : ∀{A B} → fst-ty (A `× B) ≡ A)
  (snd-× : ∀{A B} → snd-ty (A `× B) ≡ B)
  (inl-⊎ : ∀{A B} → inl-ty (A `⊎ B) ≡ A)
  (inr-⊎ : ∀{A B} → inr-ty (A `⊎ B) ≡ B)
  (conv-join-L : ∀{A B} → convert A (join A B))
  (conv-join-R : ∀{A B} → convert B (join A B))
  (rep⇒ : ∀{A B} → rep (A ⇒ B) → rep A → rep B)
  where

infixl 5 _,_

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context


infix  4 _∋_
infix  9 S_

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A



infix  4 _⊢_
infix 7 _·_
infix 8 _⟨_⟩

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ} {A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_ :  ∀ {Γ B A}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ} {A B}
    → Γ ⊢ A  →  Γ ⊢ B  → convert B (dom A)
      ------------------------------------
    → Γ ⊢ cod A

  $_ : ∀ {Γ A}
    → rep A
    → {f : Prim A}
      -----
    → Γ ⊢ A

  if : ∀ {Γ A B C}
    → Γ ⊢ A → Γ ⊢ B → Γ ⊢ C
    → convert A 𝔹
      ---------------------
    → Γ ⊢ join B C

  cons : ∀ {Γ A B}
    → Γ ⊢ A → Γ ⊢ B
      ---------------------
    → Γ ⊢ A `× B

  fst : ∀ {Γ A}
    → Γ ⊢ A
      ---------------------
    → Γ ⊢ fst-ty A

  snd : ∀ {Γ A}
    → Γ ⊢ A
      ---------------------
    → Γ ⊢ snd-ty A

  inl : ∀ {Γ A B}
    → Γ ⊢ A
      ----------
    → Γ ⊢ A `⊎ B

  inr : ∀ {Γ A B}
    → Γ ⊢ B
      ----------
    → Γ ⊢ A `⊎ B

  case : ∀ {Γ A B C D E}
    → Γ ⊢ A
    → Γ ⊢ B ⇒ C
    → Γ ⊢ D ⇒ E
    → convert (inl-ty A) B
    → convert (inr-ty A) D
      --------------------
    → Γ ⊢ join C E

  _⟨_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → convert A B
      ----------------------
    → Γ ⊢ B

  blame : ∀ {Γ A} → Label → Γ ⊢ A


ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → (Γ , B) ∋ A → (Δ , B) ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)


rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          = ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ ((L · M) c)    =  ((rename ρ L) · (rename ρ M)) c
rename ρ (($ k) {f})    = ($ k) {f}
rename ρ (if L M N c)   =  if (rename ρ L) (rename ρ M) (rename ρ N) c
rename ρ (cons L M)     = cons (rename ρ L) (rename ρ M)
rename ρ (fst M)        = fst (rename ρ M)
rename ρ (snd M)        = snd (rename ρ M)
rename ρ (inl M)        = inl (rename ρ M)
rename ρ (inr M)        = inr (rename ρ M)
rename ρ (case L M N cl cr) = case (rename ρ L) (rename ρ M) (rename ρ N) cl cr
rename ρ (M ⟨ c ⟩)      =  ((rename ρ M) ⟨ c ⟩)
rename ρ (blame ℓ)      =  blame ℓ

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)          =  σ x
subst σ (ƛ  N)         =  ƛ (subst (exts σ) N)
subst σ ((L · M) c)    =  ((subst σ L) · (subst σ M)) c
subst σ (($ k){f})     =  ($ k){f}
subst σ (if L M N c)   =  if (subst σ L) (subst σ M) (subst σ N) c
subst σ (cons M N)     =  cons (subst σ M) (subst σ N)
subst σ (fst M)     =  fst (subst σ M)
subst σ (snd M)     =  snd (subst σ M)
subst σ (inl M)     =  inl (subst σ M)
subst σ (inr M)     =  inr (subst σ M)
subst σ (case L M N cl cr) =  case (subst σ L) (subst σ M) (subst σ N) cl cr
subst σ (M ⟨ c ⟩)      =  (subst σ M) ⟨ c ⟩
subst σ (blame ℓ)      =  blame ℓ

subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x


_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N


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

  V-cast : ∀ {Γ : Context} {A B : Type} {V : Γ ⊢ A} {c : convert A B}
    → Value V
      ---------------
    → Value (V ⟨ c ⟩)


data Frame : {Γ : Context} → Type → Type → Set where

  F-·₁ : ∀ {Γ A B}
    → Γ ⊢ B
    → convert B (dom A)
    → Frame {Γ} A (cod A)

  F-·₂ : ∀ {Γ A B}
    → (M : Γ ⊢ A) → ∀{v : Value {Γ} M}
    → convert B (dom A)
    → Frame {Γ} B (cod A)

  F-if : ∀ {Γ A B C}
    → Γ ⊢ B
    → Γ ⊢ C
    → convert A 𝔹
    → Frame {Γ} A (join B C)

  F-×₁ : ∀ {Γ A B}
    → Γ ⊢ A
    → Frame {Γ} B (A `× B)

  F-×₂ : ∀ {Γ A B}
    → Γ ⊢ B
    → Frame {Γ} A (A `× B)

  F-fst : ∀ {Γ A}
    → Frame {Γ} A (fst-ty A)

  F-snd : ∀ {Γ A}
    → Frame {Γ} A (snd-ty A)

  F-inl : ∀ {Γ A B}
    → Frame {Γ} A (A `⊎ B)

  F-inr : ∀ {Γ A B}
    → Frame {Γ} B (A `⊎ B)

  F-case : ∀ {Γ A B C D E}
    → Γ ⊢ B ⇒ C
    → Γ ⊢ D ⇒ E
    → convert (inl-ty A) B
    → convert (inr-ty A) D
    → Frame {Γ} A (join C E)

{-

The plug function inserts an expression into the hole of a frame.

-}

plug : ∀{Γ A B} → Γ ⊢ A → Frame {Γ} A B → Γ ⊢ B
plug L (F-·₁ M c)    = (L · M) c
plug M (F-·₂ L c)    = (L · M) c
plug L (F-if M N c)  = if L M N c
plug L (F-×₁ M)      = cons M L
plug M (F-×₂ L)      = cons M L
plug M (F-fst)      = fst M
plug M (F-snd)      = snd M
plug M (F-inl)      = inl M
plug M (F-inr)      = inr M
plug L (F-case M N cl cr) = case L M N cl cr

{-
dom-fun : ∀{Γ}{A B : Type} → Γ ⊢ dom (A ⇒ B) → Γ ⊢ A)
-}

fst× : ∀{Γ}{A B} → Γ ⊢ A → Γ ⊢ fst-ty (A `× B)
fst× {Γ}{A}{B} M rewrite fst-× {A}{B} = M

snd× : ∀{Γ}{A B} → Γ ⊢ B → Γ ⊢ snd-ty (A `× B)
snd× {Γ}{A}{B} M rewrite snd-× {A}{B} = M

cod⇒ : ∀{Γ}{A B} → Γ ⊢ B → Γ ⊢ cod (A ⇒ B)
cod⇒ {Γ}{A}{B} M rewrite cod-fun {A}{B} = M

cod-rep : ∀{A B} → rep B → rep (cod (A ⇒ B))
cod-rep {A}{B} k rewrite cod-fun {A}{B} = k

dom-conv : ∀{A₁ A₂ B} → convert B (dom (A₁ ⇒ A₂)) → convert B A₁
dom-conv {A₁}{A₂}{B} c rewrite dom-fun {A₁}{A₂} = c

dom-prim : ∀{A₁ A₂ B} → convert B (dom (A₁ ⇒ A₂)) → rep B → rep A₁
dom-prim {A₁}{A₂}{B} c k rewrite dom-fun {A₁}{A₂} = prim-convert c k


inl-conv-dom : ∀{A₁ A₂ B C} → convert (inl-ty (A₁ `⊎ A₂)) B
            → convert A₁ (dom (B ⇒ C))
inl-conv-dom {A₁}{A₂}{B}{C} c
   rewrite dom-fun {B}{C} | inl-⊎ {A₁}{A₂} = c

inr-conv-dom : ∀{A₁ A₂ B C} → convert (inr-ty (A₁ `⊎ A₂)) B
            → convert A₂ (dom (B ⇒ C))
inr-conv-dom {A₁}{A₂}{B}{C} c
   rewrite dom-fun {B}{C} | inr-⊎ {A₁}{A₂} = c

conv-cod-join-L : ∀{B C E} → convert (cod (B ⇒ C)) (join C E)
conv-cod-join-L {B}{C}{E}
  rewrite cod-fun {B}{C} = conv-join-L {C}{E}

conv-cod-join-R : ∀{C D E} → convert (cod (D ⇒ E)) (join C E)
conv-cod-join-R {C}{D}{E}
  rewrite cod-fun {D}{E} = conv-join-R {C}{E}





infix 2 _—→_
data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B}
    → M —→ M′
      ---------------------
    → plug M F —→ plug M′ F

  ξ-blame : ∀ {Γ A B} {F : Frame {Γ} A B} {ℓ}
      ---------------------------
    → plug (blame ℓ) F —→ blame ℓ

  β : ∀ {Γ A₁ A₂ B} {N : Γ , A₁ ⊢ A₂} {W : Γ ⊢ B}{c : convert B (dom (A₁ ⇒ A₂))}
    → Value W
      ----------------------------------------------
    → ((ƛ N) · W) c —→ cod⇒ (N [ W ⟨ dom-conv c ⟩ ])

  δ : ∀ {Γ : Context} {A₁ A₂ B} {f : rep (A₁ ⇒ A₂)} {k : rep B}
        {ab} {a} {b} {c : convert B (dom (A₁ ⇒ A₂))}
      ---------------------------------------------------------
    → (($_ {Γ}{A₁ ⇒ A₂} f {ab}) · (($ k){a})) c
       —→ ($ (cod-rep ((rep⇒ f) (dom-prim c k)))){b}

  β-if-true :  ∀ {Γ A B C} {M : Γ ⊢ B} {N : Γ ⊢ C}{p : Prim A}{c : convert A 𝔹}
      -------------------------------------------
    → if (($ {!!}){p}) M N c —→ M ⟨ conv-join-L ⟩

  β-if-false :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}{f}{c}
      ---------------------------------------------
    → if (($ {!!}){f}) M N c —→ N  ⟨ conv-join-R ⟩

  β-fst :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V → Value W
      ------------------------
    → fst (cons V W) —→ fst× V

  β-snd :  ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V → Value W
      --------------------
    → snd (cons V W) —→ snd× W

  β-caseL : ∀ {Γ A₁ A₂ B C D E} {V : Γ ⊢ A₁} {L : Γ ⊢ B ⇒ C} {M : Γ ⊢ D ⇒ E}
      {cl : convert (inl-ty (A₁ `⊎ A₂)) B} {cr : convert (inr-ty (A₁ `⊎ A₂)) D}
    → Value V
      ---------------------------------------------------------------
    → case (inl {Γ}{A₁}{A₂} V) L M cl cr
      —→ ((L · V) (inl-conv-dom cl)) ⟨ conv-cod-join-L ⟩

  β-caseR : ∀ {Γ A₁ A₂ B C D E} {V : Γ ⊢ A₂} {L : Γ ⊢ B ⇒ C} {M : Γ ⊢ D ⇒ E}
      {cl : convert (inl-ty (A₁ `⊎ A₂)) B} {cr : convert (inr-ty (A₁ `⊎ A₂)) D}
    → Value V
      ------------------------------------------------------------------
    → case (inr {Γ}{A₁}{A₂} V) L M cl cr
      —→ ((M · V) (inr-conv-dom cr)) ⟨ conv-cod-join-R ⟩ 

data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      -------------
    → Progress M

  done :
      Value M
      ----------
    → Progress M


progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M) = done V-ƛ
progress ((M · M₁) c) = {!!}
progress ($ x) = done V-const
progress {D} (if {∅}{A}{B}{C} L M N c) = {!!}
{-
    with progress L
... | step {L'} R = step (ξ{F = F-if M N c} R)
... | done (V-const {k = k}) = {!!}
... | done (V-cast {c = c'} v) = {!!}
-}
progress (cons M M₁) = {!!}
progress (fst M) = {!!}
progress (snd M) = {!!}
progress (inl M) = {!!}
progress (inr M) = {!!}
progress (case M M₁ M₂ x x₁) = {!!}
progress (M ⟨ x ⟩) = {!!}
progress (blame x) = {!!}
