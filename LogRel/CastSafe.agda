{-# OPTIONS --rewriting #-}
module LogRel.CastSafe where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
--open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import Structures using (extensionality)
open import LogRel.Cast

{-------------      Proof of Progress    -------------}

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

  error :
      Blame M
      --------------
    → Progress M

progress : ∀ {M A}
  → [] ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢$ k)                           =  done ($̬ k)
progress (⊢ƛ ⊢N)                          =  done (ƛ̬ _)
progress (⊢· ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                          =  step (ξ (□· _) L—→L′)
... | error isBlame                       = step (ξ-blame (□· _))
... | done (ƛ̬ N)
    with progress ⊢M
... | step M—→M′                          =  step (ξ ((ƛ̬ _) ·□) M—→M′)
... | error isBlame                       = step (ξ-blame ((ƛ̬ _) ·□))
... | done w                              = step (β w)
progress (⊢⟨!⟩ ⊢M)
    with progress ⊢M
... | step M—→M′                          = step (ξ □⟨ _ !⟩ M—→M′)
... | error isBlame                       = step (ξ-blame □⟨ _ !⟩)
... | done v                              = done (v 〈 _ 〉)
progress (⊢⟨?⟩ ⊢M H) 
    with progress ⊢M
... | step M—→M′                          = step (ξ □⟨ _ ?⟩ M—→M′)
... | error isBlame                       = step (ξ-blame □⟨ _ ?⟩)
... | done v
    with v
... | v₁ 〈 G 〉
    with G ≡ᵍ H
... | yes refl                            = step (collapse v₁ refl)
... | no neq                              = step (collide v₁ neq refl)
progress ⊢blame                           = error isBlame


{- renaming preserves types -}

wtren : Rename → List Type → List Type → Set
wtren ρ Γ Δ = ∀ {B} x → Γ ∋ x ⦂ B → Δ ∋ ρ x ⦂ B

ext-ren : ∀{Γ}{Δ}{ρ}{B}
  → wtren ρ Γ Δ
  → wtren (extr ρ) (B ∷ Γ) (B ∷ Δ)
ext-ren {Γ} {Δ} {ρ} {B} ⊢ρ zero ∋x = ∋x
ext-ren {Γ} {Δ} {ρ} {B} ⊢ρ (suc x) ∋x = ⊢ρ x ∋x

ren-pres-type : ∀{Γ}{Δ}{A}{M}{ρ}
  → Γ ⊢ M ⦂ A
  → wtren ρ Γ Δ
  → Δ ⊢ ⟪ ren ρ ⟫ M ⦂ A
ren-pres-type {Γ}{Δ} {A} {.(` _)}{ρ} (⊢`{x = x} ∋x) ⊢ρ
  rewrite sub-var (ren ρ) x | ren-def ρ x = ⊢` (⊢ρ x ∋x)
ren-pres-type {Γ}{Δ} {.($ₜ typeof c)} {.($ c)} (⊢$ c) ⊢ρ = ⊢$ c
ren-pres-type {Γ}{Δ} {A} {.(_ · _)} (⊢· ⊢L ⊢M) ⊢ρ =
  ⊢· (ren-pres-type ⊢L ⊢ρ) (ren-pres-type ⊢M ⊢ρ)
ren-pres-type {Γ}{Δ} {.(_ ⇒ _)} {.(ƛ _)}{ρ = ρ} (⊢ƛ ⊢M) ⊢ρ =
  ⊢ƛ (ren-pres-type{ρ = extr ρ} ⊢M (ext-ren{Δ = Δ}{ρ} ⊢ρ))
ren-pres-type {Γ}{Δ} {.★} {.(_ ⟨ _ !⟩)} (⊢⟨!⟩ ⊢M) ⊢ρ =
  ⊢⟨!⟩ (ren-pres-type ⊢M ⊢ρ)
ren-pres-type {Γ}{Δ} {.(gnd⇒ty H)} {.(_ ⟨ H ?⟩)} (⊢⟨?⟩ ⊢M H) ⊢ρ = 
  ⊢⟨?⟩ (ren-pres-type ⊢M ⊢ρ) H
ren-pres-type {Γ}{Δ} {A} {.blame} ⊢blame ⊢ρ = ⊢blame

{- substitution preserves types -}

wtsub : Subst → List Type → List Type → Set
wtsub σ Γ Δ = ∀ {B} x → Γ ∋ x ⦂ B → Δ ⊢ σ x ⦂ B

ext-sub : ∀{Γ}{Δ}{σ}{B}
  → wtsub σ Γ Δ
  → wtsub (ext σ) (B ∷ Γ) (B ∷ Δ)
ext-sub {Γ} {Δ} {σ} {B} ⊢σ zero refl = ⊢` refl
ext-sub {Γ} {Δ} {σ} {B} ⊢σ {A} (suc x) ∋x rewrite seq-def σ ↑ x =
  ren-pres-type{ρ = suc} (⊢σ x ∋x) λ x₁ x₂ → x₂

sub-pres-type : ∀{Γ}{Δ}{A}{M}{σ}
  → Γ ⊢ M ⦂ A
  → wtsub σ Γ Δ
  → Δ ⊢ ⟪ σ ⟫ M ⦂ A
sub-pres-type {Γ} {Δ} {A} {.(` _)} {σ} (⊢`{x = x} ∋x) ⊢σ
  rewrite sub-var σ x = ⊢σ x ∋x
sub-pres-type {Γ} {Δ} {.($ₜ typeof c)} {.($ c)} {σ} (⊢$ c) ⊢σ = ⊢$ c
sub-pres-type {Γ} {Δ} {A} {.(_ · _)} {σ} (⊢· ⊢L ⊢M) ⊢σ =
  ⊢· (sub-pres-type ⊢L ⊢σ) (sub-pres-type ⊢M ⊢σ)
sub-pres-type {Γ} {Δ} {.(_ ⇒ _)} {.(ƛ _)} {σ} (⊢ƛ ⊢M) ⊢σ =
  ⊢ƛ (sub-pres-type{σ = ext σ} ⊢M (ext-sub ⊢σ))
sub-pres-type {Γ} {Δ} {.★} {.(_ ⟨ _ !⟩)} {σ} (⊢⟨!⟩ ⊢M) ⊢σ =
  ⊢⟨!⟩ (sub-pres-type ⊢M ⊢σ)
sub-pres-type {Γ} {Δ} {.(gnd⇒ty H)} {.(_ ⟨ H ?⟩)} {σ} (⊢⟨?⟩ ⊢M H) ⊢σ =
  ⊢⟨?⟩ (sub-pres-type ⊢M ⊢σ) H
sub-pres-type {Γ} {Δ} {A} {.blame} {σ} ⊢blame ⊢σ = ⊢blame

{-------------      Proof of Preservation    -------------}

preservation : ∀{Γ}{M}{N}{A}
  → Γ ⊢ M ⦂ A
  → M —→ N
  → Γ ⊢ N ⦂ A
preservation ⊢M (ξ (□· M) L→L′)
    with ⊢M
... | ⊢· ⊢L ⊢M = ⊢· (preservation ⊢L L→L′) ⊢M
preservation ⊢M (ξ (v ·□) M→M′)
    with ⊢M
... | ⊢· ⊢L ⊢M = ⊢· ⊢L (preservation ⊢M M→M′)
preservation ⊢M (ξ □⟨ G !⟩ M→M′)
    with ⊢M
... | ⊢⟨!⟩ ⊢M = ⊢⟨!⟩ (preservation ⊢M M→M′)    
preservation ⊢M (ξ □⟨ H ?⟩ M→M′)
    with ⊢M
... | ⊢⟨?⟩ ⊢M H = ⊢⟨?⟩ (preservation ⊢M M→M′) H
preservation ⊢M (ξ-blame F) = ⊢blame
preservation (⊢·{M = W} (⊢ƛ ⊢N) ⊢W) (β w) =
  sub-pres-type{σ = W • id} ⊢N λ { zero refl → ⊢W ; (suc x) ∋x → ⊢` ∋x}
preservation ⊢M (collapse v refl)
  with ⊢M
... | ⊢⟨?⟩ (⊢⟨!⟩ ⊢N) G = ⊢N  
preservation ⊢M (collide v neq refl) = ⊢blame

multi-preservation : ∀{Γ}{M}{N}{A}
  → Γ ⊢ M ⦂ A
  → M —↠ N
  → Γ ⊢ N ⦂ A
multi-preservation ⊢M (_ END) = ⊢M
multi-preservation ⊢M (_ —→⟨ M→M′ ⟩ M′—↠N) =
  multi-preservation (preservation ⊢M M→M′) M′—↠N
  
{-
   After k steps, a program will have either halted with blame or a value,
   or the program can keep going.
-}

trichotomy : ∀ {A} M k
  → [] ⊢ M ⦂ A
  → (Σ[ r ∈ M —↠ blame ] len r < k)
    ⊎ (∃[ V ] Σ[ r ∈ M —↠ V ] (len r < k) × Value V)
    ⊎ (∃[ N ] Σ[ r ∈ M —↠ N ] len r ≡ k)
trichotomy M zero ⊢M = inj₂ (inj₂ (M , ((M END) , refl)))
trichotomy M (suc k) ⊢M
    with progress ⊢M
... | done m = inj₂ (inj₁ (M , ((M END) , ((s≤s z≤n) , m))))
... | error isBlame = inj₁ ((blame END) , (s≤s z≤n))
... | step{N = N} M→N 
    with trichotomy N k (preservation ⊢M M→N)
... | inj₁ (N→blame , r<k) = inj₁ ((M —→⟨ M→N ⟩ N→blame) , s≤s r<k)
... | inj₂ (inj₁ (V , N→V , r<k , v)) =
      inj₂ (inj₁ (V , ((M —→⟨ M→N ⟩ N→V) , (s≤s r<k) , v)))
... | inj₂ (inj₂ (N , N₁—↠N , refl)) =
      inj₂ (inj₂ (N , ((M —→⟨ M→N ⟩ N₁—↠N) , refl)))

diverge : Term → Set
diverge M = ∀ k → ∃[ N ] Σ[ r ∈ M —↠ N ] k ≡ len r

halt : Term → Set
halt M  = (M —↠ blame) ⊎ (∃[ V ] (M —↠ V) × Value V)

len-concat : ∀ {L}{M}{N} (s : L —↠ M) (r : M —↠ N)
  → len (s ++ r) ≡ len s + len r
len-concat (_ END) r = refl
len-concat (_ —→⟨ x ⟩ s) r rewrite len-concat s r = refl

not-halt⇒diverge : ∀{A} M
  → [] ⊢ M ⦂ A
  → ¬ halt M
  → diverge M
not-halt⇒diverge M ⊢M ¬haltM zero = M , (M END) , refl
not-halt⇒diverge M ⊢M ¬haltM (suc k)
    with trichotomy M k ⊢M
... | inj₁ (M—↠blame , r<k) = ⊥-elim (¬haltM (inj₁ M—↠blame))
... | inj₂ (inj₁ (V , M—↠V , r<k , v)) = ⊥-elim (¬haltM (inj₂ (V , M—↠V , v)))
... | inj₂ (inj₂ (N , M—↠N , refl))
    with progress (multi-preservation ⊢M M—↠N)
... | done v = ⊥-elim (¬haltM (inj₂ (_ , (M—↠N , v))))
... | error isBlame = ⊥-elim (¬haltM (inj₁ M—↠N))
... | step r = _ , ((M—↠N ++ unit r) , EQ)
    where
    EQ : suc (len M—↠N) ≡ len (M—↠N ++ unit r)
    EQ rewrite len-concat (M—↠N) (unit r) = +-comm 1 (len M—↠N)
