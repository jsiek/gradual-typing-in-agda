{-# OPTIONS --rewriting #-}
module BigStep.BigStepGas where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Maybe
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import BigStep.Cast

{-
  Counts function application.
-}

infixr 6 _⇓_#_
data _⇓_#_ : Term → Term → ℕ → Set where
{-
zero⇓ : ∀{M}{N}
       --------------
     → (M ⇓ N # zero)
-}

  lit⇓ : ∀{c}{k}
       -----------
     → ($ c ⇓ $ c # suc k)
     
  lam⇓ : ∀{N}{k}
       -----------
     → (ƛ N ⇓ ƛ N # suc k)
     
  app⇓ : ∀{L M N W V k}
     → L ⇓ ƛ N # (suc k)
     → M ⇓ W # (suc k)
     → Value W
     → N [ W ] ⇓ V # k
     → Value V
       -------------------
     → L · M ⇓ V # (suc k)
     
  app⇓-blame-L : ∀{L M}{k}
     → L ⇓ blame # (suc k)
       -----------------------
     → L · M ⇓ blame # (suc k)
     
  app⇓-blame-R : ∀{L M V}{k}
     → L ⇓ V # (suc k)
     → Value V
     → M ⇓ blame # (suc k)
       ---------------------
     → L · M ⇓ blame # suc k

  app⇓blame : ∀{L M N W k}
     → L ⇓ ƛ N # (suc k)
     → M ⇓ W # (suc k)
     → Value W
     → N [ W ] ⇓ blame # k
       -------------------
     → L · M ⇓ blame # (suc k)

  inj⇓ : ∀{M V G}{k}
     → M ⇓ V # (suc k)
     → Value V
       -----------------------------
     → M ⟨ G !⟩ ⇓ V ⟨ G !⟩ # (suc k)
     
  inj⇓-blame : ∀{M G}{k}
     → M ⇓ blame # (suc k)
       --------------------------
     → M ⟨ G !⟩ ⇓ blame # (suc k)
     
  proj⇓-blame : ∀{M H}{k}
     → M ⇓ blame # (suc k)
       --------------------------
     → M ⟨ H ?⟩ ⇓ blame # (suc k)
  
  collapse⇓ : ∀{M V G}{k}
     → M ⇓ V ⟨ G !⟩ # (suc k)
       ----------------------
     → M ⟨ G ?⟩ ⇓ V # (suc k)
  
  collide⇓ : ∀{M V G H}{k}
     → M ⇓ V ⟨ G !⟩ # (suc k)
     → G ≢ H
       ---------------------------
     → M ⟨ H ?⟩ ⇓ blame # (suc k)
  
  blame⇓ : ∀{k}
       -----------------------
     → blame ⇓ blame # (suc k)

{-
downClosed⇓ : ∀{M}{N}{k}{j}
  → M ⇓ N # k
  → j ≤ k
  → M ⇓ N # j
downClosed⇓ {M} {N} {zero} {.zero} M⇓N z≤n = zero⇓
downClosed⇓ {M} {N} {suc k} {.zero} M⇓N z≤n = zero⇓
downClosed⇓ {.($ _)} {.($ _)} {suc k} {suc j} lit⇓ (s≤s j≤k) = lit⇓
downClosed⇓ {.(ƛ _)} {.(ƛ _)} {suc k} {suc j} lam⇓ (s≤s j≤k) = lam⇓
downClosed⇓ {.(_ · _)} {N} {suc k} {suc j} (app⇓ L⇓λN M⇓W w NW⇓V) (s≤s j≤k) =
   app⇓ (downClosed⇓ L⇓λN (s≤s j≤k)) (downClosed⇓ M⇓W (s≤s j≤k))
         w (downClosed⇓ NW⇓V j≤k)
downClosed⇓ {.(_ · _)} {.blame} {suc k} {suc j} (app⇓-blame-L M⇓N) (s≤s j≤k) =
   app⇓-blame-L (downClosed⇓ M⇓N (s≤s j≤k))
downClosed⇓ {.(_ · _)} {.blame} {suc k} {suc j} (app⇓-blame-R L⇓V v M⇓W)
   (s≤s j≤k) =
   app⇓-blame-R (downClosed⇓ L⇓V (s≤s j≤k)) v (downClosed⇓ M⇓W (s≤s j≤k))
downClosed⇓ {.(_ ⟨ _ !⟩)} {.(_ ⟨ _ !⟩)} {suc k} {suc j} (inj⇓ M⇓V v)
   (s≤s j≤k) =
   inj⇓ (downClosed⇓ M⇓V (s≤s j≤k)) v
downClosed⇓ {.(_ ⟨ _ !⟩)} {.blame} {suc k} {suc j} (inj⇓-blame M⇓N) (s≤s j≤k) =
   inj⇓-blame (downClosed⇓ M⇓N (s≤s j≤k))
downClosed⇓ {.(_ ⟨ _ ?⟩)} {.blame} {suc k} {suc j} (proj⇓-blame M⇓N) (s≤s j≤k) =
  proj⇓-blame (downClosed⇓ M⇓N (s≤s j≤k))
downClosed⇓ {.(_ ⟨ _ ?⟩)} {N} {suc k} {suc j} (collapse⇓ M⇓N) (s≤s j≤k) =
  collapse⇓ (downClosed⇓ M⇓N (s≤s j≤k))
downClosed⇓ {.(_ ⟨ _ ?⟩)} {.blame} {suc k} {suc j} (collide⇓ M⇓N x) (s≤s j≤k) =
  collide⇓ (downClosed⇓ M⇓N (s≤s j≤k)) x
downClosed⇓ {.blame} {.blame} {suc k} {suc j} blame⇓ (s≤s j≤k) = blame⇓
-}
