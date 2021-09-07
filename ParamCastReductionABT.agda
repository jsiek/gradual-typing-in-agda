open import Types
open import PreCastStructure
open import CastStructureABT
open import Labels
open import Data.Nat
open import Data.Product
  using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Data.Maybe
open import Variables
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  renaming (subst to subst-eq)
open import Data.Empty using (⊥; ⊥-elim)
open import Utils using (case_of_)

open import Syntax using (Sig; Rename; _•_; id; ↑; ⇑)


{-
  This modules defines reduction for the Parameterized Cast Calculus
  and provides proofs of both progress and preservation.
-}


module ParamCastReductionABT (cs : CastStruct) where

  open CastStruct cs

  open import ParamCastCalculusABT precast
  open import ParamCastAuxABT precast

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
  -}

  infix 2 _—→_

  data _—→_ : Term → Term → Set where

    ξ : ∀ {M M′ : Term} {F : Frame}
      → M —→ M′
        ---------------------
      → plug M F —→ plug M′ F

    ξ-blame : ∀ {F : Frame} {ℓ}
        ---------------------------
      → plug (blame ℓ) F —→ blame ℓ

    β : ∀ {A} {N : Term} {W : Term}
      → Value W
        --------------------
      → (ƛ A ˙ N) · W —→ N [ W ]

    δ : ∀ {A B} {f : rep A → rep B} {k : rep A}
          {ab : Prim (A ⇒ B)} {a : Prim A} {b : Prim B}
        ---------------------------------------------------
      → ($ f # ab) · ($ k # a) —→ ($ f k # b)

    β-if-true :  ∀ {M N : Term} {p : Prim (` 𝔹)}
        -------------------------------------------
      → if ($ true # p) then M else N endif —→ M

    β-if-false :  ∀ {M N : Term} {p : Prim (` 𝔹)}
        ------------------------------------------
      → if ($ false # p) then M else N endif —→ N

    β-fst :  ∀ {V W : Term}
      → Value V → Value W
        --------------------
      → fst ⟦ V , W ⟧ —→ V

    β-snd :  ∀ {V W : Term}
      → Value V → Value W
        --------------------
      → snd ⟦ V , W ⟧ —→ W

    β-caseL : ∀ {A B} {V M N : Term}
      → Value V
        --------------------------
      → case (inl V other B) of A ⇒ M ∣ B ⇒ N —→ M [ V ]

    β-caseR : ∀ {A B} {V M N : Term}
      → Value V
        --------------------------
      → case (inr V other A) of A ⇒ M ∣ B ⇒ N —→ N [ V ]

    cast : ∀ {A B} {V : Term} {c : Cast (A ⇒ B)}
      → (v : Value V) → {a : Active c}
        ------------------------------
      → V ⟨ c ⟩ —→ applyCast V v c {a}

    wrap : ∀ {A B} {V : Term} {c : Cast (A ⇒ B)}
      → (v : Value V) → {i : Inert c}
        ------------------------------
      → V ⟨ c ⟩ —→ V ⟨ c ₍ i ₎⟩

    -- Fire the following rules when the cast is both cross and inert.
    fun-cast : ∀ {A B C D} {V W : Term} {c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}
      → Value V → Value W
      → {x : Cross c} → {i : Inert c}
        --------------------------------------------------
      → V ⟨ c ₍ i ₎⟩ · W —→ (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩

    fst-cast : ∀ {A B C D} {V : Term} {c : Cast ((A `× B) ⇒ (C `× D))}
      → Value V
      → {x : Cross c} → {i : Inert c}
        -------------------------------------
      → fst (V ⟨ c ₍ i ₎⟩) —→ (fst V) ⟨ fstC c x ⟩

    snd-cast : ∀ {A B C D} {V : Term} {c : Cast ((A `× B) ⇒ (C `× D))}
      → Value V
      → {x : Cross c} → {i : Inert c}
        -------------------------------------
      → snd (V ⟨ c ₍ i ₎⟩) —→ (snd V) ⟨ sndC c x ⟩

    case-cast : ∀ {A B C D} {V M N : Term} {c : Cast (A `⊎ B ⇒ C `⊎ D)}
      → Value V
      → {x : Cross c} → {i : Inert c}
        --------------------------------------------
      → case (V ⟨ c ₍ i ₎⟩) of C ⇒ M ∣ D ⇒ N
           —→
         case V of A ⇒ (rename ⇑ M [ ` 0 ⟨ inlC c x ⟩ ])
                 ∣ B ⇒ (rename ⇑ N [ ` 0 ⟨ inrC c x ⟩ ])
