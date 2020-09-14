open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe


open import Types
open import Variables
open import Labels
open import PreCastStructure
open import CastStructure



-- Module definition - parameterized by `CastStruct` .
module ParamCastSubtyping (cs : CastStruct) where

open CastStruct cs

import ParamCastCalculus
open ParamCastCalculus Cast

import ParamCastAux
open ParamCastAux precast

import ParamCastReduction
open ParamCastReduction cs



-- Data type `CastsRespect<:` says all casts in M with blame label ℓ respect subtyping.
data CastsRespect<: : ∀ {Γ A} → (M : Γ ⊢ A) → (ℓ : Label) → Set where

  -- {- NOTE:
  --   If the cast has the same blame label as ℓ , which is what the data type is quantified over,
  --   we require that the source & target types respect subtyping <: .
  -- -}
  CR<:-cast-same-ℓ : ∀ {Γ S T} {M : Γ ⊢ S} {c : Cast (S ⇒ T)} {ℓ}
    → Safe c
    → labC c ≡ just ℓ
    → CastsRespect<: M ℓ
      -------------------------------------
    → CastsRespect<: (M ⟨ c ⟩) ℓ

  -- {- NOTE:
  --   If the blame label ℓ′ on the cast is different from what the data type is quantified over,
  --   this is fine and we don't impose any restriction on this cast.
  -- -}
  CR<:-cast-diff-ℓ : ∀ {Γ S T} {M : Γ ⊢ S} {c : Cast (S ⇒ T)} {ℓ}
    → labC c ≢ just ℓ
    → CastsRespect<: M ℓ
      ----------------------------------------------
    → CastsRespect<: (M ⟨ c ⟩) ℓ

  CR<:-var : ∀ {Γ A} {x : Γ ∋ A} {ℓ}
      ------------------------------
    → CastsRespect<: (` x) ℓ

  CR<:-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {ℓ}
    → CastsRespect<: N ℓ
      -----------------------
    → CastsRespect<: (ƛ N) ℓ

  CR<:-· : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} {ℓ}
    → CastsRespect<: L ℓ
    → CastsRespect<: M ℓ
      -------------------------
    → CastsRespect<: (L · M) ℓ

  CR<:-prim : ∀ {Γ A} {p : rep A} {f : Prim A} {ℓ}
      --------------------------------------------
    → CastsRespect<: ($_ {Γ} p {f}) ℓ

  CR<:-if : ∀ {Γ A} {L : Γ ⊢ ` 𝔹} {M : Γ ⊢ A} {N : Γ ⊢ A} {ℓ}
    → CastsRespect<: L ℓ
    → CastsRespect<: M ℓ
    → CastsRespect<: N ℓ
      -----------------------------
    → CastsRespect<: (if L M N) ℓ

  CR<:-cons : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ ⊢ B} {ℓ}
    → CastsRespect<: M ℓ
    → CastsRespect<: N ℓ
      ----------------------------
    → CastsRespect<: (cons M N) ℓ

  CR<:-fst : ∀ {Γ A B} {M : Γ ⊢ A `× B} {ℓ}
    → CastsRespect<: M ℓ
      -------------------------
    → CastsRespect<: (fst M) ℓ

  CR<:-snd : ∀ {Γ A B} {M : Γ ⊢ A `× B} {ℓ}
    → CastsRespect<: M ℓ
      -------------------------
    → CastsRespect<: (snd M) ℓ

  CR<:-inl : ∀ {Γ A B} {M : Γ ⊢ A} {ℓ}
    → CastsRespect<: M ℓ
      ---------------------------------
    → CastsRespect<: (inl {B = B} M) ℓ

  CR<:-inr : ∀ {Γ A B} {N : Γ ⊢ B} {ℓ}
    → CastsRespect<: N ℓ
      ----------------------------------
    → CastsRespect<: (inr {A = A} N) ℓ

  CR<:-case : ∀ {Γ A B C} {L : Γ ⊢ A `⊎ B} {M : Γ ⊢ A ⇒ C} {N : Γ ⊢ B ⇒ C} {ℓ}
    → CastsRespect<: L ℓ
    → CastsRespect<: M ℓ
    → CastsRespect<: N ℓ
      ------------------------------
    → CastsRespect<: (case L M N) ℓ

  {- NOTE:
    A well-typed surface language term can never be compiled into a blame in the cast calculus (CC).
    However we still have a case for `blame ℓ` here since it has such a case in CC.
  -}
  CR<:-blame-diff-ℓ : ∀ {Γ A} {ℓ ℓ′}
    → ℓ ≢ ℓ′
      ------------------------------------
    → CastsRespect<: (blame {Γ} {A} ℓ′) ℓ


plug-blame-CR<:-inv : ∀ {Γ A B} {F : Frame {Γ = Γ} A B} {ℓ ℓ′}
  → CastsRespect<: (plug (blame ℓ′) F) ℓ
    -------------------------------------
  → ℓ ≢ ℓ′
plug-blame-CR<:-inv {F = F-·₁ _} (CR<:-· (CR<:-blame-diff-ℓ ℓ≢ℓ′) _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-·₂ _} (CR<:-· _ (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-if _ _} (CR<:-if (CR<:-blame-diff-ℓ ℓ≢ℓ′) _ _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-×₁ _} (CR<:-cons _ (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-×₂ _} (CR<:-cons (CR<:-blame-diff-ℓ ℓ≢ℓ′) _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-fst} (CR<:-fst (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-snd} (CR<:-snd (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-inl} (CR<:-inl (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-inr} (CR<:-inr (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-case _ _} (CR<:-case (CR<:-blame-diff-ℓ ℓ≢ℓ′) _ _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-cast _} (CR<:-cast-same-ℓ _ _ (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-CR<:-inv {F = F-cast _} (CR<:-cast-diff-ℓ _ (CR<:-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′

preserve-CR<:-plug : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B} {ℓ}
  → CastsRespect<: (plug M F) ℓ
  → M —→ M′
    -----------------------------
  → CastsRespect<: (plug M′ F) ℓ

preserve-CR<: : ∀ {Γ A} {M M′ : Γ ⊢ A} {ℓ}
    → CastsRespect<: M ℓ
    → M —→ M′
      --------------------
    → CastsRespect<: M′ ℓ

preserve-CR<:-plug {M = L} {L′} {F = F-·₁ M} (CR<:-· resp-L resp-M) rd = CR<:-· (preserve-CR<: resp-L rd) resp-M
preserve-CR<:-plug {F = F-·₂ L {v}} (CR<:-· resp-L resp-M) rd = CR<:-· resp-L (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-if M N} (CR<:-if resp-L resp-M resp-N) rd = CR<:-if (preserve-CR<: resp-L rd ) resp-M resp-N
preserve-CR<:-plug {F = F-×₁ M} (CR<:-cons resp-M resp-N) rd = CR<:-cons resp-M (preserve-CR<: resp-N rd)
preserve-CR<:-plug {F = F-×₂ N} (CR<:-cons resp-M resp-N) rd = CR<:-cons (preserve-CR<: resp-M rd) resp-N
preserve-CR<:-plug {F = F-fst} (CR<:-fst resp-M) rd = CR<:-fst (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-snd} (CR<:-snd resp-M) rd = CR<:-snd (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-inl} (CR<:-inl resp-M) rd = CR<:-inl (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-inr} (CR<:-inr resp-M) rd = CR<:-inr (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-case M N} (CR<:-case resp-L resp-M resp-N) rd = CR<:-case (preserve-CR<: resp-L rd) resp-M resp-N
preserve-CR<:-plug {F = F-cast c} (CR<:-cast-same-ℓ safe eq resp-M) rd = CR<:-cast-same-ℓ safe eq (preserve-CR<: resp-M rd)
preserve-CR<:-plug {F = F-cast c} (CR<:-cast-diff-ℓ neq resp-M) rd = CR<:-cast-diff-ℓ neq (preserve-CR<: resp-M rd)

preserve-CR<: resp (ξ rd) = preserve-CR<:-plug resp rd
preserve-CR<: resp ξ-blame = CR<:-blame-diff-ℓ (plug-blame-CR<:-inv resp)
-- Need to prove substitution preserves `CR<:` .
preserve-CR<: (CR<:-· (CR<:-ƛ resp-N) resp-W) (β v) = {!!}
preserve-CR<: resp δ = CR<:-prim
preserve-CR<: (CR<:-if _ resp-M _) β-if-true = resp-M
preserve-CR<: (CR<:-if _ _ resp-M′) β-if-false = resp-M′
preserve-CR<: (CR<:-fst (CR<:-cons resp-M _)) (β-fst _ _) = resp-M
preserve-CR<: (CR<:-snd (CR<:-cons _ resp-N)) (β-snd _ _) = resp-N
preserve-CR<: (CR<:-case (CR<:-inl resp) resp-M _) (β-caseL x) = CR<:-· resp-M resp
preserve-CR<: (CR<:-case (CR<:-inr resp) _ resp-N) (β-caseR x) = CR<:-· resp-N resp
preserve-CR<: (CR<:-cast-same-ℓ safe eq resp) (cast v {a}) = {!!}
preserve-CR<: (CR<:-cast-diff-ℓ neq resp) (cast v {a}) = {!!}
-- CR<: (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩
preserve-CR<: (CR<:-· (CR<:-cast-same-ℓ safe eq resp-V) resp-W) (fun-cast {c = c} vV vW {x}) =
  -- Here we expect a proof that `labC c ≡ labC (dom c x)` , where `c` is a function cast.
  let dom-eq = subst-eq (λ □ → □ ≡ just _) (domLabEq c x) eq in
  let cod-eq = subst-eq (λ □ → □ ≡ just _) (codLabEq c x) eq in
    CR<:-cast-same-ℓ (codSafe safe x) cod-eq (CR<:-· resp-V (CR<:-cast-same-ℓ (domSafe safe x) dom-eq resp-W))
preserve-CR<: (CR<:-· (CR<:-cast-diff-ℓ neq resp-V) resp-W) (fun-cast {c = c} vV vW {x}) =
  let dom-neq = subst-eq (λ □ → □ ≢ just _) (domLabEq c x) neq in
  let cod-neq = subst-eq (λ □ → □ ≢ just _) (codLabEq c x) neq in
    CR<:-cast-diff-ℓ cod-neq (CR<:-· resp-V (CR<:-cast-diff-ℓ dom-neq resp-W))
preserve-CR<: (CR<:-fst (CR<:-cast-same-ℓ safe eq resp-V)) (fst-cast {c = c} vV {x}) =
  let fst-eq = subst-eq (λ □ → □ ≡ just _) (fstLabEq c x) eq in
    CR<:-cast-same-ℓ (fstSafe safe x) fst-eq (CR<:-fst resp-V)
preserve-CR<: (CR<:-fst (CR<:-cast-diff-ℓ neq resp-V)) (fst-cast {c = c} vV {x}) =
  let fst-neq = subst-eq (λ □ → □ ≢ just _) (fstLabEq c x) neq in
    CR<:-cast-diff-ℓ fst-neq (CR<:-fst resp-V)
preserve-CR<: (CR<:-snd (CR<:-cast-same-ℓ safe eq resp-V)) (snd-cast {c = c} vV {x}) =
  let snd-eq = subst-eq (λ □ → □ ≡ just _) (sndLabEq c x) eq in
    CR<:-cast-same-ℓ (sndSafe safe x) snd-eq (CR<:-snd resp-V)
preserve-CR<: (CR<:-snd (CR<:-cast-diff-ℓ neq resp-V)) (snd-cast {c = c} vV {x}) =
  let snd-neq = subst-eq (λ □ → □ ≢ just _) (sndLabEq c x) neq in
    CR<:-cast-diff-ℓ snd-neq (CR<:-snd resp-V)
preserve-CR<: (CR<:-case (CR<:-cast-same-ℓ safe eq resp-V) resp-W₁ resp-W₂) (case-cast {c = c} vV {x}) =
  let inl-eq = subst-eq (λ □ → □ ≡ just _) (inlLabEq c x) eq in
  let inr-eq = subst-eq (λ □ → □ ≡ just _) (inrLabEq c x) eq in
    CR<:-case resp-V (CR<:-ƛ (CR<:-· {!!} (CR<:-cast-same-ℓ (inlSafe safe x) inl-eq CR<:-var)))
                     (CR<:-ƛ (CR<:-· {!!} (CR<:-cast-same-ℓ (inrSafe safe x) inr-eq CR<:-var)))
preserve-CR<: (CR<:-case (CR<:-cast-diff-ℓ neq resp-V) resp-W₁ resp-W₂) (case-cast {c = c} vV {x}) =
  let inl-neq = subst-eq (λ □ → □ ≢ just _) (inlLabEq c x) neq in
  let inr-neq = subst-eq (λ □ → □ ≢ just _) (inrLabEq c x) neq in
    CR<:-case resp-V (CR<:-ƛ (CR<:-· {!!} (CR<:-cast-diff-ℓ inl-neq CR<:-var)))
                     (CR<:-ƛ (CR<:-· {!!} (CR<:-cast-diff-ℓ inr-neq CR<:-var)))

