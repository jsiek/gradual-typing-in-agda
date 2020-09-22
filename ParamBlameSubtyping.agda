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



module ParamBlameSubtyping (cs : CastStruct) where

open CastStruct cs

open import ParamCastCalculus Cast
open import ParamCastAux precast
open import ParamCastSubtyping pcss
open import ParamCastReduction cs

{- NOTE:
   To prove blame-subtyping, we first prove preservation of `CastsAllSafe` .
-}
plug-blame-allsafe-inv : ∀ {Γ A B} {F : Frame {Γ = Γ} A B} {ℓ ℓ′}
  → CastsAllSafe (plug (blame ℓ′) F) ℓ
    -------------------------------------
  → ℓ ≢̂ ℓ′
plug-blame-allsafe-inv {F = F-·₁ _} (allsafe-· (allsafe-blame-diff-ℓ ℓ≢ℓ′) _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-·₂ _} (allsafe-· _ (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-if _ _} (allsafe-if (allsafe-blame-diff-ℓ ℓ≢ℓ′) _ _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-×₁ _} (allsafe-cons _ (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-×₂ _} (allsafe-cons (allsafe-blame-diff-ℓ ℓ≢ℓ′) _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-fst} (allsafe-fst (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-snd} (allsafe-snd (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-inl} (allsafe-inl (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-inr} (allsafe-inr (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-case _ _} (allsafe-case (allsafe-blame-diff-ℓ ℓ≢ℓ′) _ _) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′
plug-blame-allsafe-inv {F = F-cast _} (allsafe-cast _ (allsafe-blame-diff-ℓ ℓ≢ℓ′)) ℓ≡ℓ′ = ℓ≢ℓ′ ℓ≡ℓ′

preserve-allsafe-plug : ∀ {Γ A B} {M M′ : Γ ⊢ A} {F : Frame A B} {ℓ}
  → CastsAllSafe (plug M F) ℓ
  → M —→ M′
    -----------------------------
  → CastsAllSafe (plug M′ F) ℓ

preserve-allsafe : ∀ {Γ A} {M M′ : Γ ⊢ A} {ℓ}
  → CastsAllSafe M ℓ
  → M —→ M′
    --------------------
  → CastsAllSafe M′ ℓ

preserve-allsafe-plug {M = L} {L′} {F = F-·₁ M} (allsafe-· allsafe-L allsafe-M) rd = allsafe-· (preserve-allsafe allsafe-L rd) allsafe-M
preserve-allsafe-plug {F = F-·₂ L {v}} (allsafe-· allsafe-L allsafe-M) rd = allsafe-· allsafe-L (preserve-allsafe allsafe-M rd)
preserve-allsafe-plug {F = F-if M N} (allsafe-if allsafe-L allsafe-M allsafe-N) rd = allsafe-if (preserve-allsafe allsafe-L rd ) allsafe-M allsafe-N
preserve-allsafe-plug {F = F-×₁ M} (allsafe-cons allsafe-M allsafe-N) rd = allsafe-cons allsafe-M (preserve-allsafe allsafe-N rd)
preserve-allsafe-plug {F = F-×₂ N} (allsafe-cons allsafe-M allsafe-N) rd = allsafe-cons (preserve-allsafe allsafe-M rd) allsafe-N
preserve-allsafe-plug {F = F-fst} (allsafe-fst allsafe-M) rd = allsafe-fst (preserve-allsafe allsafe-M rd)
preserve-allsafe-plug {F = F-snd} (allsafe-snd allsafe-M) rd = allsafe-snd (preserve-allsafe allsafe-M rd)
preserve-allsafe-plug {F = F-inl} (allsafe-inl allsafe-M) rd = allsafe-inl (preserve-allsafe allsafe-M rd)
preserve-allsafe-plug {F = F-inr} (allsafe-inr allsafe-M) rd = allsafe-inr (preserve-allsafe allsafe-M rd)
preserve-allsafe-plug {F = F-case M N} (allsafe-case allsafe-L allsafe-M allsafe-N) rd = allsafe-case (preserve-allsafe allsafe-L rd) allsafe-M allsafe-N
preserve-allsafe-plug {F = F-cast c} (allsafe-cast safe allsafe-M) rd = allsafe-cast safe (preserve-allsafe allsafe-M rd)

preserve-allsafe allsafe (ξ rd) = preserve-allsafe-plug allsafe rd
preserve-allsafe allsafe ξ-blame = allsafe-blame-diff-ℓ (plug-blame-allsafe-inv allsafe)
-- Need to prove substitution preserves `CR<:` .
preserve-allsafe (allsafe-· (allsafe-ƛ allsafe-N) allsafe-W) (β v) = substitution-allsafe allsafe-N allsafe-W
preserve-allsafe allsafe δ = allsafe-prim
preserve-allsafe (allsafe-if _ allsafe-M _) β-if-true = allsafe-M
preserve-allsafe (allsafe-if _ _ allsafe-M′) β-if-false = allsafe-M′
preserve-allsafe (allsafe-fst (allsafe-cons allsafe-M _)) (β-fst _ _) = allsafe-M
preserve-allsafe (allsafe-snd (allsafe-cons _ allsafe-N)) (β-snd _ _) = allsafe-N
preserve-allsafe (allsafe-case (allsafe-inl allsafe) allsafe-M _) (β-caseL x) = allsafe-· allsafe-M allsafe
preserve-allsafe (allsafe-case (allsafe-inr allsafe) _ allsafe-N) (β-caseR x) = allsafe-· allsafe-N allsafe
preserve-allsafe (allsafe-cast safe allsafe) (cast v {a}) = applyCast-pres-allsafe a safe allsafe
-- CR<: (V · (W ⟨ dom c x ⟩)) ⟨ cod c x ⟩
preserve-allsafe (allsafe-· (allsafe-cast safe allsafe-V) allsafe-W) (fun-cast {c = c} vV vW {x}) =
  -- Here we expect a proof that `labC c ≡ labC (dom c x)` , where `c` is a function cast.
  allsafe-cast (codSafe safe x) (allsafe-· allsafe-V (allsafe-cast (domSafe safe x) allsafe-W))
preserve-allsafe (allsafe-fst (allsafe-cast safe allsafe-V)) (fst-cast {c = c} vV {x}) =
  allsafe-cast (fstSafe safe x) (allsafe-fst allsafe-V)
preserve-allsafe (allsafe-snd (allsafe-cast safe allsafe-V)) (snd-cast {c = c} vV {x}) =
  allsafe-cast (sndSafe safe x) (allsafe-snd allsafe-V)
preserve-allsafe (allsafe-case (allsafe-cast safe allsafe-V) allsafe-W₁ allsafe-W₂) (case-cast {c = c} vV {x}) =
  allsafe-case allsafe-V (allsafe-ƛ (allsafe-· (rename-pres-allsafe S_ allsafe-W₁) (allsafe-cast (inlSafe safe x) allsafe-var)))
                         (allsafe-ƛ (allsafe-· (rename-pres-allsafe S_ allsafe-W₂) (allsafe-cast (inrSafe safe x) allsafe-var)))


-- There is no way to plug a `blame ℓ` in a frame and produce a term where every cast with label ℓ respects <: .
plug-blame→¬allsafe : ∀ {Γ A B ℓ}
  → (F : Frame {Γ} A B)
  → ¬ (CastsAllSafe (plug (blame ℓ) F) ℓ)
plug-blame→¬allsafe (F-·₁ M) (allsafe-· (allsafe-blame-diff-ℓ ℓ≢ℓ) _) = ℓ≢ℓ ≡̂-refl                               -- □ · M
plug-blame→¬allsafe (F-·₂ L) (allsafe-· _ (allsafe-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ ≡̂-refl                               -- L · □
plug-blame→¬allsafe (F-if M N) (allsafe-if (allsafe-blame-diff-ℓ ℓ≢ℓ) _ _) = ℓ≢ℓ ≡̂-refl                          -- if □ M N
plug-blame→¬allsafe (F-×₁ M) (allsafe-cons _ (allsafe-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ ≡̂-refl                            -- cons M □
plug-blame→¬allsafe (F-×₂ L) (allsafe-cons (allsafe-blame-diff-ℓ ℓ≢ℓ) _) = ℓ≢ℓ ≡̂-refl                            -- cons □ L
plug-blame→¬allsafe F-fst (allsafe-fst (allsafe-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ ≡̂-refl                                  -- fst □
plug-blame→¬allsafe F-snd (allsafe-snd (allsafe-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ ≡̂-refl                                  -- snd □
plug-blame→¬allsafe F-inl (allsafe-inl (allsafe-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ ≡̂-refl                                  -- inl □
plug-blame→¬allsafe F-inr (allsafe-inr (allsafe-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ ≡̂-refl                                  -- inr □
plug-blame→¬allsafe (F-case M N) (allsafe-case (allsafe-blame-diff-ℓ ℓ≢ℓ) _ _) = ℓ≢ℓ ≡̂-refl                      -- case □ M N
plug-blame→¬allsafe (F-cast _) (allsafe-cast _ (allsafe-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ ≡̂-refl


-- Lemma:
blame↠blame→ℓ≡ : ∀ {Γ A} {ℓ₁ ℓ₂}
  → (rd* : blame {Γ} {A} ℓ₁ —↠ blame {Γ} {A} ℓ₂)
    ----------------------------------------------
  → ℓ₁ ≡ ℓ₂
blame↠blame→ℓ≡ (.(blame _) ∎) = refl
blame↠blame→ℓ≡ (.(blame _) —→⟨ rd ⟩ rd*) = ⊥-elim (blame⌿→ rd)



{- NOTE:
  If every cast in the term M with blame label ℓ is safe (respects subtyping), then M ⌿↠ blame ℓ .
-}
soundness-<: : ∀ {Γ A} {M : Γ ⊢ A} {ℓ}
  → CastsAllSafe M ℓ
  → ¬ (M —↠ blame ℓ)
-- By induction on M —↠ blame ℓ .
soundness-<: allsafe-plugMF ( .(plug _ _) —→⟨ ξ M→M′ ⟩ plugM′F↠blame ) =
  -- In this case we need to prove that single step reduction preserves `CastsRespect<:` .
  soundness-<: (preserve-allsafe allsafe-plugMF (ξ M→M′)) plugM′F↠blame
-- There is no way to plug a `blame ℓ` in a frame and produce a term where every cast with ℓ respects <: .
soundness-<: allsafe ( .(plug (blame _) _) —→⟨ ξ-blame {F = F} ⟩ blame↠blame ) =
  let ℓ₁≡ℓ = blame↠blame→ℓ≡ blame↠blame in
    plug-blame→¬allsafe F (subst-eq (λ □ → CastsAllSafe (plug (blame □) _) _) ℓ₁≡ℓ allsafe)
-- Application (β).
soundness-<: {M = (ƛ N) · W} (allsafe-· (allsafe-ƛ allsafe-N) allsafe-W) ( .((ƛ N) · W) —→⟨ β vW ⟩ N[W]↠blame ) =
  {-
    We need to prove that given Γ , A ⊢ N ⦂ B and Γ ⊢ W ⦂ A that both satisfy `CastsRespect<:`,
    the substituted term N [ W ] also satisfies `CastsRespect<:` - single substitution preserves `CastsRespect<:` .
  -}
  soundness-<: (substitution-allsafe allsafe-N allsafe-W) N[W]↠blame
-- This case corresponds to the δ rule.
soundness-<: (allsafe-· allsafe-f allsafe-k) ( .(($ _) · ($ _)) —→⟨ δ ⟩ fk↠blame ) =
    soundness-<: allsafe-prim fk↠blame
-- If
soundness-<: {M = if ($ true) M N} (allsafe-if _ allsafe-M _) ( .(if ($ true) M N) —→⟨ β-if-true ⟩ M↠blame ) =
    soundness-<: allsafe-M M↠blame
soundness-<: {M = if ($ false) M N} (allsafe-if _ _ allsafe-N) ( .(if ($ false) M N) —→⟨ β-if-false ⟩ N↠blame ) =
    soundness-<: allsafe-N N↠blame
-- Fst & snd
soundness-<: (allsafe-fst (allsafe-cons allsafe-V allsafe-W)) ( .(fst (cons _ _)) —→⟨ β-fst vV vW ⟩ V↠blame ) =
    -- Another way to do this is to prove that V cannot step to blame.
    soundness-<: allsafe-V V↠blame
soundness-<: (allsafe-snd (allsafe-cons allsafe-V allsafe-W)) ( .(snd (cons _ _)) —→⟨ β-snd vV vW ⟩ W↠blame ) =
    soundness-<: allsafe-W W↠blame
-- Case
soundness-<: (allsafe-case (allsafe-inl allsafe-V) allsafe-L _) ( .(case (inl _) _ _) —→⟨ β-caseL vV ⟩ L·V↠blame ) =
    soundness-<: (allsafe-· allsafe-L allsafe-V) L·V↠blame
soundness-<: (allsafe-case (allsafe-inr allsafe-V) _ allsafe-M) ( .(case (inr _) _ _) —→⟨ β-caseR vV ⟩ M·V↠blame ) =
    soundness-<: (allsafe-· allsafe-M allsafe-V) M·V↠blame
-- Cast
soundness-<: (allsafe-cast safe allsafe-V) ((V ⟨ c ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ) =
  soundness-<: (applyCast-pres-allsafe a safe allsafe-V) applyCastVc↠blame
-- Fun-cast
soundness-<: (allsafe-· (allsafe-cast safe allsafe-V) allsafe-W) ((V ⟨ c ⟩ · W) —→⟨ fun-cast vV vW {x} ⟩ V·W↠blame) =
    soundness-<: (allsafe-cast (codSafe safe x) (allsafe-· allsafe-V (allsafe-cast (domSafe safe x) allsafe-W))) V·W↠blame
-- Fst-cast & snd-cast
soundness-<: (allsafe-fst (allsafe-cast safe allsafe-V)) ( (fst (V ⟨ c ⟩)) —→⟨ fst-cast _ {x} ⟩ fstV⟨fstc⟩↠blame ) =
    soundness-<: (allsafe-cast (fstSafe safe x) (allsafe-fst allsafe-V)) fstV⟨fstc⟩↠blame
soundness-<: (allsafe-snd (allsafe-cast safe allsafe-V)) ( (snd (V ⟨ c ⟩)) —→⟨ snd-cast _ {x} ⟩ sndV⟨sndc⟩↠blame ) =
    soundness-<: (allsafe-cast (sndSafe safe x) (allsafe-snd allsafe-V)) sndV⟨sndc⟩↠blame
-- Case-cast
soundness-<: (allsafe-case (allsafe-cast safe allsafe-V) allsafe-W₁ allsafe-W₂) ( (case (V ⟨ c ⟩) W₁ W₂) —→⟨ case-cast vV {x} ⟩ ↠blame ) =
    soundness-<: (allsafe-case allsafe-V (allsafe-ƛ (allsafe-· (rename-pres-allsafe S_ allsafe-W₁)
                                                               (allsafe-cast (inlSafe safe x) allsafe-var)))
                                         (allsafe-ƛ (allsafe-· (rename-pres-allsafe S_ allsafe-W₂)
                                                               (allsafe-cast (inrSafe safe x) allsafe-var)))) ↠blame
-- Blame
soundness-<: (allsafe-blame-diff-ℓ ℓ≢ℓ) ((blame ℓ) ∎) = ℓ≢ℓ ≡̂-refl

