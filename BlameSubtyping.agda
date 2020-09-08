open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂; inspect; [_])
  renaming (subst to subst-eq; subst₂ to subst₂-eq)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)

-- We're using simple cast - at least for now.
open import SimpleCast using (Cast; Active; Cross; applyCast; pcs; cs; dom; cod)
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast
import ParamCastAux
open ParamCastAux pcs using (Value; Frame; plug)
import ParamCastReduction
open ParamCastReduction cs
import ParamCastReductionNoFrame
open ParamCastReductionNoFrame cs renaming (_—→_ to _—→′_; _—↠_ to _—↠′_)
open import CastSubtyping using (CastsRespect<:; _<:_)



-- Test
-- M : ∅ ⊢ ⋆
-- M = ($_ zero {Prim.P-Base}) ⟨ _⇒⟨_⟩_ (` Nat) (Label.pos zero) ⋆ {unk~R} ⟩


open Value

-- Experimental
rd→rd′ : ∀ {Γ A} {M M′ : Γ ⊢ A}
  → M —→ M′
  → M —→′ M′
rd→rd′ (ξ {F = ParamCastAux.F-·₁ _} rd) = ξ-·₁ (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-·₂ _ {v = v}} rd) = ξ-·₂ {v = v} (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-if _ _} rd) = ξ-if (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-×₁ _} rd) = ξ-×₂ (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-×₂ _} rd) = ξ-x₁ (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-fst} rd) = ξ-fst (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-snd} rd) = ξ-snd (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-inl} rd) = ξ-inl (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-inr} rd) = ξ-inr (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-case _ _} rd) = ξ-case (rd→rd′ rd)
rd→rd′ (ξ {F = ParamCastAux.F-cast _} rd) = ξ-cast (rd→rd′ rd)
rd→rd′ (ξ-blame {F = ParamCastAux.F-·₁ _}) = ξ-blame-·₁
rd→rd′ (ξ-blame {F = ParamCastAux.F-·₂ _ {v = v}}) = (ξ-blame-·₂ {v = v})
rd→rd′ (ξ-blame {F = ParamCastAux.F-if _ _}) = ξ-blame-if
rd→rd′ (ξ-blame {F = ParamCastAux.F-×₁ _}) = ξ-blame-×₂
rd→rd′ (ξ-blame {F = ParamCastAux.F-×₂ _}) = ξ-blame-x₁
rd→rd′ (ξ-blame {F = ParamCastAux.F-fst}) = ξ-blame-fst
rd→rd′ (ξ-blame {F = ParamCastAux.F-snd}) = ξ-blame-snd
rd→rd′ (ξ-blame {F = ParamCastAux.F-inl}) = ξ-blame-inl
rd→rd′ (ξ-blame {F = ParamCastAux.F-inr}) = ξ-blame-inr
rd→rd′ (ξ-blame {F = ParamCastAux.F-case _ _}) = ξ-blame-case
rd→rd′ (ξ-blame {F = ParamCastAux.F-cast _}) = ξ-blame-cast
rd→rd′ (β v) = β v
rd→rd′ δ = δ
rd→rd′ β-if-true = β-if-true
rd→rd′ β-if-false = β-if-false
rd→rd′ (β-fst vv vw) = β-fst vv vw
rd→rd′ (β-snd vv vw) = β-snd vv vw
rd→rd′ (β-caseL v) = β-caseL v
rd→rd′ (β-caseR v) = β-caseR v
rd→rd′ (cast v) = cast v
rd→rd′ (fun-cast v vv {x = x}) = fun-cast v vv {x = x}
rd→rd′ (fst-cast v {x = x}) = fst-cast v {x = x}
rd→rd′ (snd-cast v {x = x}) = snd-cast v {x = x}
rd→rd′ (case-cast v {x = x}) = case-cast v {x = x}

-- Values do not reduce.
-- V⌿→ : ∀ {Γ A} {M N : Γ ⊢ A}
--     → Value M
--     → ¬ (M —→ N)

-- Blame does not reduce.
blame⌿→ : ∀ {Γ A} {M : Γ ⊢ A} {ℓ}
    → ¬ (blame {Γ} {A} ℓ —→ M)
blame⌿→ rd with rd→rd′ rd
... | ()

open CastsRespect<:
open Frame
open _<:_

-- There is no way to plug a `blame ℓ` in a frame and produce a term where every cast with label ℓ respects <: .
plug-blame→¬respect<: : ∀ {Γ A B ℓ}
  → (F : Frame {Γ} A B)
  → ¬ (CastsRespect<: (plug (blame ℓ) F) ℓ)
plug-blame→¬respect<: (F-·₁ M) (CR<:-· (CR<:-blame-diff-ℓ ℓ≢ℓ) _) = ℓ≢ℓ refl                               -- □ · M
plug-blame→¬respect<: (F-·₂ L) (CR<:-· _ (CR<:-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ refl                               -- L · □
plug-blame→¬respect<: (F-if M N) (CR<:-if (CR<:-blame-diff-ℓ ℓ≢ℓ) _ _) = ℓ≢ℓ refl                          -- if □ M N
plug-blame→¬respect<: (F-×₁ M) (CR<:-cons _ (CR<:-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ refl                            -- cons M □
plug-blame→¬respect<: (F-×₂ L) (CR<:-cons (CR<:-blame-diff-ℓ ℓ≢ℓ) _) = ℓ≢ℓ refl                            -- cons □ L
plug-blame→¬respect<: F-fst (CR<:-fst (CR<:-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ refl                                  -- fst □
plug-blame→¬respect<: F-snd (CR<:-snd (CR<:-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ refl                                  -- snd □
plug-blame→¬respect<: F-inl (CR<:-inl (CR<:-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ refl                                  -- inl □
plug-blame→¬respect<: F-inr (CR<:-inr (CR<:-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ refl                                  -- inr □
plug-blame→¬respect<: (F-case M N) (CR<:-case (CR<:-blame-diff-ℓ ℓ≢ℓ) _ _) = ℓ≢ℓ refl                      -- case □ M N
plug-blame→¬respect<: (F-cast _) (CR<:-cast-same-ℓ _ (CR<:-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ refl -- □ ⟨ c ⟩
plug-blame→¬respect<: (F-cast _) (CR<:-cast-diff-ℓ _ (CR<:-blame-diff-ℓ ℓ≢ℓ)) = ℓ≢ℓ refl

-- A term does not blame on ℓ. The data type is useful when discriminating on the reduction.
data NotBlameℓ : ∀ {Γ A} → Γ ⊢ A → Label → Set where

  blame-diff-ℓ : ∀ {Γ A} {M : Γ ⊢ A} {ℓ}
    → ∃[ ℓ′ ] ((M ≡ blame ℓ′) × (ℓ ≢ ℓ′))
      ------------------------------------
    → NotBlameℓ M ℓ

  `-not-blame : ∀ {Γ A} {M : Γ ⊢ A} {ℓ}
    → ∃[ x ] (M ≡ ` x)
      -----------------
    → NotBlameℓ M ℓ

  ƛ-not-blame : ∀ {Γ B A} {M : Γ ⊢ A ⇒ B} {ℓ}
    → ∃[ N ] (M ≡ ƛ N)
      -----------------
    → NotBlameℓ M ℓ

  ·-not-blame : ∀ {Γ A B} {M : Γ ⊢ B} {ℓ}
    → Σ[ L ∈ Γ ⊢ A ⇒ B ] ∃[ N ] (M ≡ L · N)
      ---------------------------------------
    → NotBlameℓ M ℓ

  $-not-blame : ∀ {Γ A} {p : rep A} {f : Prim A} {M : Γ ⊢ A} {ℓ}
    → ∃[ p ] (M ≡ $_ {Γ} p {f})
      --------------------------
    → NotBlameℓ M ℓ

  if-not-blame : ∀ {Γ A} {M : Γ ⊢ A} {ℓ}
    → ∃[ L ] ∃[ N₁ ] ∃[ N₂ ] (M ≡ if L N₁ N₂)
      ----------------------------------------
    → NotBlameℓ M ℓ

  cons-not-blame : ∀ {Γ A B} {M : Γ ⊢ A `× B} {ℓ}
    → ∃[ L ] ∃[ N ] (M ≡ cons L N)
      ----------------------------
    → NotBlameℓ M ℓ

  fst-not-blame : ∀ {Γ A B} {M : Γ ⊢ A} {ℓ}
    → Σ[ N ∈ Γ ⊢ A `× B ] (M ≡ fst N)
      -------------------------------
    → NotBlameℓ M ℓ

  snd-not-blame : ∀ {Γ A B} {M : Γ ⊢ B} {ℓ}
    → Σ[ N ∈ Γ ⊢ A `× B ] (M ≡ snd N)
      --------------------------------
    → NotBlameℓ M ℓ

  inl-not-blame : ∀ {Γ A B} {M : Γ ⊢ A `⊎ B} {ℓ}
    → ∃[ N ] (M ≡ inl N)
      -------------------
    → NotBlameℓ M ℓ

  inr-not-blame : ∀ {Γ A B} {M : Γ ⊢ A `⊎ B} {ℓ}
    → ∃[ N ] (M ≡ inr N)
      -------------------
    → NotBlameℓ M ℓ

  case-not-blame : ∀ {Γ A B C} {M : Γ ⊢ C} {ℓ}
    → Σ[ L ∈ Γ ⊢ A `⊎ B ] ∃[ N₁ ] ∃[ N₂ ] (M ≡ case L N₁ N₂)
      -------------------------------------------------------
    → NotBlameℓ M ℓ

  cast-not-blame : ∀ {Γ A B} {M : Γ ⊢ B} {ℓ}
    → Σ[ N ∈ Γ ⊢ A ] ∃[ c ] (M ≡ N ⟨ c ⟩)
      ------------------------------------
    → NotBlameℓ M ℓ

-- -- A value V is not blame.
value-not-blame : ∀ {Γ A} {V : Γ ⊢ A} {ℓ}
  → (vV : Value V)
    ---------------
  → NotBlameℓ V ℓ
value-not-blame V-ƛ = ƛ-not-blame (⟨ _ , refl ⟩)
value-not-blame (V-const {k = p}) = $-not-blame {p = p} (⟨ _ , refl ⟩)
value-not-blame (V-pair vV vW) = cons-not-blame (⟨ _ , ⟨ _ , refl ⟩ ⟩)
value-not-blame (V-inl vV) = inl-not-blame (⟨ _ , refl ⟩)
value-not-blame (V-inr vV) = inr-not-blame (⟨ _ , refl ⟩)
value-not-blame (V-cast vV) = cast-not-blame (⟨ _ , ⟨ _ , refl ⟩ ⟩)


-- Lemma:
blame↠blame→ℓ≡ : ∀ {Γ A} {ℓ₁ ℓ₂}
  → (rd* : blame {Γ} {A} ℓ₁ —↠ blame {Γ} {A} ℓ₂)
    ----------------------------------------------
  → ℓ₁ ≡ ℓ₂
blame↠blame→ℓ≡ (.(blame _) ∎) = refl
blame↠blame→ℓ≡ (.(blame _) —→⟨ rd ⟩ rd*) = ⊥-elim (blame⌿→ rd)

open Active
open Cast

{-
  This proposition says that a safe cast, that is, a cast whose source type S and target type T respect subtyping <: ,
  never results in a blame.
-}
-- <:-safe-cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
--   → (a : Active c)
--   → (vV : Value V)
--   → A <: B
--     --------------------------------
--   → NotBlame (applyCast V vV c {a})
-- -- Id
-- <:-safe-cast (activeId (A ⇒⟨ _ ⟩ .A)) vV sub = value-not-blame vV
-- -- Collapse and conflict.
-- <:-safe-cast (activeProj (.⋆ ⇒⟨ x₁ ⟩ B) x) vV sub = {!!}
-- -- Function
-- <:-safe-cast {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂} {V = V} (activeFun ((.(_ ⇒ _) ⇒⟨ ℓ ⟩ .(_ ⇒ _)) {c})) vV _ =
--   ƛ-not-blame (⟨ (((rename S_ V) · ((` Z) ⟨ dom (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {c}) (Cross.C-fun _) ⟩)) ⟨ cod (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {c}) (Cross.C-fun _) ⟩) , refl ⟩)
-- -- Product
-- <:-safe-cast {A = A₁ `× A₂} {B = B₁ `× B₂} {V = V} (activePair ((.(_ `× _) ⇒⟨ ℓ ⟩ .(_ `× _)) {c})) vV _ =
--   cons-not-blame (⟨ (fst V ⟨ SimpleCast.fstC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {c}) (Cross.C-pair _) ⟩) , ⟨ (snd V ⟨ SimpleCast.sndC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {c}) (Cross.C-pair _) ⟩) , refl ⟩ ⟩)
-- -- Sum
-- <:-safe-cast {A = A₁ `⊎ A₂} {B = B₁ `⊎ B₂} {V = V} (activeSum ((.(_ `⊎ _) ⇒⟨ x ⟩ .(_ `⊎ _)) {c})) vV _ =
--   case-not-blame (⟨ V , ⟨ ƛ (inl ((` Z) ⟨ SimpleCast.inlC (((A₁ `⊎ A₂) ⇒⟨ x ⟩ (B₁ `⊎ B₂)) {c}) (Cross.C-sum _) ⟩)) , ⟨ ƛ (inr ((` Z) ⟨ SimpleCast.inrC (((A₁ `⊎ A₂) ⇒⟨ x ⟩ (B₁ `⊎ B₂)) {c}) (Cross.C-sum _) ⟩)) , refl ⟩ ⟩ ⟩)

{- TODO:
  We need to prove preservation w.r.t `CastsRespect<:` .
-}

{-
  If every cast in the term M with blame label ℓ respects subtyping, then M ⌿↠ blame ℓ .
-}
soundness-<: : ∀ {Γ A} {M : Γ ⊢ A} {ℓ}
  → CastsRespect<: M ℓ
  → ¬ (M —↠ blame ℓ)
-- -- By induction on M —↠ blame ℓ .
soundness-<: resp-plugMF ( .(plug _ _) —→⟨ ξ {F = F} M→M′ ⟩ plugM′F↠blame ) =
  -- In this case we need to prove that single step reduction preserves `CastsRespect<:` .
  let plugMF→plugM′F = ξ {F = F} M→M′ in
    soundness-<: {!!} plugM′F↠blame

-- There is no way to plug a `blame ℓ` in a frame and produce a term where every cast with ℓ respects <: .
soundness-<: resp ( .(plug (blame _) _) —→⟨ ξ-blame {F = F} {ℓ₁} ⟩ blame↠blame ) =
  let ℓ₁≡ℓ = blame↠blame→ℓ≡ blame↠blame in
    plug-blame→¬respect<: F (subst-eq (λ □ → CastsRespect<: (plug (blame □) _) _) ℓ₁≡ℓ resp)

soundness-<: {M = (ƛ N) · W} (CR<:-· resp-ƛN resp-W) ( .((ƛ N) · W) —→⟨ β vW ⟩ N[W]↠blame ) =
  {-
    We need to prove that given Γ , A ⊢ N ⦂ B and Γ ⊢ W ⦂ A that both satisfy `CastsRespect<:`,
    the substituted term N [ W ] also satisfies `CastsRespect<:` - single substitution preserves `CastsRespect<:` .
  -}
  soundness-<: {!!} N[W]↠blame

 -- This case corresponds to the δ rule.
soundness-<: (CR<:-· resp-f resp-k) ( .(($ _) · ($ _)) —→⟨ δ ⟩ fk↠blame ) =
    soundness-<: CR<:-prim fk↠blame

soundness-<: {M = if ($ true) M N} (CR<:-if _ resp-M _) ( .(if ($ true) M N) —→⟨ β-if-true ⟩ M↠blame ) =
    soundness-<: resp-M M↠blame

soundness-<: {M = if ($ false) M N} (CR<:-if _ _ resp-N) ( .(if ($ false) M N) —→⟨ β-if-false ⟩ N↠blame ) =
    soundness-<: resp-N N↠blame

soundness-<: (CR<:-fst (CR<:-cons resp-V resp-W)) ( .(fst (cons _ _)) —→⟨ β-fst vV vW ⟩ V↠blame ) =
    -- Another way to do this is to prove that V cannot step to blame.
    soundness-<: resp-V V↠blame

soundness-<: (CR<:-snd (CR<:-cons resp-V resp-W)) ( .(snd (cons _ _)) —→⟨ β-snd vV vW ⟩ W↠blame ) =
    soundness-<: resp-W W↠blame

soundness-<: (CR<:-case (CR<:-inl resp-V) resp-L _) ( .(case (inl _) _ _) —→⟨ β-caseL vV ⟩ L·V↠blame ) =
    soundness-<: (CR<:-· resp-L resp-V) L·V↠blame

soundness-<: (CR<:-case (CR<:-inr resp-V) _ resp-M) ( .(case (inr _) _ _) —→⟨ β-caseR vV ⟩ M·V↠blame ) =
    soundness-<: (CR<:-· resp-M resp-V) M·V↠blame

{- NOTE:
  We need to prove two things here:
    1. Reduction `—→` preserves `CastsRespect<:`
    2. `applyCast` preserves `CastsRespect<:`
  The data type `NotBlame` is useful here to discriminate on `applyCastVc↠blame` .
-}
soundness-<: {M = V ⟨ c ⟩} (CR<:-cast-same-ℓ {S = S} {T} S<:T resp-V) (.(_ ⟨ _ ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ) = {!!}
soundness-<: {M = V ⟨ c ⟩} (CR<:-cast-diff-ℓ ℓ≢ℓ′ resp-V) (.(_ ⟨ _ ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ) = {!!}
--   with <:-safe-cast a vV S<:T
-- soundness-<: {M = V ⟨ c ⟩} (CastsRespect<:-cast {S = S} {T} S<:T resp-V) ⟨ ℓ , .(_ ⟨ _ ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ⟩ | `-not-blame (⟨ x , eq ⟩) rewrite eq with applyCastVc↠blame
-- ...   | ` x —→⟨ `x→M ⟩ M↠blame = soundness-<: {!!} (⟨ ℓ , M↠blame ⟩)
-- soundness-<: {M = V ⟨ c ⟩} (CastsRespect<:-cast {S = S} {T} S<:T resp-V) ⟨ ℓ , .(_ ⟨ _ ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ⟩ | ƛ-not-blame (⟨ N , eq ⟩) rewrite eq with applyCastVc↠blame
-- ...   | ƛ N —→⟨ ƛN→M ⟩ M↠blame = soundness-<: {!!} (⟨ ℓ , M↠blame ⟩)

soundness-<: {ℓ = ℓ} (CR<:-· (CR<:-cast-same-ℓ (<:-⇒ T₁<:S₁ S₂<:T₂) resp-V) resp-W) ((V ⟨ (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {c}) ⟩ · W) —→⟨ fun-cast vV vW {x = x} ⟩ V·W↠blame) =
  soundness-<: (subst₂-eq (λ C₁ C₂ → CastsRespect<: ((V · (W ⟨ C₁ ⟩)) ⟨ C₂ ⟩) ℓ) (sym eq-dom) (sym eq-cod) resp)  V·W↠blame
  where
  c′ : T₁ ~ S₁
  c′ with ~-relevant c
  ... | fun~ c′ _ =  c′
  c″ : S₂ ~ T₂
  c″ with ~-relevant c
  ... | fun~ _ c″ = c″
  eq-dom : (dom (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {c}) x) ≡ ((T₁ ⇒⟨ ℓ ⟩ S₁) {c′})
  eq-dom with ~-relevant c
  ... | fun~ _ _ = refl
  eq-cod : (cod (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {c}) x) ≡ ((S₂ ⇒⟨ ℓ ⟩ T₂) {c″})
  eq-cod with ~-relevant c
  ... | fun~ _ _ = refl
  resp : CastsRespect<: ((V · (W ⟨ ((T₁ ⇒⟨ ℓ ⟩ S₁) {c′}) ⟩)) ⟨ ((S₂ ⇒⟨ ℓ ⟩ T₂) {c″}) ⟩) ℓ
  resp = CR<:-cast-same-ℓ S₂<:T₂ (CR<:-· resp-V (CR<:-cast-same-ℓ T₁<:S₁ resp-W))

soundness-<: {ℓ = ℓ} (CR<:-· (CR<:-cast-diff-ℓ x resp-V) resp-W) ((V ⟨ (S₁ ⇒ S₂) ⇒⟨ ℓ₁ ⟩ (T₁ ⇒ T₂) ⟩ · W) —→⟨ fun-cast vV vW ⟩ V·W↠blame) = {!!}

-- soundness-<: {M = fst (_⟨_⟩ {A = A₁ `× A₂} {B = B₁ `× B₂} V c)}
--   (CastsRespect<:-fst (CastsRespect<:-cast (<:-× A₁<:B₁ A₂<:B₂) resp-V))
--   ⟨ ℓ , .(fst (V ⟨ c ⟩)) —→⟨ fst-cast _ ⟩ fstV⟨fstc⟩↠blame ⟩ =
--     soundness-<: (CastsRespect<:-cast A₁<:B₁ (CastsRespect<:-fst resp-V)) (⟨ ℓ , fstV⟨fstc⟩↠blame ⟩)

-- soundness-<: {M = snd (_⟨_⟩ {A = A₁ `× A₂} {B = B₁ `× B₂} V c)}
--   (CastsRespect<:-snd (CastsRespect<:-cast (<:-× A₁<:B₁ A₂<:B₂) resp-V))
--   ⟨ ℓ , .(snd (V ⟨ c ⟩)) —→⟨ snd-cast _ ⟩ sndV⟨sndc⟩↠blame ⟩ =
--     soundness-<: (CastsRespect<:-cast A₂<:B₂ (CastsRespect<:-snd resp-V)) (⟨ ℓ , sndV⟨sndc⟩↠blame ⟩)

-- soundness-<: {M = case (_⟨_⟩ {A = A₁ `⊎ A₂} {B = B₁ `⊎ B₂} V c) W₁ W₂}
--   (CastsRespect<:-case (CastsRespect<:-cast (<:-⊎ A₁<:B₁ A₂<:B₂) resp-V) resp-W₁ resp-W₂)
--   ⟨ ℓ , .(case (V ⟨ c ⟩) W₁ W₂) —→⟨ case-cast vV ⟩ ↠blame ⟩ =
--     soundness-<: (CastsRespect<:-case resp-V
--                                       (CastsRespect<:-ƛ (CastsRespect<:-· {!!} (CastsRespect<:-cast A₁<:B₁ CastsRespect<:-var)))
--                                       (CastsRespect<:-ƛ (CastsRespect<:-· {!!} (CastsRespect<:-cast A₂<:B₂ CastsRespect<:-var))))
--                  (⟨ ℓ , ↠blame ⟩)
