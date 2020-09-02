open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties using (_≟_)

-- We're using simple cast - at least for now.
open import SimpleCast using (Cast; pcs; cs)
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast
import ParamCastAux
open ParamCastAux pcs using (Value; Frame; plug)
import ParamCastReduction
open ParamCastReduction cs
open import CastSubtyping using (CastsRespect<:; _<:_)



-- Test
-- M : ∅ ⊢ ⋆
-- M = ($_ zero {Prim.P-Base}) ⟨ _⇒⟨_⟩_ (` Nat) (Label.pos zero) ⋆ {unk~R} ⟩


open _—→_
open _—↠_
open Value

-- Values do not reduce.
postulate
  V⌿→ : ∀ {Γ A} {M N : Γ ⊢ A}
    → Value M
    → ¬ (M —→ N)

open CastsRespect<:
open Frame
open _<:_

-- There is no way to plug a blame in a frame and produce a term where every cast respects <: .
plug-blame→¬respect<: : ∀ {Γ A B 𝓁}
  → (F : Frame {Γ} A B)
  → ¬ (CastsRespect<: (plug (blame 𝓁) F))
plug-blame→¬respect<: (F-·₁ M) (CastsRespect<:-· () _)                   -- □ · M
plug-blame→¬respect<: (F-·₂ L) (CastsRespect<:-· _ ())                   -- L · □
plug-blame→¬respect<: (F-if M N) (CastsRespect<:-if () _ _)              -- if □ M N
plug-blame→¬respect<: (F-×₁ M) (CastsRespect<:-cons _ ())                -- cons M □
plug-blame→¬respect<: (F-×₂ L) (CastsRespect<:-cons () _)                -- cons □ L
plug-blame→¬respect<: F-fst (CastsRespect<:-fst ())                      -- fst □
plug-blame→¬respect<: F-snd (CastsRespect<:-snd ())                      -- snd □
plug-blame→¬respect<: F-inl (CastsRespect<:-inl ())                      -- inl □
plug-blame→¬respect<: F-inr (CastsRespect<:-inr ())                      -- inr □
plug-blame→¬respect<: (F-case M N) (CastsRespect<:-case () _ _)          -- case □ M N
plug-blame→¬respect<: (F-cast c) (CastsRespect<:-cast _ ())              -- □ ⟨ c ⟩

{-
  If every cast in the term M respects subtyping, then M ⌿↠ blame 𝓁 for any 𝓁 .
-}
soundness-<: : ∀ {Γ A} {M : Γ ⊢ A}
  → CastsRespect<: M
  → ¬ (∃[ 𝓁 ] (M —↠ blame 𝓁))
-- By induction on M —↠ blame 𝓁 .
soundness-<: resp-plugMF ⟨ 𝓁 , .(plug _ _) —→⟨ ξ M→M′ ⟩ plugM′F↠blame ⟩ =
  -- In this case we need to prove that reduction preserves `CastsRespect<:` .
  soundness-<: {!!} (⟨ 𝓁 , plugM′F↠blame ⟩)

-- There is no way to plug a blame in a frame and produce a term where every cast respects <: .
soundness-<: resp ⟨ 𝓁 , .(plug (blame _) _) —→⟨ ξ-blame {F = F} ⟩ _ ⟩ = plug-blame→¬respect<: F resp

soundness-<: {M = (ƛ N) · W} (CastsRespect<:-· resp-ƛN resp-W) ⟨ 𝓁 , .((ƛ N) · W) —→⟨ β vW ⟩ N[W]↠blame ⟩ =
  {-
    We need to prove that given Γ , A ⊢ N ⦂ B and Γ ⊢ W ⦂ A that both satisfy `CastsRespect<:`,
    the substituted term N [ W ] also satisfies `CastsRespect<:` - single substitution preserves `CastsRespect<:` .
  -}
  soundness-<: {!!} (⟨ 𝓁 , N[W]↠blame ⟩)

soundness-<: {M = ($ f) · ($ k)} -- This case corresponds to the δ rule.
  (CastsRespect<:-· resp-f resp-k)
  ⟨ 𝓁 , .(($ _) · ($ _)) —→⟨ δ ⟩ fk↠blame ⟩ =
    soundness-<: CastsRespect<:-prim (⟨ 𝓁 , fk↠blame ⟩)

soundness-<: {M = if ($ true) M N}
  (CastsRespect<:-if _ resp-M _)
  ⟨ 𝓁 , .(if ($ true) M N) —→⟨ β-if-true ⟩ M↠blame ⟩ =
    soundness-<: resp-M (⟨ 𝓁 , M↠blame ⟩)

soundness-<: {M = if ($ false) M N}
  (CastsRespect<:-if _ _ resp-N)
  ⟨ 𝓁 , .(if ($ false) M N) —→⟨ β-if-false ⟩ N↠blame ⟩ =
    soundness-<: resp-N (⟨ 𝓁 , N↠blame ⟩)

soundness-<: {M = fst (cons V W)}
  (CastsRespect<:-fst (CastsRespect<:-cons resp-V resp-W))
  ⟨ 𝓁 , .(fst (cons V W)) —→⟨ β-fst vV vW ⟩ V↠blame ⟩ =
    -- Another way to do this is to prove that V cannot step to blame.
    soundness-<: resp-V (⟨ 𝓁 , V↠blame ⟩)

soundness-<: {M = snd (cons V W)}
  (CastsRespect<:-snd (CastsRespect<:-cons resp-V resp-W))
  ⟨ 𝓁 , .(snd (cons V W)) —→⟨ β-snd vV vW ⟩ W↠blame ⟩ =
    soundness-<: resp-W (⟨ 𝓁 , W↠blame ⟩)

soundness-<: {M = case (inl V) L M}
  (CastsRespect<:-case (CastsRespect<:-inl resp-V) resp-L _)
  ⟨ 𝓁 , .(case (inl V) L M) —→⟨ β-caseL vV ⟩ L·V↠blame ⟩ =
    soundness-<: (CastsRespect<:-· resp-L resp-V) (⟨ 𝓁 , L·V↠blame ⟩)

soundness-<: {M = case (inr V) L M}
  (CastsRespect<:-case (CastsRespect<:-inr resp-V) _ resp-M)
  ⟨ 𝓁 , .(case (inr V) L M) —→⟨ β-caseR vV ⟩ M·V↠blame ⟩ =
    soundness-<: (CastsRespect<:-· resp-M resp-V) (⟨ 𝓁 , M·V↠blame ⟩)

soundness-<: {M = V ⟨ c ⟩}
  (CastsRespect<:-cast {S = S} {T} S<:T resp-V)
  ⟨ 𝓁 , .(_ ⟨ _ ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ⟩ = {!!}

soundness-<: {M = (_⟨_⟩ {A = S₁ ⇒ S₂} {B = T₁ ⇒ T₂} V c) · W}
  (CastsRespect<:-· (CastsRespect<:-cast (<:-⇒ T₁<:S₁ S₂<:T₂) resp-V) resp-W)
  ⟨ 𝓁 , .(V ⟨ c ⟩ · W) —→⟨ fun-cast vV vW ⟩ V·W↠blame ⟩ =
  soundness-<: (CastsRespect<:-cast S₂<:T₂
                                    (CastsRespect<:-· resp-V (CastsRespect<:-cast T₁<:S₁ resp-W)))
               (⟨ 𝓁 , V·W↠blame ⟩)

soundness-<: {M = fst (_⟨_⟩ {A = A₁ `× A₂} {B = B₁ `× B₂} V c)}
  (CastsRespect<:-fst (CastsRespect<:-cast (<:-× A₁<:B₁ A₂<:B₂) resp-V))
  ⟨ 𝓁 , .(fst (V ⟨ c ⟩)) —→⟨ fst-cast _ ⟩ fstV⟨fstc⟩↠blame ⟩ =
    soundness-<: (CastsRespect<:-cast A₁<:B₁ (CastsRespect<:-fst resp-V)) (⟨ 𝓁 , fstV⟨fstc⟩↠blame ⟩)

soundness-<: {M = snd (_⟨_⟩ {A = A₁ `× A₂} {B = B₁ `× B₂} V c)}
  (CastsRespect<:-snd (CastsRespect<:-cast (<:-× A₁<:B₁ A₂<:B₂) resp-V))
  ⟨ 𝓁 , .(snd (V ⟨ c ⟩)) —→⟨ snd-cast _ ⟩ sndV⟨sndc⟩↠blame ⟩ =
    soundness-<: (CastsRespect<:-cast A₂<:B₂ (CastsRespect<:-snd resp-V)) (⟨ 𝓁 , sndV⟨sndc⟩↠blame ⟩)

soundness-<: {M = case (_⟨_⟩ {A = A₁ `⊎ A₂} {B = B₁ `⊎ B₂} V c) W₁ W₂}
  (CastsRespect<:-case (CastsRespect<:-cast (<:-⊎ A₁<:B₁ A₂<:B₂) resp-V) resp-W₁ resp-W₂)
  ⟨ 𝓁 , .(case (V ⟨ c ⟩) W₁ W₂) —→⟨ case-cast vV ⟩ ↠blame ⟩ =
    soundness-<: (CastsRespect<:-case resp-V
                                      (CastsRespect<:-ƛ (CastsRespect<:-· {!!} (CastsRespect<:-cast A₁<:B₁ CastsRespect<:-var)))
                                      (CastsRespect<:-ƛ (CastsRespect<:-· {!!} (CastsRespect<:-cast A₂<:B₂ CastsRespect<:-var))))
                 (⟨ 𝓁 , ↠blame ⟩)
