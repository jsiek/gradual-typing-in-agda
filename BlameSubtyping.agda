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
open import SimpleCast using (Cast; Active; Cross; applyCast; pcs; cs; dom; cod; fstC; sndC; inlC; inrC)
open import Types
open import Variables
open import Labels

import ParamCastCalculus
open ParamCastCalculus Cast
import ParamCastAux
open ParamCastAux pcs using (Value; Frame; plug; canonical⋆)
import ParamCastReduction
open ParamCastReduction cs
import ParamCastReductionNoFrame
open ParamCastReductionNoFrame cs renaming (_—→_ to _—→′_; _—↠_ to _—↠′_)
open import CastSubtyping



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


-- Lemma:
blame↠blame→ℓ≡ : ∀ {Γ A} {ℓ₁ ℓ₂}
  → (rd* : blame {Γ} {A} ℓ₁ —↠ blame {Γ} {A} ℓ₂)
    ----------------------------------------------
  → ℓ₁ ≡ ℓ₂
blame↠blame→ℓ≡ (.(blame _) ∎) = refl
blame↠blame→ℓ≡ (.(blame _) —→⟨ rd ⟩ rd*) = ⊥-elim (blame⌿→ rd)

open Active
open Cast

fun~-dom : ∀ {S₁ S₂ T₁ T₂}
  → (S~T : (S₁ ⇒ S₂) ~ (T₁ ⇒ T₂))
  → T₁ ~ S₁
fun~-dom S~T with ~-relevant S~T
... | fun~ T₁~S₁ _ = T₁~S₁

fun~-cod : ∀ {S₁ S₂ T₁ T₂}
  → (S~T : (S₁ ⇒ S₂) ~ (T₁ ⇒ T₂))
  → S₂ ~ T₂
fun~-cod S~T with ~-relevant S~T
... | fun~ _ S₂~T₂ = S₂~T₂

dom-eq : ∀ {S₁ S₂ T₁ T₂} {ℓ}
  → (S~T : (S₁ ⇒ S₂) ~ (T₁ ⇒ T₂))
  → (x : Cross ((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)))
  → (dom (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {S~T}) x) ≡ ((T₁ ⇒⟨ ℓ ⟩ S₁) {fun~-dom S~T})
dom-eq S~T x with ~-relevant S~T
... | fun~ _ _ = refl

cod-eq : ∀ {S₁ S₂ T₁ T₂} {ℓ}
  → (S~T : (S₁ ⇒ S₂) ~ (T₁ ⇒ T₂))
  → (x : Cross ((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)))
  → (cod (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {S~T}) x) ≡ ((S₂ ⇒⟨ ℓ ⟩ T₂) {fun~-cod S~T})
cod-eq S~T x with ~-relevant S~T
... | fun~ _ _ = refl

pair~-fst : ∀ {A₁ A₂ B₁ B₂}
  → (A~B : (A₁ `× A₂) ~ (B₁ `× B₂))
  → A₁ ~ B₁
pair~-fst A~B with ~-relevant A~B
... | pair~ A₁~B₁ _ = A₁~B₁

pair~-snd : ∀ {A₁ A₂ B₁ B₂}
  → (A~B : (A₁ `× A₂) ~ (B₁ `× B₂))
  → A₂ ~ B₂
pair~-snd A~B with ~-relevant A~B
... | pair~ _ A₂~B₂ = A₂~B₂

fstC-eq : ∀ {A₁ A₂ B₁ B₂} {ℓ}
  → (A~B : (A₁ `× A₂) ~ (B₁ `× B₂))
  → (x : Cross ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))
    -----------------------------------------------
  → (fstC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {A~B}) x) ≡ ((A₁ ⇒⟨ ℓ ⟩ B₁) {pair~-fst A~B}) -- here we use a helper to destruct A~B
fstC-eq A~B x with ~-relevant A~B
... | pair~ _ _ = refl

sndC-eq : ∀ {A₁ A₂ B₁ B₂} {ℓ}
  → (A~B : (A₁ `× A₂) ~ (B₁ `× B₂))
  → (x : Cross ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))
    ------------------------------------------------
  → (sndC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {A~B}) x) ≡ ((A₂ ⇒⟨ ℓ ⟩ B₂) {pair~-snd A~B})
sndC-eq A~B x with ~-relevant A~B
... | pair~ _ _ = refl

sum~-inl : ∀ {A₁ A₂ B₁ B₂}
  → (A~B : (A₁ `⊎ A₂) ~ (B₁ `⊎ B₂))
  → A₁ ~ B₁
sum~-inl A~B with ~-relevant A~B
... | sum~ A₁~B₁ _ = A₁~B₁

sum~-inr : ∀ {A₁ A₂ B₁ B₂}
  → (A~B : (A₁ `⊎ A₂) ~ (B₁ `⊎ B₂))
  → A₂ ~ B₂
sum~-inr A~B with ~-relevant A~B
... | sum~ _ A₂~B₂ = A₂~B₂

inlC-eq : ∀ {A₁ A₂ B₁ B₂} {ℓ}
  → (A~B : (A₁ `⊎ A₂) ~ (B₁ `⊎ B₂))
  → (x : Cross ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))
    -----------------------------------------------
  → (inlC (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {A~B}) x) ≡ ((A₁ ⇒⟨ ℓ ⟩ B₁) {sum~-inl A~B})
inlC-eq A~B x with ~-relevant A~B
... | sum~ _ _ = refl

inrC-eq : ∀ {A₁ A₂ B₁ B₂} {ℓ}
  → (A~B : (A₁ `⊎ A₂) ~ (B₁ `⊎ B₂))
  → (x : Cross ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))
    -----------------------------------------------
  → (inrC (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {A~B}) x) ≡ ((A₂ ⇒⟨ ℓ ⟩ B₂) {sum~-inr A~B})
inrC-eq A~B x with ~-relevant A~B
... | sum~ _ _ = refl

{- Applying (an active) cast on a value preserves CastsRespect<: . -}
-- If the cast has the same blame label with the one that CR<: is quantified with :
applyCast-same-ℓ-pres-CR<: : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {ℓ}
  → (A~B : A ~ B)
  → (a : Active ((A ⇒⟨ ℓ ⟩ B) {A~B})) -- Since the cast can apply, it need to active.
  → A <: B         -- We require A <: B since the label on the cast is the same as the one CR<: is quantified with.
  → (resp-V : CastsRespect<: V ℓ)
    -----------------------------------------------------
  → CastsRespect<: (applyCast V vV (A ⇒⟨ ℓ ⟩ B) {a}) ℓ
applyCast-same-ℓ-pres-CR<: _ (activeId (A ⇒⟨ ℓ ⟩ A)) A<:B resp-V = resp-V
-- For simple cast, the key observation here is that B must be ⋆ .
applyCast-same-ℓ-pres-CR<: {V = V} {vV} A~B (activeProj (⋆ ⇒⟨ ℓ ⟩ B) x) T<:⋆ resp-V
  with canonical⋆ V vV
... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A′ `~ B
...   | no _ = CR<:-blame-diff-ℓ (λ _ → x refl)
...   | yes _ with resp-V
...     | CR<:-cast-same-ℓ _ resp-M′ = CR<:-cast-same-ℓ T<:⋆ resp-M′
...     | CR<:-cast-diff-ℓ _ resp-M′ = CR<:-cast-same-ℓ T<:⋆ resp-M′
applyCast-same-ℓ-pres-CR<: A~B (activeFun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) (<:-⇒ B₁<:A₁ A₂<:B₂) resp-V
  rewrite dom-eq A~B (Cross.C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) | cod-eq A~B (Cross.C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) =
    -- We need to prove renaming preserves CR<: .
    CR<:-ƛ (CR<:-cast-same-ℓ A₂<:B₂ (CR<:-· {!!} (CR<:-cast-same-ℓ B₁<:A₁ CR<:-var)))
applyCast-same-ℓ-pres-CR<: A~B (activePair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) (<:-× A₁<:B₁ A₂<:B₂) resp-V
  rewrite fstC-eq A~B (Cross.C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) | sndC-eq A~B (Cross.C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) =
  -- Prove CastsRespect<: (cons (fst V ⟨ fstC c x ⟩) (snd V ⟨ sndC c x ⟩)) ℓ
    CR<:-cons (CR<:-cast-same-ℓ A₁<:B₁ (CR<:-fst resp-V)) (CR<:-cast-same-ℓ A₂<:B₂ (CR<:-snd resp-V))
applyCast-same-ℓ-pres-CR<: A~B (activeSum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) (<:-⊎ A₁<:B₁ A₂<:B₂) resp-V
  rewrite inlC-eq A~B (Cross.C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) | inrC-eq A~B (Cross.C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) =
    CR<:-case resp-V (CR<:-ƛ (CR<:-inl (CR<:-cast-same-ℓ A₁<:B₁ CR<:-var))) (CR<:-ƛ (CR<:-inr (CR<:-cast-same-ℓ A₂<:B₂ CR<:-var)))

-- This handles the other case when the blame label on the cast is different from the one that CR<: is quantified with :
applyCast-diff-ℓ-pres-CR<: : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {ℓ ℓ′}
  → (A~B : A ~ B)
  → (a : Active ((A ⇒⟨ ℓ′ ⟩ B) {A~B})) -- Since the cast can apply, it need to active.
  → ℓ ≢ ℓ′
  → (resp-V : CastsRespect<: V ℓ)
    -----------------------------------------------------
  → CastsRespect<: (applyCast V vV (A ⇒⟨ ℓ′ ⟩ B) {a}) ℓ
applyCast-diff-ℓ-pres-CR<: _ (activeId (A ⇒⟨ ℓ′ ⟩ A)) ℓ≢ℓ′ resp-V = resp-V
applyCast-diff-ℓ-pres-CR<: {V = V} {vV} {ℓ} A~B (activeProj (⋆ ⇒⟨ ℓ′ ⟩ B) x) ℓ≢ℓ′ resp-V
  with canonical⋆ V vV
... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A′ `~ B
...   | no _ = CR<:-blame-diff-ℓ ℓ≢ℓ′
...   | yes _ with resp-V
...     | CR<:-cast-same-ℓ _ resp-M′ = CR<:-cast-diff-ℓ ℓ≢ℓ′ resp-M′
...     | CR<:-cast-diff-ℓ _ resp-M′ = CR<:-cast-diff-ℓ ℓ≢ℓ′ resp-M′
applyCast-diff-ℓ-pres-CR<: A~B (activeFun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) ℓ≢ℓ′ resp-V
  rewrite dom-eq A~B (Cross.C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) | cod-eq A~B (Cross.C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂))) =
    -- We need to prove renaming preserves CR<: .
    CR<:-ƛ (CR<:-cast-diff-ℓ ℓ≢ℓ′ (CR<:-· {!!} (CR<:-cast-diff-ℓ ℓ≢ℓ′ CR<:-var)))
applyCast-diff-ℓ-pres-CR<: A~B (activePair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) ℓ≢ℓ′ resp-V
  rewrite fstC-eq A~B (Cross.C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) | sndC-eq A~B (Cross.C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂))) =
  -- Prove CastsRespect<: (cons (fst V ⟨ fstC c x ⟩) (snd V ⟨ sndC c x ⟩)) ℓ
    CR<:-cons (CR<:-cast-diff-ℓ ℓ≢ℓ′ (CR<:-fst resp-V)) (CR<:-cast-diff-ℓ ℓ≢ℓ′ (CR<:-snd resp-V))
applyCast-diff-ℓ-pres-CR<: A~B (activeSum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) ℓ≢ℓ′ resp-V
  rewrite inlC-eq A~B (Cross.C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) | inrC-eq A~B (Cross.C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂))) =
    CR<:-case resp-V (CR<:-ƛ (CR<:-inl (CR<:-cast-diff-ℓ ℓ≢ℓ′ CR<:-var))) (CR<:-ƛ (CR<:-inr (CR<:-cast-diff-ℓ ℓ≢ℓ′ CR<:-var)))



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
    soundness-<: (preserve-CR<: resp-plugMF plugMF→plugM′F) plugM′F↠blame

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

soundness-<: (CR<:-cast-same-ℓ A<:B resp-V) ((V ⟨ ((A ⇒⟨ ℓ ⟩ B) {c}) ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ) =
  soundness-<: (applyCast-same-ℓ-pres-CR<: c a A<:B resp-V) applyCastVc↠blame
soundness-<: {ℓ = ℓ} (CR<:-cast-diff-ℓ ℓ≢ℓ′ resp-V) ((V ⟨ ((A ⇒⟨ ℓ′ ⟩ B) {c}) ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ) =
  soundness-<: (applyCast-diff-ℓ-pres-CR<: c a ℓ≢ℓ′ resp-V) applyCastVc↠blame

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
soundness-<: {ℓ = ℓ} (CR<:-· (CR<:-cast-diff-ℓ ℓ≢ℓ₁ resp-V) resp-W) ((V ⟨ (((S₁ ⇒ S₂) ⇒⟨ ℓ₁ ⟩ (T₁ ⇒ T₂)) {c}) ⟩ · W) —→⟨ fun-cast vV vW {x = x} ⟩ V·W↠blame) =
  soundness-<: (subst₂-eq (λ C₁ C₂ → CastsRespect<: ((V · (W ⟨ C₁ ⟩)) ⟨ C₂ ⟩) ℓ) (sym eq-dom) (sym eq-cod) resp) V·W↠blame
  where
  c′ : T₁ ~ S₁
  c′ with ~-relevant c
  ... | fun~ c′ _ =  c′
  c″ : S₂ ~ T₂
  c″ with ~-relevant c
  ... | fun~ _ c″ = c″
  -- This is essentially the same proof except that we use a differennt constructor for CR<: .
  eq-dom : (dom (((S₁ ⇒ S₂) ⇒⟨ ℓ₁ ⟩ (T₁ ⇒ T₂)) {c}) x) ≡ ((T₁ ⇒⟨ ℓ₁ ⟩ S₁) {c′})
  eq-dom with ~-relevant c
  ... | fun~ _ _ = refl
  eq-cod : (cod (((S₁ ⇒ S₂) ⇒⟨ ℓ₁ ⟩ (T₁ ⇒ T₂)) {c}) x) ≡ ((S₂ ⇒⟨ ℓ₁ ⟩ T₂) {c″})
  eq-cod with ~-relevant c
  ... | fun~ _ _ = refl
  resp : CastsRespect<: ((V · (W ⟨ ((T₁ ⇒⟨ ℓ₁ ⟩ S₁) {c′}) ⟩)) ⟨ ((S₂ ⇒⟨ ℓ₁ ⟩ T₂) {c″}) ⟩) ℓ
  resp = CR<:-cast-diff-ℓ ℓ≢ℓ₁ (CR<:-· resp-V (CR<:-cast-diff-ℓ ℓ≢ℓ₁ resp-W))

soundness-<: {ℓ = ℓ} (CR<:-fst (CR<:-cast-same-ℓ (<:-× A₁<:B₁ A₂<:B₂) resp-V)) ( (fst (V ⟨ (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {c}) ⟩)) —→⟨ fst-cast _ {x = x} ⟩ fstV⟨fstc⟩↠blame ) =
  soundness-<: (subst-eq (λ C → CastsRespect<: (fst V ⟨ C ⟩) ℓ) (sym eq-fst) resp) fstV⟨fstc⟩↠blame
  where
  c′ : A₁ ~ B₁
  c′ with ~-relevant c
  ... | pair~ c′ _ =  c′
  eq-fst : (fstC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {c}) x) ≡ ((A₁ ⇒⟨ ℓ ⟩ B₁) {c′})
  eq-fst with ~-relevant c
  ... | pair~ _ _ = refl
  resp : CastsRespect<: (fst V ⟨ ((A₁ ⇒⟨ ℓ ⟩ B₁) {c′}) ⟩ ) ℓ
  resp = CR<:-cast-same-ℓ A₁<:B₁ (CR<:-fst resp-V)
soundness-<: {ℓ = ℓ} (CR<:-fst (CR<:-cast-diff-ℓ ℓ≢ℓ₁ resp-V)) ( (fst (V ⟨ (((A₁ `× A₂) ⇒⟨ ℓ₁ ⟩ (B₁ `× B₂)) {c}) ⟩)) —→⟨ fst-cast _ {x = x} ⟩ fstV⟨fstc⟩↠blame ) =
  soundness-<: (subst-eq (λ C → CastsRespect<: (fst V ⟨ C ⟩) ℓ) (sym eq-fst) resp) fstV⟨fstc⟩↠blame
  where
  c′ : A₁ ~ B₁
  c′ with ~-relevant c
  ... | pair~ c′ _ =  c′
  eq-fst : (fstC (((A₁ `× A₂) ⇒⟨ ℓ₁ ⟩ (B₁ `× B₂)) {c}) x) ≡ ((A₁ ⇒⟨ ℓ₁ ⟩ B₁) {c′})
  eq-fst with ~-relevant c
  ... | pair~ _ _ = refl
  resp : CastsRespect<: (fst V ⟨ ((A₁ ⇒⟨ ℓ₁ ⟩ B₁) {c′}) ⟩ ) ℓ
  resp = CR<:-cast-diff-ℓ ℓ≢ℓ₁ (CR<:-fst resp-V)

soundness-<: {ℓ = ℓ} (CR<:-snd (CR<:-cast-same-ℓ (<:-× A₁<:B₁ A₂<:B₂) resp-V)) ( (snd (V ⟨ (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {c}) ⟩)) —→⟨ snd-cast _ {x = x} ⟩ sndV⟨sndc⟩↠blame ) =
  soundness-<: (subst-eq (λ C → CastsRespect<: (snd V ⟨ C ⟩) ℓ) (sym eq-snd) resp) sndV⟨sndc⟩↠blame
  where
  c′ : A₂ ~ B₂
  c′ with ~-relevant c
  ... | pair~ _ c′ =  c′
  eq-snd : (sndC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {c}) x) ≡ ((A₂ ⇒⟨ ℓ ⟩ B₂) {c′})
  eq-snd with ~-relevant c
  ... | pair~ _ _ = refl
  resp : CastsRespect<: (snd V ⟨ ((A₂ ⇒⟨ ℓ ⟩ B₂) {c′}) ⟩ ) ℓ
  resp = CR<:-cast-same-ℓ A₂<:B₂ (CR<:-snd resp-V)
soundness-<: {ℓ = ℓ} (CR<:-snd (CR<:-cast-diff-ℓ ℓ≢ℓ₁ resp-V)) ( (snd (V ⟨ (((A₁ `× A₂) ⇒⟨ ℓ₁ ⟩ (B₁ `× B₂)) {c}) ⟩)) —→⟨ snd-cast _ {x = x} ⟩ sndV⟨sndc⟩↠blame ) =
  soundness-<: (subst-eq (λ C → CastsRespect<: (snd V ⟨ C ⟩) ℓ) (sym eq-snd) resp) sndV⟨sndc⟩↠blame
  where
  c′ : A₂ ~ B₂
  c′ with ~-relevant c
  ... | pair~ _ c′ =  c′
  eq-snd : (sndC (((A₁ `× A₂) ⇒⟨ ℓ₁ ⟩ (B₁ `× B₂)) {c}) x) ≡ ((A₂ ⇒⟨ ℓ₁ ⟩ B₂) {c′})
  eq-snd with ~-relevant c
  ... | pair~ _ _ = refl
  resp : CastsRespect<: (snd V ⟨ ((A₂ ⇒⟨ ℓ₁ ⟩ B₂) {c′}) ⟩ ) ℓ
  resp = CR<:-cast-diff-ℓ ℓ≢ℓ₁ (CR<:-snd resp-V)

soundness-<: {Γ = Γ} {ℓ = ℓ} (CR<:-case (CR<:-cast-same-ℓ (<:-⊎ A₁<:B₁ A₂<:B₂) resp-V) resp-W₁ resp-W₂) ( (case (V ⟨ (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {c}) ⟩) W₁ W₂) —→⟨ case-cast vV {x = x} ⟩ ↠blame ) =
  soundness-<: (CR<:-case resp-V (CR<:-ƛ (CR<:-· {!!} (subst-eq (λ C → CastsRespect<: ((` Z) ⟨ C ⟩) ℓ) (sym eq-inl) respl)))
                                 (CR<:-ƛ (CR<:-· {!!} (subst-eq (λ C → CastsRespect<: ((` Z) ⟨ C ⟩) ℓ) (sym eq-inr) respr))))
               ↠blame
  where
  c′ : A₁ ~ B₁
  c′ with ~-relevant c
  ... | sum~ c′ _ =  c′
  c″ : A₂ ~ B₂
  c″ with ~-relevant c
  ... | sum~ _ c″ =  c″
  eq-inl : (inlC (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {c}) x) ≡ ((A₁ ⇒⟨ ℓ ⟩ B₁) {c′})
  eq-inl with ~-relevant c
  ... | sum~ _ _ = refl
  eq-inr : (inrC (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {c}) x) ≡ ((A₂ ⇒⟨ ℓ ⟩ B₂) {c″})
  eq-inr with ~-relevant c
  ... | sum~ _ _ = refl
  respl : CastsRespect<: ((`_ {Γ = Γ , A₁} Z) ⟨ ((A₁ ⇒⟨ ℓ ⟩ B₁) {c′}) ⟩) ℓ
  respl = CR<:-cast-same-ℓ A₁<:B₁ CR<:-var
  respr : CastsRespect<: ((`_ {Γ = Γ , A₂} Z) ⟨ ((A₂ ⇒⟨ ℓ ⟩ B₂) {c″}) ⟩) ℓ
  respr = CR<:-cast-same-ℓ A₂<:B₂ CR<:-var

soundness-<: {Γ = Γ} {ℓ = ℓ} (CR<:-case (CR<:-cast-diff-ℓ ℓ≢ℓ₁ resp-V) resp-W₁ resp-W₂) ( (case (V ⟨ (((A₁ `⊎ A₂) ⇒⟨ ℓ₁ ⟩ (B₁ `⊎ B₂)) {c}) ⟩) W₁ W₂) —→⟨ case-cast vV {x = x} ⟩ ↠blame ) =
  soundness-<: (CR<:-case resp-V (CR<:-ƛ (CR<:-· {!!} (subst-eq (λ C → CastsRespect<: ((` Z) ⟨ C ⟩) ℓ) (sym eq-inl) respl)))
                                 (CR<:-ƛ (CR<:-· {!!} (subst-eq (λ C → CastsRespect<: ((` Z) ⟨ C ⟩) ℓ) (sym eq-inr) respr))))
               ↠blame
  where
  c′ : A₁ ~ B₁
  c′ with ~-relevant c
  ... | sum~ c′ _ =  c′
  c″ : A₂ ~ B₂
  c″ with ~-relevant c
  ... | sum~ _ c″ =  c″
  eq-inl : (inlC (((A₁ `⊎ A₂) ⇒⟨ ℓ₁ ⟩ (B₁ `⊎ B₂)) {c}) x) ≡ ((A₁ ⇒⟨ ℓ₁ ⟩ B₁) {c′})
  eq-inl with ~-relevant c
  ... | sum~ _ _ = refl
  eq-inr : (inrC (((A₁ `⊎ A₂) ⇒⟨ ℓ₁ ⟩ (B₁ `⊎ B₂)) {c}) x) ≡ ((A₂ ⇒⟨ ℓ₁ ⟩ B₂) {c″})
  eq-inr with ~-relevant c
  ... | sum~ _ _ = refl
  respl : CastsRespect<: ((`_ {Γ = Γ , A₁} Z) ⟨ ((A₁ ⇒⟨ ℓ₁ ⟩ B₁) {c′}) ⟩) ℓ
  respl = CR<:-cast-diff-ℓ ℓ≢ℓ₁ CR<:-var
  respr : CastsRespect<: ((`_ {Γ = Γ , A₂} Z) ⟨ ((A₂ ⇒⟨ ℓ₁ ⟩ B₂) {c″}) ⟩) ℓ
  respr = CR<:-cast-diff-ℓ ℓ≢ℓ₁ CR<:-var

soundness-<: (CR<:-blame-diff-ℓ ℓ≢ℓ) ((blame ℓ) ∎) = ℓ≢ℓ refl
