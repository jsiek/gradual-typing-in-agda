open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties using (_≟_)

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
plug-blame→¬respect<: : ∀ {Γ A B ℓ}
  → (F : Frame {Γ} A B)
  → ¬ (CastsRespect<: (plug (blame ℓ) F))
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

data NotBlame : ∀ {Γ A} → Γ ⊢ A → Set where

  `-not-blame : ∀ {Γ A} {M : Γ ⊢ A}
    → ∃[ x ] (M ≡ ` x)
    → NotBlame M

  ƛ-not-blame : ∀ {Γ B A} {M : Γ ⊢ A ⇒ B}
    → ∃[ N ] (M ≡ ƛ N)
    → NotBlame M

  ·-not-blame : ∀ {Γ A B} {M : Γ ⊢ B}
    → Σ[ L ∈ Γ ⊢ A ⇒ B ] ∃[ N ] (M ≡ L · N)
    → NotBlame M

  $-not-blame : ∀ {Γ A} {p : rep A} {f : Prim A} {M : Γ ⊢ A}
    → ∃[ p ] (M ≡ $_ {Γ} p {f})
    → NotBlame M

  if-not-blame : ∀ {Γ A} {M : Γ ⊢ A}
    → ∃[ L ] ∃[ N₁ ] ∃[ N₂ ] (M ≡ if L N₁ N₂)
    → NotBlame M

  cons-not-blame : ∀ {Γ A B} {M : Γ ⊢ A `× B}
    → ∃[ L ] ∃[ N ] (M ≡ cons L N)
    → NotBlame M

  fst-not-blame : ∀ {Γ A B} {M : Γ ⊢ A}
    → Σ[ N ∈ Γ ⊢ A `× B ] (M ≡ fst N)
    → NotBlame M

  snd-not-blame : ∀ {Γ A B} {M : Γ ⊢ B}
    → Σ[ N ∈ Γ ⊢ A `× B ] (M ≡ snd N)
    → NotBlame M

  inl-not-blame : ∀ {Γ A B} {M : Γ ⊢ A `⊎ B}
    → ∃[ N ] (M ≡ inl N)
    → NotBlame M

  inr-not-blame : ∀ {Γ A B} {M : Γ ⊢ A `⊎ B}
    → ∃[ N ] (M ≡ inr N)
    → NotBlame M

  case-not-blame : ∀ {Γ A B C} {M : Γ ⊢ C}
    → Σ[ L ∈ Γ ⊢ A `⊎ B ] ∃[ N₁ ] ∃[ N₂ ] (M ≡ case L N₁ N₂)
    → NotBlame M

  cast-not-blame : ∀ {Γ A B} {M : Γ ⊢ B}
    → Σ[ N ∈ Γ ⊢ A ] ∃[ c ] (M ≡ N ⟨ c ⟩)
    → NotBlame M

-- A value V is not blame.
value-not-blame : ∀ {Γ A} {V : Γ ⊢ A}
  → (vV : Value V)
  → NotBlame V
value-not-blame V-ƛ = ƛ-not-blame (⟨ _ , refl ⟩)
value-not-blame (V-const {k = p}) = $-not-blame {p = p} (⟨ _ , refl ⟩)
value-not-blame (V-pair vV vW) = cons-not-blame (⟨ _ , ⟨ _ , refl ⟩ ⟩)
value-not-blame (V-inl vV) = inl-not-blame (⟨ _ , refl ⟩)
value-not-blame (V-inr vV) = inr-not-blame (⟨ _ , refl ⟩)
value-not-blame (V-cast vV) = cast-not-blame (⟨ _ , ⟨ _ , refl ⟩ ⟩)

open Active
open Cast

{-
  This proposition says that a safe cast, that is, a cast whose source type S and target type T respect subtyping <: ,
  never results in a blame.
-}
<:-safe-cast : ∀ {Γ A B} {V : Γ ⊢ A} {c : Cast (A ⇒ B)}
  → (a : Active c)
  → (vV : Value V)
  → A <: B
  → NotBlame (applyCast V vV c {a})
-- Id
<:-safe-cast (activeId (A ⇒⟨ _ ⟩ .A)) vV sub = value-not-blame vV
-- Collapse and conflict.
<:-safe-cast (activeProj (.⋆ ⇒⟨ x₁ ⟩ B) x) vV sub = {!!}
-- Function
<:-safe-cast {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂} {V = V} (activeFun ((.(_ ⇒ _) ⇒⟨ ℓ ⟩ .(_ ⇒ _)) {c})) vV _ =
  ƛ-not-blame (⟨ (((rename S_ V) · ((` Z) ⟨ dom (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {c}) (Cross.C-fun _) ⟩)) ⟨ cod (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {c}) (Cross.C-fun _) ⟩) , refl ⟩)
-- Product
<:-safe-cast {A = A₁ `× A₂} {B = B₁ `× B₂} {V = V} (activePair ((.(_ `× _) ⇒⟨ ℓ ⟩ .(_ `× _)) {c})) vV _ =
  cons-not-blame (⟨ (fst V ⟨ SimpleCast.fstC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {c}) (Cross.C-pair _) ⟩) , ⟨ (snd V ⟨ SimpleCast.sndC (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {c}) (Cross.C-pair _) ⟩) , refl ⟩ ⟩)
-- Sum
<:-safe-cast {A = A₁ `⊎ A₂} {B = B₁ `⊎ B₂} {V = V} (activeSum ((.(_ `⊎ _) ⇒⟨ x ⟩ .(_ `⊎ _)) {c})) vV _ =
  case-not-blame (⟨ V , ⟨ ƛ (inl ((` Z) ⟨ SimpleCast.inlC (((A₁ `⊎ A₂) ⇒⟨ x ⟩ (B₁ `⊎ B₂)) {c}) (Cross.C-sum _) ⟩)) , ⟨ ƛ (inr ((` Z) ⟨ SimpleCast.inrC (((A₁ `⊎ A₂) ⇒⟨ x ⟩ (B₁ `⊎ B₂)) {c}) (Cross.C-sum _) ⟩)) , refl ⟩ ⟩ ⟩)

{- TODO:
  We need to prove preservation w.r.t `CastsRespect<:` .
-}

{-
  If every cast in the term M respects subtyping, then M ⌿↠ blame ℓ for any ℓ .
-}
soundness-<: : ∀ {Γ A} {M : Γ ⊢ A}
  → CastsRespect<: M
  → ¬ (∃[ ℓ ] (M —↠ blame ℓ))
-- By induction on M —↠ blame ℓ .
soundness-<: resp-plugMF ⟨ ℓ , .(plug _ _) —→⟨ ξ M→M′ ⟩ plugM′F↠blame ⟩ =
  -- In this case we need to prove that reduction preserves `CastsRespect<:` .
  soundness-<: {!!} (⟨ ℓ , plugM′F↠blame ⟩)

-- There is no way to plug a blame in a frame and produce a term where every cast respects <: .
soundness-<: resp ⟨ ℓ , .(plug (blame _) _) —→⟨ ξ-blame {F = F} ⟩ _ ⟩ = plug-blame→¬respect<: F resp

soundness-<: {M = (ƛ N) · W} (CastsRespect<:-· resp-ƛN resp-W) ⟨ ℓ , .((ƛ N) · W) —→⟨ β vW ⟩ N[W]↠blame ⟩ =
  {-
    We need to prove that given Γ , A ⊢ N ⦂ B and Γ ⊢ W ⦂ A that both satisfy `CastsRespect<:`,
    the substituted term N [ W ] also satisfies `CastsRespect<:` - single substitution preserves `CastsRespect<:` .
  -}
  soundness-<: {!!} (⟨ ℓ , N[W]↠blame ⟩)

soundness-<: {M = ($ f) · ($ k)} -- This case corresponds to the δ rule.
  (CastsRespect<:-· resp-f resp-k)
  ⟨ ℓ , .(($ _) · ($ _)) —→⟨ δ ⟩ fk↠blame ⟩ =
    soundness-<: CastsRespect<:-prim (⟨ ℓ , fk↠blame ⟩)

soundness-<: {M = if ($ true) M N}
  (CastsRespect<:-if _ resp-M _)
  ⟨ ℓ , .(if ($ true) M N) —→⟨ β-if-true ⟩ M↠blame ⟩ =
    soundness-<: resp-M (⟨ ℓ , M↠blame ⟩)

soundness-<: {M = if ($ false) M N}
  (CastsRespect<:-if _ _ resp-N)
  ⟨ ℓ , .(if ($ false) M N) —→⟨ β-if-false ⟩ N↠blame ⟩ =
    soundness-<: resp-N (⟨ ℓ , N↠blame ⟩)

soundness-<: {M = fst (cons V W)}
  (CastsRespect<:-fst (CastsRespect<:-cons resp-V resp-W))
  ⟨ ℓ , .(fst (cons V W)) —→⟨ β-fst vV vW ⟩ V↠blame ⟩ =
    -- Another way to do this is to prove that V cannot step to blame.
    soundness-<: resp-V (⟨ ℓ , V↠blame ⟩)

soundness-<: {M = snd (cons V W)}
  (CastsRespect<:-snd (CastsRespect<:-cons resp-V resp-W))
  ⟨ ℓ , .(snd (cons V W)) —→⟨ β-snd vV vW ⟩ W↠blame ⟩ =
    soundness-<: resp-W (⟨ ℓ , W↠blame ⟩)

soundness-<: {M = case (inl V) L M}
  (CastsRespect<:-case (CastsRespect<:-inl resp-V) resp-L _)
  ⟨ ℓ , .(case (inl V) L M) —→⟨ β-caseL vV ⟩ L·V↠blame ⟩ =
    soundness-<: (CastsRespect<:-· resp-L resp-V) (⟨ ℓ , L·V↠blame ⟩)

soundness-<: {M = case (inr V) L M}
  (CastsRespect<:-case (CastsRespect<:-inr resp-V) _ resp-M)
  ⟨ ℓ , .(case (inr V) L M) —→⟨ β-caseR vV ⟩ M·V↠blame ⟩ =
    soundness-<: (CastsRespect<:-· resp-M resp-V) (⟨ ℓ , M·V↠blame ⟩)

{- NOTE:
  We need to prove two things here:
    1. Reduction `—→` preserves `CastsRespect<:`
    2. `applyCast` preserves `CastsRespect<:`
-}
soundness-<: {M = V ⟨ c ⟩}
  (CastsRespect<:-cast {S = S} {T} S<:T resp-V)
  ⟨ ℓ , .(_ ⟨ _ ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ⟩ = {!!}
--   with <:-safe-cast a vV S<:T
-- soundness-<: {M = V ⟨ c ⟩} (CastsRespect<:-cast {S = S} {T} S<:T resp-V) ⟨ ℓ , .(_ ⟨ _ ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ⟩ | `-not-blame (⟨ x , eq ⟩) rewrite eq with applyCastVc↠blame
-- ...   | ` x —→⟨ `x→M ⟩ M↠blame = soundness-<: {!!} (⟨ ℓ , M↠blame ⟩)
-- soundness-<: {M = V ⟨ c ⟩} (CastsRespect<:-cast {S = S} {T} S<:T resp-V) ⟨ ℓ , .(_ ⟨ _ ⟩) —→⟨ cast vV {a} ⟩ applyCastVc↠blame ⟩ | ƛ-not-blame (⟨ N , eq ⟩) rewrite eq with applyCastVc↠blame
-- ...   | ƛ N —→⟨ ƛN→M ⟩ M↠blame = soundness-<: {!!} (⟨ ℓ , M↠blame ⟩)

soundness-<: {M = (_⟨_⟩ {A = S₁ ⇒ S₂} {B = T₁ ⇒ T₂} V c) · W}
  (CastsRespect<:-· (CastsRespect<:-cast (<:-⇒ T₁<:S₁ S₂<:T₂) resp-V) resp-W)
  ⟨ ℓ , .(V ⟨ c ⟩ · W) —→⟨ fun-cast vV vW ⟩ V·W↠blame ⟩ =
  soundness-<: (CastsRespect<:-cast S₂<:T₂
                                    (CastsRespect<:-· resp-V (CastsRespect<:-cast T₁<:S₁ resp-W)))
               (⟨ ℓ , V·W↠blame ⟩)

soundness-<: {M = fst (_⟨_⟩ {A = A₁ `× A₂} {B = B₁ `× B₂} V c)}
  (CastsRespect<:-fst (CastsRespect<:-cast (<:-× A₁<:B₁ A₂<:B₂) resp-V))
  ⟨ ℓ , .(fst (V ⟨ c ⟩)) —→⟨ fst-cast _ ⟩ fstV⟨fstc⟩↠blame ⟩ =
    soundness-<: (CastsRespect<:-cast A₁<:B₁ (CastsRespect<:-fst resp-V)) (⟨ ℓ , fstV⟨fstc⟩↠blame ⟩)

soundness-<: {M = snd (_⟨_⟩ {A = A₁ `× A₂} {B = B₁ `× B₂} V c)}
  (CastsRespect<:-snd (CastsRespect<:-cast (<:-× A₁<:B₁ A₂<:B₂) resp-V))
  ⟨ ℓ , .(snd (V ⟨ c ⟩)) —→⟨ snd-cast _ ⟩ sndV⟨sndc⟩↠blame ⟩ =
    soundness-<: (CastsRespect<:-cast A₂<:B₂ (CastsRespect<:-snd resp-V)) (⟨ ℓ , sndV⟨sndc⟩↠blame ⟩)

soundness-<: {M = case (_⟨_⟩ {A = A₁ `⊎ A₂} {B = B₁ `⊎ B₂} V c) W₁ W₂}
  (CastsRespect<:-case (CastsRespect<:-cast (<:-⊎ A₁<:B₁ A₂<:B₂) resp-V) resp-W₁ resp-W₂)
  ⟨ ℓ , .(case (V ⟨ c ⟩) W₁ W₂) —→⟨ case-cast vV ⟩ ↠blame ⟩ =
    soundness-<: (CastsRespect<:-case resp-V
                                      (CastsRespect<:-ƛ (CastsRespect<:-· {!!} (CastsRespect<:-cast A₁<:B₁ CastsRespect<:-var)))
                                      (CastsRespect<:-ƛ (CastsRespect<:-· {!!} (CastsRespect<:-cast A₂<:B₂ CastsRespect<:-var))))
                 (⟨ ℓ , ↠blame ⟩)
