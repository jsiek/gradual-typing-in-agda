open import Types hiding (_⊔_)
open import Labels
open import Variables
open import CastStructure
import EfficientParamCasts
open import Data.Nat {-using (ℕ; _≤_; _⊔_; z≤n; s≤s)-}
open import Data.Nat.Properties
open import Data.Nat.Solver
open Data.Nat.Properties.≤-Reasoning
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

{-

  A proof that the Efficient Parameterized Cast Calculus
  is indeed space efficient.

  Proof idea:

  We define a predicate on terms that ensures that there
  are no more than 2 casts in sequence. The compose-casts
  rule takes 2-cast sequences that appear and reduces them
  to 1 cast before they can further grow to a 3-cast sequence.

-}

module SpaceEfficient (ecs : EfficientCastStruct) where

  open EfficientCastStruct ecs
  open EfficientParamCasts ecs

  import ParamCastCalculus
  open ParamCastCalculus Cast
  open import EfficientParamCastAux precast

  data _⊢_ok : ∀{Γ A} → ℕ → Γ ⊢ A  → Set where
    castOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}
             → suc n ⊢ M ok → n ≤ 1
             → n ⊢ M ⟨ c ⟩ ok
    varOK : ∀{Γ A}{∋x : Γ ∋ A}{n : ℕ} → n ⊢ (` ∋x) ok
    lamOK : ∀{Γ B A}{N : Γ , A ⊢ B}{n}
          → 0 ⊢ N ok
          → n ⊢ (ƛ N) ok
    appOK : ∀{Γ A B}{L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}{n}
          → 0 ⊢ L ok → 0 ⊢ M ok
          → n ⊢ (L · M) ok
    litOK : ∀{Γ : Context}{A}{r : rep A}{p : Prim A}{n}
          → n ⊢ ($_ {Γ} r {p}) ok
    ifOK : ∀{Γ A}{L : Γ ⊢ ` 𝔹}{M N : Γ ⊢ A}{n}
          → 0 ⊢ L ok → 0 ⊢ M ok → 0 ⊢ N ok
          → n ⊢ (if L M N) ok
    consOK : ∀{Γ A B}{M : Γ ⊢ A}{N : Γ ⊢ B}{n}
          → 0 ⊢ M ok → 0 ⊢ N ok
          → n ⊢ (cons M N) ok
    fstOK : ∀{Γ A B}{M : Γ ⊢ A `× B}{n}
          → 0 ⊢ M ok
          → n ⊢ fst M ok
    sndOK : ∀{Γ A B}{M : Γ ⊢ A `× B}{n}
          → 0 ⊢ M ok
          → n ⊢ snd M ok
    inlOK : ∀{Γ A B}{M : Γ ⊢ A}{n}
          → 0 ⊢ M ok
          → n ⊢ (inl {B = B} M) ok
    inrOK : ∀{Γ A B}{M : Γ ⊢ B}{n}
          → 0 ⊢ M ok
          → n ⊢ (inr {A = A} M) ok
    caseOK : ∀{Γ A B C}{L : Γ ⊢ A `⊎ B}{M : Γ ⊢ A ⇒ C}{N : Γ ⊢ B ⇒ C}{n}
           → 0 ⊢ L ok → 0 ⊢ M ok → 0 ⊢ N ok
           → n ⊢ (case L M N) ok
    blameOK : ∀{Γ A ℓ}{n}
           → n ⊢ (blame {Γ}{A} ℓ) ok

  weakenOK : ∀{Γ A}{M : Γ ⊢ A}{n m}
       → n ⊢ M ok → m ≤ n
       → m ⊢ M ok
  weakenOK (castOK Mok x) m≤n = castOK (weakenOK Mok (s≤s m≤n)) (≤-trans m≤n x)
  weakenOK varOK m≤n = varOK
  weakenOK (lamOK Mok) m≤n = lamOK Mok
  weakenOK (appOK Mok Mok₁) m≤n = appOK Mok Mok₁
  weakenOK litOK m≤n = litOK
  weakenOK (ifOK Mok Mok₁ Mok₂) m≤n = ifOK Mok Mok₁ Mok₂
  weakenOK (consOK Mok Mok₁) m≤n = consOK Mok Mok₁
  weakenOK (fstOK Mok) m≤n = fstOK Mok
  weakenOK (sndOK Mok) m≤n = sndOK Mok
  weakenOK (inlOK Mok) m≤n = inlOK Mok
  weakenOK (inrOK Mok) m≤n = inrOK Mok
  weakenOK (caseOK Mok Mok₁ Mok₂) m≤n = caseOK Mok Mok₁ Mok₂
  weakenOK blameOK m≤n = blameOK

  plug→OK : ∀{Γ A B}{M : Γ ⊢ A}{F : Frame A B}{n}
    → n ⊢ plug M F ok
    → 0 ⊢ M ok 
  plug→OK {F = EfficientParamCasts.F-·₁ x} (appOK Mok Mok₁) = Mok
  plug→OK {F = EfficientParamCasts.F-·₂ M} (appOK Mok Mok₁) = Mok₁
  plug→OK {F = EfficientParamCasts.F-if x x₁} (ifOK Mok Mok₁ Mok₂) = Mok
  plug→OK {F = EfficientParamCasts.F-×₁ x} (consOK Mok Mok₁) = Mok₁
  plug→OK {F = EfficientParamCasts.F-×₂ x} (consOK Mok Mok₁) = Mok
  plug→OK {F = EfficientParamCasts.F-fst} (fstOK Mok) = Mok
  plug→OK {F = EfficientParamCasts.F-snd} (sndOK Mok) = Mok
  plug→OK {F = EfficientParamCasts.F-inl} (inlOK Mok) = Mok
  plug→OK {F = EfficientParamCasts.F-inr} (inrOK Mok) = Mok
  plug→OK {F = EfficientParamCasts.F-case x x₁} (caseOK Mok Mok₁ Mok₂) = Mok

  OK→plug : ∀{Γ A B}{M M′ : Γ ⊢ A}{F : Frame A B}{n}
    → n ⊢ plug M F ok
    → 0 ⊢ M′ ok
    → n ⊢ plug M′ F ok
  OK→plug {F = EfficientParamCasts.F-·₁ x} (appOK MFok MFok₁) Mok = appOK Mok MFok₁
  OK→plug {F = EfficientParamCasts.F-·₂ M} (appOK MFok MFok₁) Mok = appOK MFok Mok
  OK→plug {F = EfficientParamCasts.F-if x x₁} (ifOK MFok MFok₁ MFok₂) Mok =
     ifOK Mok MFok₁ MFok₂
  OK→plug {F = EfficientParamCasts.F-×₁ x} (consOK MFok MFok₁) Mok = consOK MFok Mok
  OK→plug {F = EfficientParamCasts.F-×₂ x} (consOK MFok MFok₁) Mok = consOK Mok MFok₁
  OK→plug {F = EfficientParamCasts.F-fst} (fstOK x) Mok = fstOK Mok
  OK→plug {F = EfficientParamCasts.F-snd} (sndOK x) Mok = sndOK Mok
  OK→plug {F = EfficientParamCasts.F-inl} (inlOK x) Mok = inlOK Mok
  OK→plug {F = EfficientParamCasts.F-inr} (inrOK x) Mok = inrOK Mok
  OK→plug {F = EfficientParamCasts.F-case x x₁} (caseOK a b c) Mok = caseOK Mok b c

  preserve-ok : ∀{Γ A}{M M′ : Γ ⊢ A}{n}{ctx : ReductionCtx}
          → n ⊢ M ok  →  ctx / M —→ M′
          → n ⊢ M′ ok

  preserve-ncc : ∀{Γ A}{M M′ : Γ ⊢ A}
          → 0 ⊢ M ok  →  non_cast_ctx / M —→ M′
          → 0 ⊢ M′ ok

  preserve-any : ∀{Γ A}{M M′ : Γ ⊢ A}{n}
          → n ⊢ M ok  →  any_ctx / M —→ M′
          → n ⊢ M′ ok

  {- todo: progress -}

  preserve-ok MFok (EfficientParamCasts.ξ M-→M′) =
     let Mok = plug→OK MFok in
     let IH = preserve-ok Mok M-→M′ in
     OK→plug MFok IH
  preserve-ok (castOK Mok x) (EfficientParamCasts.ξ-cast M-→M′) =
     let IH = preserve-ok Mok M-→M′ in
     castOK IH x
  preserve-ok Mok EfficientParamCasts.ξ-blame = blameOK
  preserve-ok Mok EfficientParamCasts.ξ-cast-blame = blameOK
  preserve-ok (appOK (lamOK Mok) Mok₁) (EfficientParamCasts.β x) = {!!}
  preserve-ok Mok EfficientParamCasts.δ = {!!}
  preserve-ok Mok EfficientParamCasts.β-if-true = {!!}
  preserve-ok Mok EfficientParamCasts.β-if-false = {!!}
  preserve-ok Mok (EfficientParamCasts.β-fst x x₁) = {!!}
  preserve-ok Mok (EfficientParamCasts.β-snd x x₁) = {!!}
  preserve-ok Mok (EfficientParamCasts.β-caseL x) = {!!}
  preserve-ok Mok (EfficientParamCasts.β-caseR x) = {!!}
  preserve-ok Mok (EfficientParamCasts.cast v) = {!!}
  preserve-ok Mok (EfficientParamCasts.fun-cast v x) = {!!}
  preserve-ok Mok (EfficientParamCasts.fst-cast v) = {!!}
  preserve-ok Mok (EfficientParamCasts.snd-cast v) = {!!}
  preserve-ok Mok (EfficientParamCasts.case-cast v) = {!!}
  preserve-ok (castOK (castOK Mok x₁) x) EfficientParamCasts.compose-casts =
     castOK (weakenOK Mok (s≤s (≤-trans x (s≤s z≤n)))) x


  preserve-any MFok (ξ M—→M′) =
     let Mok = plug→OK MFok in
     {!!}
  preserve-any Mok ξ-blame = {!!}
  preserve-any Mok (β x) = {!!}
  preserve-any Mok δ = {!!}
  preserve-any Mok β-if-true = {!!}
  preserve-any Mok β-if-false = {!!}
  preserve-any Mok (β-fst x x₁) = {!!}
  preserve-any Mok (β-snd x x₁) = {!!}
  preserve-any Mok (β-caseL x) = {!!}
  preserve-any Mok (β-caseR x) = {!!}
  preserve-any Mok (fun-cast v x) = {!!}
  preserve-any Mok (fst-cast v) = {!!}
  preserve-any Mok (snd-cast v) = {!!}
  preserve-any Mok (case-cast v) = {!!}

  preserve-ncc (castOK Mok x) (EfficientParamCasts.ξ-cast M-→M′) =
     let IH = preserve-any Mok M-→M′ in castOK IH z≤n
  preserve-ncc (castOK Mok x) EfficientParamCasts.ξ-cast-blame = blameOK
  preserve-ncc (castOK Mok x) (EfficientParamCasts.cast v) = {!!}
  preserve-ncc (castOK (castOK Mok x₁) x) EfficientParamCasts.compose-casts =
     castOK (weakenOK Mok (s≤s z≤n)) z≤n

{-
  data CastCount : ∀{Γ A} → Γ ⊢ A → ℕ → Set where
    ccCast : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}
       → CastCount M n → n ≤ 1 → CastCount (M ⟨ c ⟩) (suc n)
    ccVar : ∀{Γ A}{∋x : Γ ∋ A} → CastCount (` ∋x) 0
    ccLam : ∀{Γ B A}{N : Γ , A ⊢ B}{n}
          → CastCount N n → CastCount (ƛ N) 0
    ccApp : ∀{Γ A B}{L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}{n m}
          → CastCount L n → CastCount M m → CastCount (L · M) 0
    ccLit : ∀{Γ : Context}{A}{r : rep A}{p : Prim A}
          → CastCount {Γ} ($_ r {p}) 0
    ccIf : ∀{Γ A}{L : Γ ⊢ ` 𝔹}{M N : Γ ⊢ A}{m n p}
          → CastCount L n → CastCount M m → CastCount N p
          → CastCount (if L M N) 0
    ccCons : ∀{Γ A B}{M : Γ ⊢ A}{N : Γ ⊢ B}{n m}
          → CastCount M n → CastCount N m → CastCount (cons M N) 0
    ccFst : ∀{Γ A B}{M : Γ ⊢ A `× B}{n} → CastCount M n → CastCount (fst M) 0
    ccSnd : ∀{Γ A B}{M : Γ ⊢ A `× B}{n} → CastCount M n → CastCount (snd M) 0
    ccInl : ∀{Γ A B}{M : Γ ⊢ A}{n} → CastCount M n
          → CastCount {Γ}{A `⊎ B} (inl M) 0
    ccInr : ∀{Γ A B}{M : Γ ⊢ B}{n} → CastCount M n
          → CastCount {Γ}{A `⊎ B} (inr M) 0
    ccCase : ∀{Γ A B C}{L : Γ ⊢ A `⊎ B}{M : Γ ⊢ A ⇒ C}{N : Γ ⊢ B ⇒ C}{n m p}
           → CastCount L n → CastCount M m → CastCount N p
           → CastCount (case L M N) 0
    ccBlame : ∀{Γ A ℓ} → CastCount {Γ}{A} (blame {Γ}{A} ℓ) 0

  cast-count≤2 : ∀{Γ A}{M : Γ ⊢ A}{n} → CastCount M n → n ≤ 2
  cast-count≤2 (ccCast ccM x) = s≤s x
  cast-count≤2 ccVar = z≤n
  cast-count≤2 (ccLam ccM) = z≤n
  cast-count≤2 (ccApp ccM ccM₁) = z≤n
  cast-count≤2 ccLit = z≤n
  cast-count≤2 (ccIf ccM ccM₁ ccM₂) = z≤n
  cast-count≤2 (ccCons ccM ccM₁) = z≤n
  cast-count≤2 (ccFst ccM) = z≤n
  cast-count≤2 (ccSnd ccM) = z≤n
  cast-count≤2 (ccInl ccM) = z≤n
  cast-count≤2 (ccInr ccM) = z≤n
  cast-count≤2 (ccCase ccM ccM₁ ccM₂) = z≤n
  cast-count≤2 ccBlame = z≤n

  module PreserveCount
    (applyCastCount : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}{a}
         → CastCount M n → n ≤ 1 → (v : Value M)
         → Σ[ n′ ∈ ℕ ] (CastCount (applyCast M v c {a}) n′))
    where

    castcount-plug-0 : ∀ {Γ A B}{M : Γ ⊢ A}{n} (F : Frame A B)
         → CastCount (plug M F) n → n ≡ 0
    castcount-plug-0 (F-·₁ x) (ccApp ccMF ccMF₁) = refl
    castcount-plug-0 (F-·₂ x) (ccApp ccMF ccMF₁) = refl
    castcount-plug-0 (F-if x x₁) (ccIf ccL ccM ccN) = refl
    castcount-plug-0 (F-×₁ x) (ccCons ccM ccN) = refl
    castcount-plug-0 (F-×₂ x) (ccCons ccM ccN) = refl
    castcount-plug-0 F-fst (ccFst ccM) = refl
    castcount-plug-0 F-snd (ccSnd ccM) = refl
    castcount-plug-0 F-inl (ccInl ccM) = refl
    castcount-plug-0 F-inr (ccInr ccM) = refl
    castcount-plug-0 (F-case x x₁) (ccCase ccL ccM ccN) = refl

    anyctx-castcount-0 : ∀ {Γ A}{M M′ : Γ ⊢ A}{n}
           → CastCount M n → any_ctx / M —→ M′
           → n ≡ 0
    anyctx-castcount-0 ccM (ξ {F = F} M—→M′) = castcount-plug-0 F ccM
    anyctx-castcount-0 ccM (ξ-blame{F = F}) = castcount-plug-0 F ccM
    anyctx-castcount-0 (ccApp ccM ccM₁) (β x) = refl
    anyctx-castcount-0 (ccApp ccM ccM₁) δ = refl
    anyctx-castcount-0 (ccIf ccM ccM₁ ccM₂) β-if-true = refl
    anyctx-castcount-0 (ccIf ccM ccM₁ ccM₂) β-if-false = refl
    anyctx-castcount-0 (ccFst ccM) (β-fst x x₁) = refl
    anyctx-castcount-0 (ccSnd ccM) (β-snd x x₁) = refl
    anyctx-castcount-0 (ccCase ccL ccM ccN) (β-caseL x) = refl
    anyctx-castcount-0 (ccCase ccL ccM ccN) (β-caseR x) = refl
    anyctx-castcount-0 (ccApp ccM ccM₁) (fun-cast v x) = refl
    anyctx-castcount-0 (ccFst ccM) (fst-cast v) = refl
    anyctx-castcount-0 (ccSnd ccM) (snd-cast v) = refl
    anyctx-castcount-0 (ccCase ccL ccM ccN) (case-cast v) = refl
           
    preserve-castcount-nc : ∀ {Γ A}{M M′ : Γ ⊢ A}{n}
           → CastCount M 0 → any_ctx / M —→ M′
           → CastCount M′ n
    preserve-castcount-nc ccM (ξ M—→M′) = {!!}
    preserve-castcount-nc ccM ξ-blame = {!!}
    preserve-castcount-nc ccM (β x) = {!!}
    preserve-castcount-nc ccM δ = {!!}
    preserve-castcount-nc ccM β-if-true = {!!}
    preserve-castcount-nc ccM β-if-false = {!!}
    preserve-castcount-nc ccM (β-fst x x₁) = {!!}
    preserve-castcount-nc ccM (β-snd x x₁) = {!!}
    preserve-castcount-nc ccM (β-caseL x) = {!!}
    preserve-castcount-nc ccM (β-caseR x) = {!!}
    preserve-castcount-nc ccM (fun-cast v x) = {!!}
    preserve-castcount-nc ccM (fst-cast v) = {!!}
    preserve-castcount-nc ccM (snd-cast v) = {!!}
    preserve-castcount-nc ccM (case-cast v) = {!!}

    preserve-castcount-c : ∀ {Γ A}{M M′ : Γ ⊢ A}{n}
           → CastCount M n → non_cast_ctx / M —→ M′
           → Σ[ n′ ∈ ℕ ] CastCount M′ n′
    preserve-castcount-c ccM (ξ-cast M—→M′) = {!!}
    preserve-castcount-c ccM ξ-cast-blame = ⟨ 0 , ccBlame ⟩
    preserve-castcount-c (ccCast ccM x) (cast v) = applyCastCount ccM x v
    preserve-castcount-c (ccCast (ccCast ccM x₁) (s≤s z≤n)) compose-casts =
      ⟨ 1 , (ccCast ccM x₁) ⟩
-}  
{-
  plug-maybe→maybe : ∀ {Γ A B} (M : Γ ⊢ A) (F : Frame A B)
               → MaybeCast (plug M F) → MaybeCast M
  plug-maybe→maybe M (F-·₁ x) (notCast (ncapp x₁ x₂)) = x₁
  plug-maybe→maybe M (F-·₂ M₁) (notCast (ncapp x₁ x₂)) = x₂
  plug-maybe→maybe M (F-if x x₁) (notCast (ncif x₂ x₃ x₄)) = x₂
  plug-maybe→maybe M (F-×₁ x) (notCast (nccons x₁ x₂)) = x₂
  plug-maybe→maybe M (F-×₂ x) (notCast (nccons x₁ x₂)) = x₁
  plug-maybe→maybe M F-fst (notCast (ncfst x)) = x
  plug-maybe→maybe M F-snd (notCast (ncsnd x)) = x
  plug-maybe→maybe M F-inl (notCast (ncinl x)) = x
  plug-maybe→maybe M F-inr (notCast (ncinr x)) = x
  plug-maybe→maybe M (F-case x x₁) (notCast (nccase x₂ x₃ x₄)) = x₂

  plug-not→maybe : ∀ {Γ A B} (M : Γ ⊢ A) (F : Frame A B)
               → NotCast (plug M F) → MaybeCast M
  plug-not→maybe M (F-·₁ N) (ncapp mcM mcN) = mcM
  plug-not→maybe M (F-·₂ L) (ncapp mcL mcM) = mcM
  plug-not→maybe M (F-if L N) (ncif x x₁ x₂) = x
  plug-not→maybe M (F-×₁ x) (nccons ncMF ncMF₁) = ncMF₁
  plug-not→maybe M (F-×₂ x) (nccons ncMF ncMF₁) = ncMF
  plug-not→maybe M F-fst (ncfst x) = x
  plug-not→maybe M F-snd (ncsnd x) = x
  plug-not→maybe M F-inl (ncinl x) = x
  plug-not→maybe M F-inr (ncinr x) = x
  plug-not→maybe M (F-case x x₁) (nccase x₂ ncMF ncMF₁) = x₂
               
  plug-notcast : ∀ {Γ A B} (M M′ : Γ ⊢ A) (F : Frame A B)
               → NotCast (plug M F) → MaybeCast M′ 
               → NotCast (plug M′ F)
  plug-notcast M M′ (F-·₁ N) (ncapp mcM mcN) mcM′ = ncapp mcM′ mcN
  plug-notcast M M′ (F-·₂ L) (ncapp x x₁) mcM′ = ncapp x mcM′
  plug-notcast M M′ (F-if L N) (ncif x x₁ x₂) mcM′ = ncif mcM′ x₁ x₂
  plug-notcast M M′ (F-×₁ N) (nccons ncMF ncMF₁) mcM′ = nccons ncMF mcM′
  plug-notcast M M′ (F-×₂ N) (nccons ncMF ncMF₁) mcM′ = nccons mcM′ ncMF₁
  plug-notcast M M′ F-fst (ncfst x) mcM′ = ncfst mcM′
  plug-notcast M M′ F-snd (ncsnd x) mcM′ = ncsnd mcM′
  plug-notcast M M′ F-inl (ncinl ncMF) mcM′ = ncinl mcM′
  plug-notcast M M′ F-inr (ncinr ncMF) mcM′ = ncinr mcM′
  plug-notcast M M′ (F-case L N) (nccase x ncMF ncMF₁) mcM′ =
      nccase mcM′ ncMF ncMF₁

  plug-maybecast : ∀ {Γ A B} (M M′ : Γ ⊢ A) (F : Frame A B)
               → MaybeCast (plug M F) → MaybeCast M′ 
               → MaybeCast (plug M′ F)
  plug-maybecast M M′ (F-·₁ x) (notCast (ncapp mcM mcN)) mcM′ =
     notCast (ncapp mcM′ mcN)
  plug-maybecast M M′ (F-·₂ M₁) (notCast (ncapp mcM mcN)) mcM′ =
     notCast (ncapp mcM mcM′)
  plug-maybecast M M′ (F-if x x₁) (notCast (ncif mcL mcM mcN)) mcM′ =
     notCast (ncif mcM′ mcM mcN)
  plug-maybecast M M′ (F-×₁ x) (notCast (nccons mcM mcN)) mcM′ =
     notCast (nccons mcM mcM′)
  plug-maybecast M M′ (F-×₂ x) (notCast (nccons mcM mcN)) mcM′ =
     notCast (nccons mcM′ mcN)
  plug-maybecast M M′ F-fst (notCast (ncfst mcM)) mcM′ =
     notCast (ncfst mcM′)
  plug-maybecast M M′ F-snd (notCast (ncsnd mcM)) mcM′ =
     notCast (ncsnd mcM′)
  plug-maybecast M M′ F-inl (notCast (ncinl mcM)) mcM′ =
     notCast (ncinl mcM′)
  plug-maybecast M M′ F-inr (notCast (ncinr mcM)) mcM′ =
     notCast (ncinr mcM′)
  plug-maybecast M M′ (F-case x x₁) (notCast (nccase mcL mcM mcN)) mcM′ =
     notCast (nccase mcM′ mcM mcN)

  preserve-maybecast : ∀ {Γ A}{M M′ : Γ ⊢ A} {ctx : ReductionCtx}
         → MaybeCast M
         → ctx / M —→ M′
         → MaybeCast M′


  rename-notcast : ∀ {Γ Δ A} (N : Γ ⊢ A) (ρ : ∀{B} → Γ ∋ B → Δ ∋ B)
         →  NotCast N → NotCast (rename ρ N)
  rename-maybecast : ∀ {Γ Δ A} (N : Γ ⊢ A) (ρ : ∀{B} → Γ ∋ B → Δ ∋ B)
         →  MaybeCast N → MaybeCast (rename ρ N)
         
  rename-notcast (` ∋x) ρ ncvar = ncvar
  rename-notcast (ƛ N) ρ (nclam x) = nclam (rename-maybecast N (ext ρ) x)
  rename-notcast (L · M) ρ (ncapp x x₁) =
     ncapp (rename-maybecast L ρ x) (rename-maybecast M ρ x₁)
  rename-notcast .($ _) ρ nclit = nclit
  rename-notcast (if L M N) ρ (ncif x x₁ x₂) =
      ncif (rename-maybecast L ρ x) (rename-maybecast M ρ x₁)
           (rename-maybecast N ρ x₂)
  rename-notcast (cons M N) ρ (nccons x x₁) =
      nccons (rename-maybecast M ρ x) (rename-maybecast N ρ x₁)
  rename-notcast (fst M) ρ (ncfst x) = ncfst (rename-maybecast M ρ x)
  rename-notcast (snd M) ρ (ncsnd x) = ncsnd (rename-maybecast M ρ x)
  rename-notcast (inl M) ρ (ncinl x) = ncinl (rename-maybecast M ρ x)
  rename-notcast (inr M) ρ (ncinr x) = ncinr (rename-maybecast M ρ x)
  rename-notcast (case L M N) ρ (nccase x x₁ x₂) =
      nccase (rename-maybecast L ρ x) (rename-maybecast M ρ x₁)
             (rename-maybecast N ρ x₂)
  rename-notcast (blame ℓ) ρ ncblame = ncblame
  
  rename-maybecast N ρ (notCast x) = notCast (rename-notcast N ρ x)
  rename-maybecast (M ⟨ c ⟩) ρ (isCast x) = isCast (rename-notcast M ρ x)
  rename-maybecast (M ⟨ c ⟩) ρ (castVal mcN vM) =
     castVal (rename-maybecast M ρ mcN ) (rename-value M ρ vM)

  OKSubst : ∀{Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → Set
  OKSubst {Γ}{Δ} σ = ∀ {A} (x : Γ ∋ A)
                   → (NotCast (σ x)) ⊎ (MaybeCast (σ x) × Value (σ x))

  OKSubst-exts : ∀ {Γ Δ A} (σ : ∀{B} → Γ ∋ B → Δ ⊢ B)
         → OKSubst σ → OKSubst (exts σ {B = A})
  OKSubst-exts σ okσ Z = inj₁ ncvar
  OKSubst-exts σ okσ (S ∋x)
      with okσ ∋x
  ... | inj₁ xx = inj₁ (rename-notcast (σ ∋x) S_ xx)
  ... | inj₂ (⟨ yy , zz ⟩) =
        inj₂ (⟨ (rename-maybecast (σ ∋x) S_ yy) , (rename-value (σ ∋x) S_ zz) ⟩)

  subst-maybecast : ∀ {Γ Δ A} (N : Γ ⊢ A) (σ : ∀{B} → Γ ∋ B → Δ ⊢ B)
         → OKSubst σ → MaybeCast N
         → MaybeCast (subst σ N)
         
  subst-notcast : ∀ {Γ Δ A} (N : Γ ⊢ A) (σ : ∀{B} → Γ ∋ B → Δ ⊢ B)
         → OKSubst σ → NotCast N
         → NotCast (subst σ N) ⊎ (MaybeCast (subst σ N) × Value (subst σ N))
  subst-notcast (` ∋x) σ okσ ncvar = okσ ∋x
  subst-notcast (ƛ N) σ okσ (nclam mcN) =
    let IH = subst-maybecast N (exts σ) (OKSubst-exts σ okσ) mcN in
    inj₂ (⟨ (notCast (nclam IH)) , (S-val V-ƛ) ⟩)
  subst-notcast (L · M) σ okσ (ncapp x x₁) =
     let IH1 = subst-maybecast L σ okσ x in
     let IH2 = subst-maybecast M σ okσ x₁ in
     inj₁ (ncapp IH1 IH2)
  subst-notcast ($_ r {p}) σ okσ nclit = inj₁ nclit
  subst-notcast (if L M N) σ okσ (ncif x x₁ x₂) =
     let IH1 = subst-maybecast L σ okσ x in
     let IH2 = subst-maybecast M σ okσ x₁ in
     let IH3 = subst-maybecast N σ okσ x₂ in
     inj₁ (ncif IH1 IH2 IH3)
  subst-notcast (cons M N) σ okσ (nccons x x₁) =
     let IH1 = subst-maybecast M σ okσ x in
     let IH2 = subst-maybecast N σ okσ x₁ in
     inj₁ (nccons IH1 IH2)
  subst-notcast (fst M) σ okσ (ncfst x) =
     inj₁ (ncfst (subst-maybecast M σ okσ x))
  subst-notcast (snd M) σ okσ (ncsnd x) =
     inj₁ (ncsnd (subst-maybecast M σ okσ x))
  subst-notcast (inl M) σ okσ (ncinl x) =
     inj₁ (ncinl (subst-maybecast M σ okσ x))
  subst-notcast (inr M) σ okσ (ncinr x) =
     inj₁ (ncinr (subst-maybecast M σ okσ x))
  subst-notcast (case L M N) σ okσ (nccase x x₁ x₂) =
     let IH1 = subst-maybecast L σ okσ x in
     let IH2 = subst-maybecast M σ okσ x₁ in
     let IH3 = subst-maybecast N σ okσ x₂ in
     inj₁ (nccase IH1 IH2 IH3)
  subst-notcast (blame ℓ) σ okσ ncblame = inj₁ ncblame

  subst-maybecast N σ okσ (notCast ncN)
      with subst-notcast N σ okσ ncN
  ... | inj₁ nc = notCast nc
  ... | inj₂ (⟨ mc , v ⟩) = mc
  subst-maybecast (M ⟨ c ⟩) σ okσ (isCast ncM)
      with subst-notcast M σ okσ ncM
  ... | inj₁ nc = isCast nc
  ... | inj₂ (⟨ mc , v ⟩) = castVal mc v
  subst-maybecast (M ⟨ c ⟩) σ okσ (castVal mcM x) =
     let IH = subst-maybecast M σ okσ mcM in
     castVal IH (subst-value M σ x)

  sub-maybecast : ∀ {Γ A B} (N : Γ , A ⊢ B) (M : Γ ⊢ A)
         → MaybeCast M →  Value M → MaybeCast N
         → MaybeCast (N [ M ])
  sub-maybecast N M mcM vM mcN = subst-maybecast N (subst-zero M) G mcN
    where
    G : OKSubst (subst-zero M)
    G Z = inj₂ (⟨ mcM , vM ⟩)
    G (S ∋x) = inj₁ ncvar


  preserve-notcast : ∀ {Γ A}{M M′ : Γ ⊢ A} 
         → NotCast M
         → any_ctx / M —→ M′
         → MaybeCast M′
  preserve-notcast ncM (ξ {M = M}{M′}{F} M—→M′) =
     let mcM′ = preserve-maybecast (plug-not→maybe M F ncM) M—→M′ in
     notCast (plug-notcast M M′ F ncM mcM′)
  preserve-notcast ncM ξ-blame = notCast ncblame
  preserve-notcast (ncapp (notCast (nclam mcN)) mcW) (β {N = N}{W} vW) =
      sub-maybecast N W mcW vW mcN
  preserve-notcast ncM δ = notCast nclit
  preserve-notcast (ncif x x₁ x₂) β-if-true = x₁
  preserve-notcast (ncif x x₁ x₂) β-if-false = x₂
  preserve-notcast (ncfst (notCast (nccons x₂ x₃))) (β-fst x x₁) = x₂
  preserve-notcast (ncsnd (notCast (nccons x₂ x₃))) (β-snd x x₁) = x₃
  preserve-notcast (nccase (notCast (ncinl x₁)) x₂ x₃) (β-caseL x) =
     notCast (ncapp x₂ x₁)
  preserve-notcast (nccase (notCast (ncinr x₁)) x₂ x₃) (β-caseR x) =
     notCast (ncapp x₃ x₁)
  preserve-notcast (ncapp (isCast x₁) x₂) (fun-cast v x) =
     isCast (ncapp (notCast x₁) (castVal x₂ x))
  preserve-notcast (ncapp (castVal x₁ x₃) x₂) (fun-cast v x) =
     isCast (ncapp x₁ (castVal x₂ x))
  preserve-notcast (ncfst (isCast x)) (fst-cast v) =
     isCast (ncfst (notCast x))
  preserve-notcast (ncfst (castVal x x₁)) (fst-cast v) =
     isCast (ncfst x)
  preserve-notcast (ncsnd (isCast x)) (snd-cast v) = isCast (ncsnd (notCast x))
  preserve-notcast (ncsnd (castVal x x₁)) (snd-cast v) = isCast (ncsnd x)
  preserve-notcast (nccase (isCast x) x₁ x₂) (case-cast v) =
     notCast (nccase (notCast x)
                (notCast (nclam (notCast (ncapp (rename-maybecast _ S_ x₁)
                                                (isCast ncvar)))))
                (notCast (nclam (notCast (ncapp (rename-maybecast _ S_ x₂)
                                                (isCast ncvar))))))
  preserve-notcast (nccase (castVal x x₃) x₁ x₂) (case-cast v) =
    notCast (nccase x (notCast (nclam (notCast (ncapp (rename-maybecast _ S_ x₁)
                                                      (isCast ncvar)))))
                      (notCast (nclam (notCast (ncapp (rename-maybecast _ S_ x₂)
                                                      (isCast ncvar))))))
  
  preserve-maybecast mcM (ξ {M = M}{M′}{F} M-→M′) =
    let IH = preserve-maybecast (plug-maybe→maybe M F mcM) M-→M′ in
    plug-maybecast M M′ F mcM IH 
  preserve-maybecast (isCast x) (ξ-cast M-→M′) =
    let IH = preserve-notcast x M-→M′ in
    {!!}
  preserve-maybecast (castVal mcM x) (ξ-cast M-→M′) = {!!}
  preserve-maybecast mcM ξ-blame = {!!}
  preserve-maybecast mcM ξ-cast-blame = {!!}
  preserve-maybecast mcM (β x) = {!!}
  preserve-maybecast mcM δ = {!!}
  preserve-maybecast mcM β-if-true = {!!}
  preserve-maybecast mcM β-if-false = {!!}
  preserve-maybecast mcM (β-fst x x₁) = {!!}
  preserve-maybecast mcM (β-snd x x₁) = {!!}
  preserve-maybecast mcM (β-caseL x) = {!!}
  preserve-maybecast mcM (β-caseR x) = {!!}
  preserve-maybecast mcM (cast v) = {!!}
  preserve-maybecast mcM (fun-cast v x) = {!!}
  preserve-maybecast mcM (fst-cast v) = {!!}
  preserve-maybecast mcM (snd-cast v) = {!!}
  preserve-maybecast mcM (case-cast v) = {!!}
  preserve-maybecast mcM compose-casts = {!!}

  module EfficientCompile
    (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
    where

    open import GTLC
    open import GTLC2CC Cast cast

    compile-efficient : ∀{Γ A} (M : Term) (d : Γ ⊢G M ⦂ A) → NotCast (compile M d)
    compile-efficient (` x) (⊢var ∋x) = ncvar
    compile-efficient (ƛ A ˙ N) (⊢lam d) = nclam (notCast (compile-efficient N d))
    compile-efficient (L · M at ℓ) (⊢app d₁ d₂ mA A1~B) =
       let IH1 = compile-efficient L d₁ in
       let IH2 = compile-efficient M d₂ in
       ncapp (isCast IH1) (isCast IH2)
    compile-efficient .($ _ # _) ⊢lit = nclit
    compile-efficient (if L then M else N at ℓ) (⊢if d d₁ d₂ mA aa) =
        ncif (isCast (compile-efficient L d))
             (isCast (compile-efficient M d₁))
             (isCast (compile-efficient N d₂))
    compile-efficient (⟦ M , N ⟧) (⊢cons d d₁) =
        nccons (notCast (compile-efficient M d)) (notCast (compile-efficient N d₁))
    compile-efficient (fst M at ℓ) (⊢fst d x) = ncfst (isCast (compile-efficient M d))
    compile-efficient (snd M at ℓ) (⊢snd d x) = ncsnd (isCast (compile-efficient M d))
    compile-efficient (inl M other B) (⊢inl d) =
        ncinl (notCast (compile-efficient M d))
    compile-efficient (inr M other A) (⊢inr d) =
        ncinr (notCast (compile-efficient M d))
    compile-efficient (case L of B₁ ⇒ M ∣ C₁ ⇒ N at ℓ) (⊢case d d₁ d₂ abc bc) =
      let IH1 = compile-efficient L d in 
      let IH2 = compile-efficient M d₁ in
      let IH3 = compile-efficient N d₂ in 
        nccase (isCast IH1) (notCast (nclam (isCast (compile-efficient M d₁))))
                            (notCast (nclam (isCast (compile-efficient N d₂))))

-}
{-
  simple-size : ∀{Γ A} (M : Γ ⊢ A) → MaybeCast M → SimpleValue M
            → size M ≤ 8 * ideal-size M
            
  value-size : ∀{Γ A} (M : Γ ⊢ A) → MaybeCast M → Value M
            → size M ≤ 1 + 8 * ideal-size M
  maybecast-size : ∀{Γ A} (M : Γ ⊢ A) → MaybeCast M
            → size M ≤ 2 + 8 * ideal-size M

  simple-size (ƛ N) (notCast (nclam mcN)) V-ƛ =
      let IH = maybecast-size N mcN in
      begin
        1 + size N
        ≤⟨ s≤s IH ⟩
        3 + (8 * ideal-size N)
        ≤⟨ +-mono-≤ X ≤-refl ⟩
        8 + (8 * ideal-size N)
        ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
        8 * (1 + ideal-size N)
      ∎
      where
      X : 3 ≤ 8
      X = s≤s (s≤s (s≤s z≤n))
  simple-size ($_ r {p}) mcM V-const = s≤s z≤n
  simple-size (cons M N) (notCast (nccons mcM mcN)) (V-pair vM vN) =
      let IH1 = maybecast-size M mcM in
      let IH2 = maybecast-size N mcN in
      begin
        1 + (size M + size N)
        ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
        1 + ((2 + 8 * ideal-size M) + (2 + 8 * ideal-size N))
        ≤⟨ ≤-reflexive (solve 2 (λ x y → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y)) := con 5 :+ (con 8 :* x :+ con 8 :* y)) refl (ideal-size M) (ideal-size N)) ⟩
        5 + (8 * ideal-size M + 8 * ideal-size N)
        ≤⟨ +-monoʳ-≤ 5 ((≤-reflexive ((sym (*-distribˡ-+ 8 (ideal-size M) (ideal-size N) ))))) ⟩
        5 + 8 * (ideal-size M + ideal-size N)
        ≤⟨ +-mono-≤ X ≤-refl ⟩
        8 + 8 * (ideal-size M + ideal-size N)
        ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
        8 * (1 + (ideal-size M + ideal-size N))
      ∎
    where
    X : 5 ≤ 8
    X = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
    open +-*-Solver
  simple-size (inl M) (notCast (ncinl mcM)) (V-inl vM) =
    let IH = value-size M mcM vM in
    begin
      1 + (size M)
      ≤⟨ s≤s IH ⟩
      2 + 8 * ideal-size M
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + (8 * ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * (1 + ideal-size M)
    ∎
    where
    X : 2 ≤ 8
    X = s≤s (s≤s z≤n)
  simple-size (inr M) (notCast (ncinr mcM)) (V-inr vM) =
    let IH = value-size M mcM vM in
    begin
      1 + (size M)
      ≤⟨ s≤s IH ⟩
      2 + 8 * ideal-size M
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + (8 * ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * (1 + ideal-size M)
    ∎
    where
    X : 2 ≤ 8
    X = s≤s (s≤s z≤n)
  nocast-size : ∀{Γ A} (M : Γ ⊢ A) → NotCast M → size M ≤ 8 * ideal-size M
  
  value-size M mcM (Value.S-val sM) = ≤-step (simple-size M mcM sM)
  value-size (M ⟨ c ⟩) (isCast ncM) (V-cast sM) =
    let IH = nocast-size M ncM in s≤s IH
  value-size (M ⟨ c ⟩) (castVal mcM vM) (V-cast sM) =
    let IH = simple-size M mcM sM in s≤s IH

  nocast-size (` ∋x) ncvar = s≤s z≤n
  nocast-size (ƛ N) (nclam mcN) =
    let IH = maybecast-size N mcN in
    begin
      suc (size N)
      ≤⟨ s≤s IH ⟩
      3 + 8 * (ideal-size N)
      ≤⟨ +-mono-≤ (s≤s (s≤s (s≤s (z≤n{n = 5})))) ≤-refl ⟩
      8 + 8 * (ideal-size N)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size N)
    ∎
  nocast-size (L · M) (ncapp mcL mcM) =
    let IH1 = maybecast-size L mcL in
    let IH2 = maybecast-size M mcM in
    begin
      1 + (size L + size M)
      ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
      1 + ((2 + 8 * ideal-size L) + (2 + 8 * ideal-size M))
      ≤⟨ ≤-reflexive (solve 2 (λ x y → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y))
                         := con 5 :+ ((con 8 :* x) :+ (con 8 :* y))) refl (ideal-size L) (ideal-size M)) ⟩
      5 + ((8 * ideal-size L) + (8 * ideal-size M))
      ≤⟨ +-mono-≤ (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n {n = 3})))))) ≤-refl ⟩
      8 + ((8 * ideal-size L) + (8 * ideal-size M))
      ≤⟨ +-monoʳ-≤ 8 (≤-reflexive ((sym (*-distribˡ-+ 8 (ideal-size L) (ideal-size M) )))) ⟩
      8 + 8 * (ideal-size L + ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size L + ideal-size M)
    ∎
    where open +-*-Solver
  nocast-size ($_ r {p}) nclit = s≤s z≤n
  nocast-size (if L M N) (ncif mcL mcM mcN) =
    let IH1 = maybecast-size L mcL in
    let IH2 = maybecast-size M mcM in
    let IH3 = maybecast-size N mcN in
    begin
      1 + (size L + size M + size N)
      ≤⟨ s≤s (+-mono-≤ (+-mono-≤ IH1 IH2) IH3) ⟩
      1 + ((2 + 8 * ideal-size L) + (2 + 8 * ideal-size M) + (2 + 8 * ideal-size N))
      ≤⟨ ≤-reflexive (solve 3 (λ x y z → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y) :+ (con 2 :+ con 8 :* z)) := con 7 :+ con 8 :* (x :+ y :+ z)) refl (ideal-size L) (ideal-size M) (ideal-size N)) ⟩
      7 + 8 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + 8 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size L + ideal-size M + ideal-size N)
    ∎
    where
    X : 7 ≤ 8
    X = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
    open +-*-Solver
  nocast-size (cons M N) (nccons mcM mcN) =
    let IH1 = maybecast-size M mcM in
    let IH2 = maybecast-size N mcN in
    begin
     1 + (size M + size N)
     ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
     1 + ((2 + 8 * ideal-size M) + (2 + 8 * ideal-size N))
     ≤⟨ ≤-reflexive (solve 2 (λ x y → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y)) := con 5 :+ ((con 8 :* x) :+ (con 8 :* y))) refl (ideal-size M) (ideal-size N)) ⟩
     5 + ((8 * ideal-size M) + (8 * ideal-size N))
     ≤⟨ +-mono-≤ X ≤-refl ⟩
     8 + (8 * ideal-size M + 8 * ideal-size N)
     ≤⟨ +-monoʳ-≤ 8 ((≤-reflexive ((sym (*-distribˡ-+ 8 (ideal-size M) (ideal-size N) ))))) ⟩
     8 + 8 * (ideal-size M + ideal-size N)
     ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
     8 * suc (ideal-size M + ideal-size N)
    ∎
    where
    X : 5 ≤ 8
    X = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
    open +-*-Solver
  nocast-size (fst M) (ncfst mcM) =
    let IH = maybecast-size M mcM in
    begin
     1 + size M
     ≤⟨ s≤s IH ⟩
     3 + 8 * (ideal-size M)
     ≤⟨ +-mono-≤ X ≤-refl ⟩
     8 + 8 * (ideal-size M)
     ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
     8 * suc (ideal-size M)
    ∎
    where
    X : 3 ≤ 8
    X = s≤s (s≤s (s≤s z≤n))
  nocast-size (snd M) (ncsnd mcM) =
    let IH = maybecast-size M mcM in
    begin
     1 + size M
     ≤⟨ s≤s IH ⟩
     3 + 8 * (ideal-size M)
     ≤⟨ +-mono-≤ X ≤-refl ⟩
     8 + 8 * (ideal-size M)
     ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
     8 * suc (ideal-size M)
    ∎
    where
    X : 3 ≤ 8
    X = s≤s (s≤s (s≤s z≤n))
  nocast-size (inl M) (ncinl mcM) =
    let IH = maybecast-size M mcM in
    begin
      1 + size M
      ≤⟨ s≤s IH ⟩
      3 + 8 * (ideal-size M)
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + 8 * (ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size M)
    ∎
    where
    X : 3 ≤ 8
    X = s≤s (s≤s (s≤s z≤n))
  nocast-size (inr M) (ncinr mcM) =
    let IH = maybecast-size M mcM in
    begin
      1 + size M
      ≤⟨ s≤s IH ⟩
      3 + 8 * (ideal-size M)
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + 8 * (ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size M)
    ∎
    where
    X : 3 ≤ 8
    X = s≤s (s≤s (s≤s z≤n))
  nocast-size (case L M N) (nccase mcL mcM mcN) =
    let IH1 = maybecast-size L mcL in
    let IH2 = maybecast-size M mcM in
    let IH3 = maybecast-size N mcN in
    begin
      1 + (size L + size M + size N)
      ≤⟨ s≤s (+-mono-≤ (+-mono-≤ IH1 IH2) IH3) ⟩
      1 + ((2 + 8 * ideal-size L) + (2 + 8 * ideal-size M) + (2 + 8 * ideal-size N))
      ≤⟨ ≤-reflexive (solve 3 (λ x y z → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y) :+ (con 2 :+ con 8 :* z)) := con 7 :+ con 8 :* (x :+ y :+ z)) refl (ideal-size L) (ideal-size M) (ideal-size N)) ⟩
      7 + 8 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ ≤-step ≤-refl ⟩
      8 + 8 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size L + ideal-size M + ideal-size N)
    ∎
    where open +-*-Solver
  nocast-size (blame ℓ) ncblame = s≤s z≤n
  maybecast-size M (notCast ncM) =
    let IH = nocast-size M ncM in ≤-step (≤-step IH)
  maybecast-size (M ⟨ c ⟩) (isCast ncM) =
    let IH = nocast-size M ncM in s≤s (≤-step IH)
  maybecast-size (M ⟨ c ⟩) (castVal mcM vM) =
    let IH = value-size M mcM vM in s≤s IH

-}
