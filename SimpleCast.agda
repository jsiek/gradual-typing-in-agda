module SimpleCast where

  open import Data.Nat
  open import Data.Bool
  open import Data.Maybe
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)

  data Cast : Type → Set where
    _⇒⟨_⟩_ : (A : Type) → Label → (B : Type) → {c : A ~ B } → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  data Inert : ∀ {A} → Cast A → Set where
    inert : ∀{A} → A ≢ ⋆ → (c : Cast (A ⇒ ⋆)) → Inert c

  data Active : ∀ {A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c
    activeFun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Active c
    activePair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    activeSum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c    

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert ((.⋆ ⇒⟨ ℓ ⟩ B) {unk~L}) with eq-unk B
  ... | yes eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (⋆ ⇒⟨ ℓ ⟩ ⋆))
  ... | no neq = inj₁ (activeProj (⋆ ⇒⟨ ℓ ⟩ B) neq)
  ActiveOrInert ((A ⇒⟨ ℓ ⟩ .⋆) {unk~R}) with eq-unk A
  ... | yes eq rewrite eq = inj₁ (activeId{⋆}{A-Unk} (⋆ ⇒⟨ ℓ ⟩ ⋆))
  ... | no neq = inj₂ (inert neq (A ⇒⟨ ℓ ⟩ ⋆))
  ActiveOrInert (((` ι)  ⇒⟨ ℓ ⟩ (` ι)) {base~}) =
      inj₁ (activeId{` ι}{A-Base} ((` ι) ⇒⟨ ℓ ⟩ (` ι)))
  ActiveOrInert (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {fun~ c d}) =
      inj₁ (activeFun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)))
  ActiveOrInert (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)) {pair~ c d}) =
      inj₁ (activePair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))
  ActiveOrInert (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)) {sum~ c d}) =
      inj₁ (activeSum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B C D} → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D))) → Cross c
    C-pair : ∀{A B C D} → (c : Cast ((A `× B) ⇒ (C `× D))) → Cross c
    C-sum : ∀{A B C D} → (c : Cast ((A `⊎ B) ⇒ (C `⊎ D))) → Cross c
    
  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ c ()

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× c ()

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ c ()
  
  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
  dom (((A ⇒ B) ⇒⟨ ℓ ⟩ (C ⇒ D)){c}) x
      with ~-relevant c
  ... | fun~ c' d' = (C ⇒⟨ ℓ ⟩ A) {c = c'} 

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (((A ⇒ B) ⇒⟨ ℓ ⟩ (C ⇒ D)){c}) x
      with ~-relevant c
  ... | fun~ c' d' = (B ⇒⟨ ℓ ⟩ D) {c = d'}

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (((A `× B) ⇒⟨ ℓ ⟩ (C `× D)){c}) x
      with ~-relevant c
  ... | pair~ c' d' = (A ⇒⟨ ℓ ⟩ C){c'} 

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (((A `× B) ⇒⟨ ℓ ⟩ (C `× D)){c}) x
      with ~-relevant c
  ... | pair~ c' d' = (B ⇒⟨ ℓ ⟩ D){d'} 

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (((A `⊎ B) ⇒⟨ ℓ ⟩ (C `⊎ D)){c}) x
      with ~-relevant c
  ... | sum~ c' d' = (A ⇒⟨ ℓ ⟩ C){c'} 

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (((A `⊎ B) ⇒⟨ ℓ ⟩ (C `⊎ D)){c}) x
      with ~-relevant c
  ... | sum~ c' d' = (B ⇒⟨ ℓ ⟩ D){d'}
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  labC : ∀ {A} → (c : Cast A) → Maybe Label
  labC (A ⇒⟨ ℓ ⟩ B) = just ℓ

  open import Subtyping using (_<:₁_)
  open _<:₁_

  infix 5 _<:_
  _<:_ = _<:₁_

  data Safe : ∀ {A} → Cast A → Set where

    safe-<: : ∀ {S T} {c : Cast (S ⇒ T)}
      → S <: T
        --------
      → Safe c

  domSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} → Safe c → (x : Cross c)
          → Safe (dom c x)
  domSafe (safe-<: (<:-⇒ sub-dom sub-cod)) x = safe-<: sub-dom

  codSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))} → Safe c → (x : Cross c)
          → Safe (cod c x)
  codSafe (safe-<: (<:-⇒ sub-dom sub-cod)) x = safe-<: sub-cod

  domLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))) → (x : Cross c)
           → labC c ≡ labC (dom c x)
  domLabEq (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {c~}) x with ~-relevant c~
  ... | fun~ dom~ cod~ = refl

  codLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ ⇒ S₂) ⇒ (T₁ ⇒ T₂))) → (x : Cross c)
           → labC c ≡ labC (cod c x)
  codLabEq (((S₁ ⇒ S₂) ⇒⟨ ℓ ⟩ (T₁ ⇒ T₂)) {c~}) x with ~-relevant c~
  ... | fun~ dom~ cod~ = refl

  open import PreCastStructure
  
  pcs : PreCastStruct
  pcs = record
             { Cast = Cast
             ; Inert = Inert
             ; Active = Active
             ; ActiveOrInert = ActiveOrInert
             ; Cross = Cross
             ; Inert-Cross⇒ = Inert-Cross⇒
             ; Inert-Cross× = Inert-Cross×
             ; Inert-Cross⊎ = Inert-Cross⊎
             ; dom = dom
             ; cod = cod
             ; fstC = fstC
             ; sndC = sndC
             ; inlC = inlC
             ; inrC = inrC
             ; baseNotInert = baseNotInert
             ; labC = labC
             ; Safe = Safe
             ; domSafe = domSafe
             ; codSafe = codSafe
             ; domLabEq = domLabEq
             ; codLabEq = codLabEq
             }

  import ParamCastAux
  open ParamCastAux pcs

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  {- Id -}
  applyCast {Γ} {A} {.A} M v ((A ⇒⟨ ℓ ⟩ .A) {c}) {activeId .(A ⇒⟨ ℓ ⟩ A)} = M
  {- Collapse and Conflict -}
  applyCast {Γ} {.⋆} {B} M v ((.⋆ ⇒⟨ ℓ ⟩ B) {c}) {activeProj .(⋆ ⇒⟨ ℓ ⟩ B) x}
         with canonical⋆ M v
  ...  | ⟨ A' , ⟨ M' , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | yes ap-b = M' ⟨ (A' ⇒⟨ ℓ ⟩ B) {ap-b} ⟩
  ...    | no ap-b = blame ℓ  
  {- Wrap -}
  applyCast {Γ} {A₁ ⇒ A₂} {B₁ ⇒ B₂} M v ((.(_ ⇒ _) ⇒⟨ ℓ ⟩ .(_ ⇒ _)) {c})
      {activeFun .((_ ⇒ _) ⇒⟨ ℓ ⟩ (_ ⇒ _))} =
      eta⇒ M (((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)) {c})
          (C-fun ((A₁ ⇒ A₂) ⇒⟨ ℓ ⟩ (B₁ ⇒ B₂)))
  {- Cast Pair -}                   
  applyCast{Γ}{A₁ `× A₂}{B₁ `× B₂}M v ((_ ⇒⟨ ℓ ⟩ _){c}){activePair(_ ⇒⟨ ℓ ⟩ _)} =
       eta× M (((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)){c})
          (C-pair ((A₁ `× A₂) ⇒⟨ ℓ ⟩ (B₁ `× B₂)))

  {- Cast Sum -}
  applyCast{Γ}{A₁ `⊎ A₂}{B₁ `⊎ B₂}M v((_ ⇒⟨ ℓ ⟩ _){c}){activeSum .(_ ⇒⟨ ℓ ⟩ _)} =
     eta⊎ M (((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)){c})
       (C-sum ((A₁ `⊎ A₂) ⇒⟨ ℓ ⟩ (B₁ `⊎ B₂)))


     
  open import CastStructure

  cs : CastStruct
  cs = record
             { precast = pcs
             ; applyCast = applyCast
             }

  import ParamCastReduction
  open ParamCastReduction cs public

  import GTLC2CC
  open GTLC2CC Cast (λ A B ℓ {c} → (A ⇒⟨ ℓ ⟩ B) {c}) public

