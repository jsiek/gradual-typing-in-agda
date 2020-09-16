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

  fstSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} → Safe c → (x : Cross c)
          → Safe (fstC c x)
  fstSafe (safe-<: (<:-× sub-fst sub-snd)) x = safe-<: sub-fst

  sndSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))} → Safe c → (x : Cross c)
          → Safe (sndC c x)
  sndSafe (safe-<: (<:-× sub-fst sub-snd)) x = safe-<: sub-snd

  fstLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))) → (x : Cross c)
           → labC c ≡ labC (fstC c x)
  fstLabEq (((S₁ `× S₂) ⇒⟨ ℓ ⟩ (T₁ `× T₂)) {c~}) x with ~-relevant c~
  ... | pair~ fst~ snd~ = refl

  sndLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ `× S₂) ⇒ (T₁ `× T₂))) → (x : Cross c)
           → labC c ≡ labC (sndC c x)
  sndLabEq (((S₁ `× S₂) ⇒⟨ ℓ ⟩ (T₁ `× T₂)) {c~}) x with ~-relevant c~
  ... | pair~ fst~ snd~ = refl

  inlSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} → Safe c → (x : Cross c)
          → Safe (inlC c x)
  inlSafe (safe-<: (<:-⊎ sub-l sub-r)) x = safe-<: sub-l

  inrSafe : ∀ {S₁ S₂ T₁ T₂} {c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))} → Safe c → (x : Cross c)
          → Safe (inrC c x)
  inrSafe (safe-<: (<:-⊎ sub-l sub-r)) x = safe-<: sub-r

  inlLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))) → (x : Cross c)
           → labC c ≡ labC (inlC c x)
  inlLabEq (((S₁ `⊎ S₂) ⇒⟨ ℓ ⟩ (T₁ `⊎ T₂)) {c~}) x with ~-relevant c~
  ... | sum~ l~ r~ = refl

  inrLabEq : ∀ {S₁ S₂ T₁ T₂} → (c : Cast ((S₁ `⊎ S₂) ⇒ (T₁ `⊎ T₂))) → (x : Cross c)
           → labC c ≡ labC (inrC c x)
  inrLabEq (((S₁ `⊎ S₂) ⇒⟨ ℓ ⟩ (T₁ `⊎ T₂)) {c~}) x with ~-relevant c~
  ... | sum~ l~ r~ = refl

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
             ; fstSafe = fstSafe
             ; sndSafe = sndSafe
             ; fstLabEq = fstLabEq
             ; sndLabEq = sndLabEq
             ; inlSafe = inlSafe
             ; inrSafe = inrSafe
             ; inlLabEq = inlLabEq
             ; inrLabEq = inrLabEq
             }

  import ParamCastAux
  open ParamCastAux pcs
  open import ParamCastSubtyping pcs

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

  applyCast-pres-allsafe-same-ℓ : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → labC c ≡ just ℓ
    → Safe c
    → CastsAllSafe V ℓ
      --------------------------------------
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe-same-ℓ (activeId (A ⇒⟨ x ⟩ .A)) eq safe allsafe = allsafe
  applyCast-pres-allsafe-same-ℓ {vV = vV} (activeProj (⋆ ⇒⟨ ℓ ⟩ B) x) refl (safe-<: T<:⋆) allsafe with canonical⋆ _ vV
  ... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A′ `~ B
  ...   | no _ = allsafe-blame-diff-ℓ (λ _ → x refl)
  ...   | yes _ with allsafe
  ...     | allsafe-cast-same-ℓ _ _ allsafe-M′ = allsafe-cast-same-ℓ (safe-<: T<:⋆) refl allsafe-M′
  ...     | allsafe-cast-diff-ℓ _ allsafe-M′ = allsafe-cast-same-ℓ (safe-<: T<:⋆) refl allsafe-M′
  applyCast-pres-allsafe-same-ℓ (activeFun ((.(_ ⇒ _) ⇒⟨ ℓ ⟩ .(_ ⇒ _)) {c~})) refl (safe-<: (<:-⇒ sub-dom sub-cod)) allsafe
    with ~-relevant c~
  ... | fun~ _ _ =
      allsafe-ƛ (allsafe-cast-same-ℓ (safe-<: sub-cod) refl (allsafe-· (rename-pres-allsafe S_ allsafe)
                                                                       (allsafe-cast-same-ℓ (safe-<: sub-dom) refl allsafe-var)))
  applyCast-pres-allsafe-same-ℓ (activePair ((.(_ `× _) ⇒⟨ ℓ ⟩ .(_ `× _)) {c~})) refl (safe-<: (<:-× sub-fst sub-snd)) allsafe
    with ~-relevant c~
  ... | pair~ _ _ = allsafe-cons (allsafe-cast-same-ℓ (safe-<: sub-fst) refl (allsafe-fst allsafe))
                                 (allsafe-cast-same-ℓ (safe-<: sub-snd) refl (allsafe-snd allsafe))
  applyCast-pres-allsafe-same-ℓ (activeSum ((.(_ `⊎ _) ⇒⟨ ℓ ⟩ .(_ `⊎ _)) {c~})) refl (safe-<: (<:-⊎ sub-l sub-r)) allsafe
    with ~-relevant c~
  ... | sum~ _ _ = allsafe-case allsafe (allsafe-ƛ (allsafe-inl (allsafe-cast-same-ℓ (safe-<: sub-l) refl allsafe-var)))
                                        (allsafe-ƛ (allsafe-inr (allsafe-cast-same-ℓ (safe-<: sub-r) refl allsafe-var)))

  applyCast-pres-allsafe-diff-ℓ : ∀ {Γ A B} {V : Γ ⊢ A} {vV : Value V} {c : Cast (A ⇒ B)} {ℓ}
    → (a : Active c)
    → labC c ≢ just ℓ
    → CastsAllSafe V ℓ
      --------------------------------------
    → CastsAllSafe (applyCast V vV c {a}) ℓ
  applyCast-pres-allsafe-diff-ℓ (activeId (A ⇒⟨ x ⟩ .A)) neq allsafe = allsafe
  applyCast-pres-allsafe-diff-ℓ {vV = vV} (activeProj (⋆ ⇒⟨ ℓ ⟩ B) x) neq allsafe with canonical⋆ _ vV
  ... | ⟨ A′ , ⟨ M′ , ⟨ _ , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A′ `~ B
  ...   | no _ = allsafe-blame-diff-ℓ λ ℓ′≡ℓ → neq (cong (λ □ → just □) (sym ℓ′≡ℓ))
  ...   | yes _ with allsafe
  ...     | allsafe-cast-same-ℓ _ _ allsafe-M′ = allsafe-cast-diff-ℓ neq allsafe-M′
  ...     | allsafe-cast-diff-ℓ _ allsafe-M′ = allsafe-cast-diff-ℓ neq allsafe-M′
  applyCast-pres-allsafe-diff-ℓ (activeFun ((.(_ ⇒ _) ⇒⟨ ℓ ⟩ .(_ ⇒ _)) {c~})) neq allsafe
    with ~-relevant c~
  ... | fun~ _ _ =
      allsafe-ƛ (allsafe-cast-diff-ℓ neq (allsafe-· (rename-pres-allsafe S_ allsafe)
                                         (allsafe-cast-diff-ℓ neq allsafe-var)))
  applyCast-pres-allsafe-diff-ℓ (activePair ((.(_ `× _) ⇒⟨ ℓ ⟩ .(_ `× _)) {c~})) neq allsafe
    with ~-relevant c~
  ... | pair~ _ _ = allsafe-cons (allsafe-cast-diff-ℓ neq (allsafe-fst allsafe))
                                 (allsafe-cast-diff-ℓ neq (allsafe-snd allsafe))
  applyCast-pres-allsafe-diff-ℓ (activeSum ((.(_ `⊎ _) ⇒⟨ ℓ ⟩ .(_ `⊎ _)) {c~})) neq allsafe
    with ~-relevant c~
  ... | sum~ _ _ = allsafe-case allsafe (allsafe-ƛ (allsafe-inl (allsafe-cast-diff-ℓ neq allsafe-var)))
                                        (allsafe-ƛ (allsafe-inr (allsafe-cast-diff-ℓ neq allsafe-var)))


     
  open import CastStructure

  cs : CastStruct
  cs = record
             { precast = pcs
             ; applyCast = applyCast
             ; applyCast-pres-allsafe-same-ℓ = applyCast-pres-allsafe-same-ℓ
             ; applyCast-pres-allsafe-diff-ℓ = applyCast-pres-allsafe-diff-ℓ
             }

  import ParamCastReduction
  open ParamCastReduction cs public

  import GTLC2CC
  open GTLC2CC Cast (λ A B ℓ {c} → (A ⇒⟨ ℓ ⟩ B) {c}) public

  -- Instantiate blame-subtyping theorem for `SimpleCast`.
  open import ParamBlameSubtyping cs using (soundness-<:) public
