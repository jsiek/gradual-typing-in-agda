module SimpleFunCast where

  open import Data.Nat
  open import Data.Bool
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
  import ParamCastReduction

  data Cast :  Type → Set where
    cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B)

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  data Inert : ∀{A} → Cast A → Set where
    inert-inj : ∀{A} → A ≢ ⋆ → (c : Cast (A ⇒ ⋆)) → Inert c
    inert-fun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Inert c
    inert-pair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Inert c
    inert-sum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Inert c

  data Active : ∀{A} → Cast A → Set where
    activeId : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    activeProj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert (cast .⋆ B ℓ {unk~L}) with eq-unk B
  ... | yes eqb rewrite eqb = inj₁ (activeId {⋆}{A-Unk} (cast ⋆ ⋆ ℓ))
  ... | no neqb = inj₁ (activeProj (cast ⋆ B ℓ) neqb)
  
  ActiveOrInert (cast A .⋆ ℓ {unk~R}) with eq-unk A
  ... | yes eqa rewrite eqa = inj₁ (activeId{⋆}{A-Unk} (cast ⋆ ⋆ ℓ))
  ... | no neqa = inj₂ (inert-inj neqa (cast A ⋆ ℓ))
  
  ActiveOrInert (cast (` ι) (` ι) ℓ {base~}) =
     inj₁ (activeId {` ι}{A-Base} (cast (` ι) (` ι) ℓ))
  ActiveOrInert (cast (A ⇒ B) (A' ⇒ B') ℓ {fun~ c c₁}) =
     inj₂ (inert-fun (cast (A ⇒ B) (A' ⇒ B') ℓ))
  ActiveOrInert (cast (A `× B) (A' `× B') ℓ {pair~ c c₁}) =
     inj₂ (inert-pair (cast (A `× B) (A' `× B') ℓ))
  ActiveOrInert (cast (A `⊎ B) (A' `⊎ B') ℓ {sum~ c c₁}) =
     inj₂ (inert-sum (cast (A `⊎ B) (A' `⊎ B') ℓ))

  funNotActive : ∀{A₁ A₂ B₁ B₂ ℓ c} → ¬ Active (cast (A₁ ⇒ A₂) (B₁ ⇒ B₂) ℓ {c})
  funNotActive (activeId {a = ()} .(cast (_ ⇒ _) (_ ⇒ _) _))


  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B C D} → (c : Cast ((A ⇒ B) ⇒ (C ⇒ D))) → Cross c
    C-pair : ∀{A B C D} → (c : Cast ((A `× B) ⇒ (C `× D))) → Cross c
    C-sum : ∀{A B C D} → (c : Cast ((A `⊎ B) ⇒ (C `⊎ D))) → Cross c
    
  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ (cast (A ⇒ B) (C ⇒ D) x) (inert-fun _) =
      ⟨ C-fun (cast (A ⇒ B) (C ⇒ D) x) , ⟨ A , ⟨ B , refl ⟩ ⟩ ⟩

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× (cast (A `× B) (C `× D) x) (inert-pair _) =
      ⟨ C-pair (cast (A `× B) (C `× D) x) , ⟨ A , ⟨ B , refl ⟩ ⟩ ⟩

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ (cast (A `⊎ B) (C `⊎ D) x) (inert-sum _) =
      ⟨ C-sum (cast (A `⊎ B) (C `⊎ D) x) , ⟨ A , ⟨ B , refl ⟩ ⟩ ⟩
  
  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
  dom (cast (A ⇒ B) (C ⇒ D) ℓ {cn}) (C-fun _)
      with ~-relevant cn
  ... | fun~ c d = cast C A ℓ {c}

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (cast (A ⇒ B) (C ⇒ D) ℓ {cn}) (C-fun _)
      with ~-relevant cn
  ... | fun~ c d = cast B D ℓ {d}

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (cast (A `× B) (C `× D) ℓ {cn}) (C-pair _)
      with ~-relevant cn
  ... | pair~ c d = cast A C ℓ {c}

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (cast (A `× B) (C `× D) ℓ {cn}) (C-pair _)
      with ~-relevant cn
  ... | pair~ c d = cast B D ℓ {d}
  
  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (cast (A `⊎ B) (C `⊎ D) ℓ {cn}) (C-sum _)
      with ~-relevant cn
  ... | sum~ c d = cast A C ℓ {c}

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (cast (A₁ `⊎ A₂) (A' `⊎ B') ℓ {cn}) (C-sum _)
      with ~-relevant cn
  ... | sum~ c d = cast A₂ B' ℓ {d}
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()
  
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
             }

  import ParamCastAux
  open ParamCastAux pcs

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
            → ∀ {a : Active c} → Γ ⊢ B
  applyCast {Γ}{A}{B} M v (cast .⋆ B ℓ {unk~L}) {a} with canonical⋆ M v
  ...  | ⟨ A' , ⟨ M' , ⟨ c , ⟨ _ , meq ⟩ ⟩ ⟩ ⟩ rewrite meq with A' `~ B
  ...    | yes ap-b = M' ⟨ cast A' B ℓ {ap-b} ⟩
  ...    | no ap-b = blame ℓ  
  applyCast M v (cast .⋆ ⋆ ℓ {unk~R}) {activeId .(cast ⋆ ⋆ ℓ)} = M
  applyCast M v (cast A ⋆ ℓ {unk~R}) {activeProj .(cast A ⋆ ℓ) x} =
     ⊥-elim (x refl)
  applyCast M v (cast (` ι) (` ι) ℓ {base~}) {a} = M
  
  applyCast{Γ} M v (cast (A₁ ⇒ A₂) (B₁ ⇒ B₂) ℓ {fun~ c c₁}) {a} =
     contradiction a funNotActive
  
  applyCast M v (cast (A₁ `× A₂) (B₁ `× B₂) ℓ {pair~ c c₁}) {a} =
    cons (fst M ⟨ cast A₁ B₁ ℓ {c} ⟩) (snd M ⟨ cast A₂ B₂ ℓ {c₁}⟩)
  
  applyCast M v (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ {sum~ c c₁}) {a} =
    let l = inl ((` Z) ⟨ cast A₁ B₁ ℓ {c}⟩) in
    let r = inr ((` Z) ⟨ cast A₂ B₂ ℓ {c₁}⟩) in
    case M (ƛ l) (ƛ r)

  open import CastStructure

  cs : CastStruct
  cs = record
             { precast = pcs
             ; applyCast = applyCast
             }

  import ParamCastReduction
  open ParamCastReduction cs public

  import GTLC2CC
  open GTLC2CC Cast (λ A B ℓ {c} → (cast A B ℓ {c})) public

