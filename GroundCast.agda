{-

  This module formalizes the λB calculus (Siek, Thiemann, Wadler
  2015), aka. the blame calculus without predicate types, and proves
  type safety via progress and preservation.  

  This module is relatively small because it reuses the definitions
  and proofs from the Parameterized Cast Calculus. This module just
  has to provide the appropriate parameters.

-}

module GroundCast where

  open import Data.Nat
  open import Data.Bool
  open import Types
  open import PreCastStructure
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to [_,_])
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)

  {-

   The λB calculus represents a cast as a pair of types, the source and target,
   and a blame label. The two types must be consistent.

   -}

  data Cast : Type → Set where
    cast : (A : Type) → (B : Type) → Label → .(A ~ B) → Cast (A ⇒ B)

  import ParamCastCalculus
  open ParamCastCalculus Cast public

  import GTLC2CC
  open GTLC2CC Cast (λ A B ℓ {c} → cast A B ℓ c) public
  
  {-

  We categorize casts into the inert ones (that form values) and
  the active ones (that reduce).  

  For λB, there are two kinds of inert casts, those from a ground
  type to ⋆ and those between two function types.

n  -}

  data Inert : ∀ {A} → Cast A → Set where
    I-inj : ∀{A} → Ground A → (c : Cast (A ⇒ ⋆)) → Inert c
    I-fun : ∀{A B A' B'} → (c : Cast ((A ⇒ B) ⇒ (A' ⇒ B'))) → Inert c

  {-

  The rest of the casts are active casts, which we further subdivide
  according to which reduction rule is applicable. We have the
  identity casts, the injections from non-ground types, the casts
  between pair types, and the casts between sum types.

  -}

  data Active : ∀ {A} → Cast A → Set where
    A-id : ∀{A} → {a : Atomic A} → (c : Cast (A ⇒ A)) → Active c
    A-inj : ∀{A} → (c : Cast (A ⇒ ⋆)) → ¬ Ground A → A ≢ ⋆ → Active c
    A-proj : ∀{B} → (c : Cast (⋆ ⇒ B)) → B ≢ ⋆ → Active c
    A-pair : ∀{A B A' B'} → (c : Cast ((A `× B) ⇒ (A' `× B'))) → Active c
    A-sum : ∀{A B A' B'} → (c : Cast ((A `⊎ B) ⇒ (A' `⊎ B'))) → Active c    

  {-

   To show that every cast is either active or inert, we
   consider all the cases between two consistent types.

   -}

  base-consis-eq : ∀ {ι ι' : Base} → .(` ι ~ ` ι') → ι ≡ ι'
  base-consis-eq {Nat} {Nat} c = refl
  base-consis-eq {Int} {Int} c = refl
  base-consis-eq {𝔹} {𝔹} c = refl
  base-consis-eq {Unit} {Unit} c = refl
  base-consis-eq {Base.⊥} {Base.⊥} c = refl

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert {.(⋆ ⇒ ⋆)} (cast ⋆ ⋆ ℓ A~B) = inj₁ (A-id {a = A-Unk} (cast ⋆ ⋆ ℓ A~B))
  ActiveOrInert {.(⋆ ⇒ ` ι)} (cast ⋆ (` ι) ℓ A~B) = inj₁ (A-proj (cast ⋆ (` ι) ℓ A~B) (λ ()))
  ActiveOrInert {.(⋆ ⇒ (B ⇒ B₁))} (cast ⋆ (B ⇒ B₁) ℓ A~B) = inj₁ (A-proj (cast ⋆ (B ⇒ B₁) ℓ A~B) (λ ()))
  ActiveOrInert {.(⋆ ⇒ B `× B₁)} (cast ⋆ (B `× B₁) ℓ A~B) = inj₁ (A-proj (cast ⋆ (B `× B₁) ℓ A~B) (λ ()))
  ActiveOrInert {.(⋆ ⇒ B `⊎ B₁)} (cast ⋆ (B `⊎ B₁) ℓ A~B) = inj₁ (A-proj (cast ⋆ (B `⊎ B₁) ℓ A~B) (λ ()))
  ActiveOrInert {.(` ι ⇒ ⋆)} (cast (` ι) ⋆ ℓ A~B) = inj₂ (I-inj G-Base (cast (` ι) ⋆ ℓ A~B))
  ActiveOrInert {.(` ι ⇒ ` ι')} (cast (` ι) (` ι') ℓ A~B)
      with base-consis-eq A~B
  ... | refl = inj₁ (A-id {a = A-Base} (cast (` ι) (` ι) ℓ A~B))
  ActiveOrInert {.((A ⇒ A₁) ⇒ ⋆)} (cast (A ⇒ A₁) ⋆ ℓ A~B)
      with ground? (A ⇒ A₁)
  ... | yes g = inj₂ (I-inj g (cast (A ⇒ A₁) ⋆ ℓ A~B))
  ... | no ng = inj₁ (A-inj (cast (A ⇒ A₁) ⋆ ℓ A~B) ng (λ ()))
  ActiveOrInert {.((A ⇒ A₁) ⇒ (B ⇒ B₁))} (cast (A ⇒ A₁) (B ⇒ B₁) ℓ A~B) = inj₂ (I-fun (cast (A ⇒ A₁) (B ⇒ B₁) ℓ A~B))
  ActiveOrInert {.(A `× A₁ ⇒ ⋆)} (cast (A `× A₁) ⋆ ℓ A~B)
      with ground? (A `× A₁)
  ... | yes g = inj₂ (I-inj g (cast (A `× A₁) ⋆ ℓ A~B))
  ... | no ng = inj₁ (A-inj (cast (A `× A₁) ⋆ ℓ A~B) ng (λ ()))
  ActiveOrInert {.(A `× A₁ ⇒ B `× B₁)} (cast (A `× A₁) (B `× B₁) ℓ A~B) = inj₁ (A-pair (cast (A `× A₁) (B `× B₁) ℓ A~B))
  ActiveOrInert {.(A `⊎ A₁ ⇒ ⋆)} (cast (A `⊎ A₁) ⋆ ℓ A~B)
      with ground? (A `⊎ A₁)
  ... | yes g = inj₂ (I-inj g (cast (A `⊎ A₁) ⋆ ℓ A~B))
  ... | no ng = inj₁ (A-inj (cast (A `⊎ A₁) ⋆ ℓ A~B) ng (λ ()))
  ActiveOrInert {.(A `⊎ A₁ ⇒ B `⊎ B₁)} (cast (A `⊎ A₁) (B `⊎ B₁) ℓ A~B) = inj₁ (A-sum (cast (A `⊎ A₁) (B `⊎ B₁) ℓ A~B))

  data Cross : ∀ {A} → Cast A → Set where
    C-fun : ∀{A B A' B' ℓ} .{cn} → Cross (cast (A ⇒ B) (A' ⇒ B') ℓ cn)
    C-pair : ∀{A B A' B' ℓ} .{cn} → Cross (cast (A `× B) (A' `× B') ℓ cn)
    C-sum : ∀{A B A' B' ℓ} .{cn} → Cross (cast (A `⊎ B) (A' `⊎ B') ℓ cn)

  Inert-Cross⇒ : ∀{A C D} → (c : Cast (A ⇒ (C ⇒ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
  Inert-Cross⇒ (cast (A ⇒ B) (C ⇒ D) ℓ cn) (I-fun _) =
      [ C-fun , [ A , [ B , refl ] ] ]

  Inert-Cross× : ∀{A C D} → (c : Cast (A ⇒ (C `× D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `× A₂
  Inert-Cross× (cast A .(_ `× _) x x₁) ()

  Inert-Cross⊎ : ∀{A C D} → (c : Cast (A ⇒ (C `⊎ D))) → (i : Inert c)
              → Cross c × Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ `⊎ A₂
  Inert-Cross⊎ (cast A .(_ `⊎ _) x x₁) ()

  dom : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         → Cast (A' ⇒ A₁)
  dom (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ c) i =
      cast A' A₁ ℓ (Sym~ (~⇒L c))

  cod : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ ⇒ A₂) ⇒ (A' ⇒ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  cod (cast (A₁ ⇒ A₂) (A' ⇒ B') ℓ c) i =
      cast A₂ B' ℓ (~⇒R c)

  fstC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         → Cast (A₁ ⇒ A')
  fstC (cast (A `× B) (C `× D) ℓ cn) i = cast A C ℓ (~×L cn)

  sndC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `× A₂) ⇒ (A' `× B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  sndC (cast (A `× B) (C `× D) ℓ cn) i = cast B D ℓ (~×R cn)

  inlC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         → Cast (A₁ ⇒ A')
  inlC (cast (A `⊎ B) (C `⊎ D) ℓ cn) i = cast A C ℓ (~⊎L cn)

  inrC : ∀{A₁ A₂ A' B'} → (c : Cast ((A₁ `⊎ A₂) ⇒ (A' `⊎ B'))) → Cross c
         →  Cast (A₂ ⇒ B')
  inrC (cast (A `⊎ B) (C `⊎ D) ℓ cn) i = cast B D ℓ (~⊎R cn)

  {-
  Finally, we show that casts to base type are not inert.
  -}
  
  baseNotInert : ∀ {A ι} → (c : Cast (A ⇒ ` ι)) → ¬ Inert c
  baseNotInert c ()

  {-

   We take the first step of instantiating the reduction semantics of
   the Parametric Cast Calculus by applying the ParamCastAux module.

   -}
   
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

  inert-ground : ∀{A} → (c : Cast (A ⇒ ⋆)) → Inert c → Ground A
  inert-ground c (I-inj g .c) = g

  {-

   To instantiate the ParamCastReduction module, we must provide
   several operations, the first of which is applyCast. This handles
   applying an active cast to a value. We comment each case with the
   reduction rule from Siek, Thiemann, and Wadler (2015). The
   definition of applyCast is driven by pattern matching on the
   parameter {a : Active c}.

   -}

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B))
     → ∀ {a : Active c} → Γ ⊢ B
  {-
    V : ι ⇒ ι   —→   V 
   -}
  applyCast M v c {A-id c} = M
  {-
    V : A ⇒ ⋆   —→   V : A ⇒ G ⇒ ⋆
   -}
  applyCast M v (cast A ⋆ ℓ cn) {A-inj c a-ng a-nd}
      with ground A {a-nd}
  ... | [ G , cns ] = (M ⟨ cast A G ℓ (proj₂ cns) ⟩) ⟨ cast G ⋆ ℓ unk~R ⟩
  {-
    V : G ⇒p ⋆ ⇒q G  —→   V
    V : G ⇒p ⋆ ⇒q H  —→   blame q
   -}
  applyCast M v (cast ⋆ B ℓ cn) {A-proj c b-nd}
      with ground? B
  ... | yes b-g
          with canonical⋆ M v
  ...     | [ G , [ V , [ c' , [ i , meq ] ] ] ] rewrite meq
              with gnd-eq? G B {inert-ground c' i} {b-g}
  ...         | yes ap-b rewrite ap-b = V
  ...         | no ap-b = blame ℓ
  {-
    V : ⋆ ⇒ B   —→   V : ⋆ ⇒ H ⇒ B
   -}
  applyCast M v (cast ⋆ B ℓ cn) {A-proj c b-nd}
      | no b-ng with ground B {b-nd}
  ...    | [ H , [ h-g , cns ] ] =
           (M ⟨ cast ⋆ H ℓ unk~L ⟩) ⟨ cast H B ℓ (Sym~ cns) ⟩
  
  applyCast M v (cast (A₁ `× A₂) (B₁ `× B₂) ℓ c) {A-pair _} =
    cons (fst M ⟨ cast A₁ B₁ ℓ (~×L c) ⟩) (snd M ⟨ cast A₂ B₂ ℓ (~×R c) ⟩)
    
  applyCast M v (cast (A₁ `⊎ A₂) (B₁ `⊎ B₂) ℓ c) {A-sum _} =
    let l = inl ((` Z) ⟨ cast A₁ B₁ ℓ (~⊎L c) ⟩) in
    let r = inr ((` Z) ⟨ cast A₂ B₂ ℓ (~⊎R c) ⟩) in
    case M (ƛ l) (ƛ r)

  open import CastStructure

  cs : CastStruct
  cs = record
             { precast = pcs
             ; applyCast = applyCast
             }

  {-

  We now instantiate the module ParamCastReduction, thereby proving
  type safety for λB.

  -}

  import ParamCastReduction
  module Red = ParamCastReduction cs
  open Red

