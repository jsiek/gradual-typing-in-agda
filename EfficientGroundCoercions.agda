module EfficientGroundCoercions where

  open import Agda.Primitive
  open import Data.Nat
  open import Data.Nat.Properties
  open ≤-Reasoning {- renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_) -}
  open import Types
  open import Variables
  open import Labels
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  
  data IntermediateCast : Type → Set
  data GroundCast : Type → Set
  data Cast : Type → Set
  
  data Cast where
    id⋆ : Cast (⋆ ⇒ ⋆)
    proj : ∀{B}
       → (G : Type) → Label → IntermediateCast (G ⇒ B) → {g : Ground G}
       → Cast (⋆ ⇒ B)
    intmd : ∀{A B}
       → IntermediateCast (A ⇒ B)
       → Cast (A ⇒ B)

  data IntermediateCast where
    inj : ∀{A}
       → (G : Type)
       → GroundCast (A ⇒ G)
       → {g : Ground G}
       → IntermediateCast (A ⇒ ⋆)
    gnd : ∀{A B}
       → (g : GroundCast (A ⇒ B))
       → IntermediateCast (A ⇒ B)
    cfail : ∀{A B} (G : Type) → (H : Type) → Label
       → IntermediateCast (A ⇒ B)

  data GroundCast where
    cid : ∀ {A : Type} {a : Base A} → GroundCast (A ⇒ A)
    cfun : ∀ {A B A' B'}
      → (c : Cast (B ⇒ A)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → GroundCast ((A ⇒ A') ⇒ (B ⇒ B'))
    cpair : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → GroundCast ((A `× A') ⇒ (B `× B'))
    csum : ∀ {A B A' B'}
      → (c : Cast (A ⇒ B)) → (d : Cast (A' ⇒ B'))
        -----------------------------------------
      → GroundCast ((A `⊎ A') ⇒ (B `⊎ B'))

  size-gnd : ∀{A} → GroundCast A → ℕ
  size-intmd : ∀{A} → IntermediateCast A → ℕ  
  size-cast : ∀{A} → Cast A → ℕ  

  size-gnd cid = 1
  size-gnd (cfun c d) = 1 + size-cast c + size-cast d
  size-gnd (cpair c d) = 1 + size-cast c + size-cast d
  size-gnd (csum c d) =  1 + size-cast c + size-cast d

  size-intmd (inj G g) = 1 + size-gnd g
  size-intmd (gnd g) = 1 + size-gnd g
  size-intmd (cfail G H ℓ) = 1
  
  size-cast id⋆ = 1
  size-cast (proj G ℓ i) = 1 + size-intmd i
  size-cast (intmd i) = 1 + size-intmd i

  size-gnd-pos : ∀{A c} → size-gnd {A} c ≢ zero
  size-gnd-pos {.(_ ⇒ _)} {cid} = λ ()
  size-gnd-pos {.((_ ⇒ _) ⇒ (_ ⇒ _))} {cfun c d} = λ ()
  size-gnd-pos {.(_ `× _ ⇒ _ `× _)} {cpair c d} = λ ()
  size-gnd-pos {.(_ `⊎ _ ⇒ _ `⊎ _)} {csum c d} = λ ()

  size-intmd-pos : ∀{A c} → size-intmd {A} c ≢ zero
  size-intmd-pos {.(_ ⇒ ⋆)} {inj G x} = λ ()
  size-intmd-pos {.(_ ⇒ _)} {gnd g} = λ ()
  size-intmd-pos {.(_ ⇒ _)} {cfail G H x} = λ ()

  size-cast-pos : ∀{A c} → size-cast {A} c ≢ zero
  size-cast-pos {.(⋆ ⇒ ⋆)} {id⋆} = λ ()
  size-cast-pos {.(⋆ ⇒ _)} {proj G x x₁} = λ ()
  size-cast-pos {.(_ ⇒ _)} {intmd x} = λ ()

  plus-zero1 : ∀{a}{b} → a + b ≡ zero → a ≡ zero
  plus-zero1 {zero} {b} p = refl
  plus-zero1 {suc a} {b} ()

  plus-zero2 : ∀{a}{b} → a + b ≡ zero → b ≡ zero
  plus-zero2 {zero} {b} p = p
  plus-zero2 {suc a} {b} ()

  plus-gnd-pos : ∀{A}{B}{c}{d} → size-gnd{A} c + size-gnd{B} d ≤ zero → ⊥
  plus-gnd-pos {A}{B}{c}{d} p =
     let cd-z = n≤0⇒n≡0 p in
     let c-z = plus-zero1 {size-gnd c}{size-gnd d} cd-z in
     contradiction c-z (size-gnd-pos{A}{c})

  plus-intmd-pos : ∀{A}{B}{c}{d} → size-intmd{A} c + size-intmd{B} d ≤ zero → ⊥
  plus-intmd-pos {A}{B}{c}{d} p =
     let cd-z = n≤0⇒n≡0 p in
     let c-z = plus-zero1 {size-intmd c}{size-intmd d} cd-z in
     contradiction c-z (size-intmd-pos{A}{c})

  plus-cast-pos : ∀{A}{B}{c}{d} → size-cast{A} c + size-cast{B} d ≤ zero → ⊥
  plus-cast-pos {A}{B}{c}{d} p =
     let cd-z = n≤0⇒n≡0 p in
     let c-z = plus-zero1 {size-cast c}{size-cast d} cd-z in
     contradiction c-z (size-cast-pos{A}{c})

  import ParamCastCalculus
  module CastCalc = ParamCastCalculus Cast
  open CastCalc

  coerce-to-gnd : (A : Type) → (B : Type) → {g : Ground B}
     → ∀ {c : A ~ B}{a : A ≢ ⋆} → Label → GroundCast (A ⇒ B)
  coerce-from-gnd : (A : Type) → (B : Type) → {g : Ground A}
     → ∀ {c : A ~ B}{b : B ≢ ⋆} → Label → GroundCast (A ⇒ B)

  coerce-gnd-to⋆ : (A : Type) → {g : Ground A} → Label → Cast (A ⇒ ⋆)
  coerce-gnd-to⋆ .Nat {G-Base B-Nat} ℓ = intmd (inj Nat (cid{Nat}{B-Nat}) {G-Base B-Nat})
  coerce-gnd-to⋆ .𝔹 {G-Base B-Bool} ℓ = intmd (inj 𝔹 (cid{𝔹}{B-Bool}) {G-Base B-Bool})
  coerce-gnd-to⋆ .(⋆ ⇒ ⋆) {G-Fun} ℓ = intmd (inj (⋆ ⇒ ⋆) (cfun id⋆ id⋆) {G-Fun})
  coerce-gnd-to⋆ .(⋆ `× ⋆) {G-Pair} ℓ = intmd (inj (⋆ `× ⋆) (cpair id⋆ id⋆) {G-Pair})
  coerce-gnd-to⋆ .(⋆ `⊎ ⋆) {G-Sum} ℓ = intmd (inj  (⋆ `⊎ ⋆) (csum id⋆ id⋆) {G-Sum})

  coerce-gnd-from⋆ : (B : Type) → {g : Ground B} → Label → Cast (⋆ ⇒ B)
  coerce-gnd-from⋆ .Nat {G-Base B-Nat} ℓ = proj Nat ℓ (gnd (cid{Nat}{B-Nat})) {G-Base B-Nat}
  coerce-gnd-from⋆ .𝔹 {G-Base B-Bool} ℓ = proj 𝔹 ℓ (gnd (cid{𝔹}{B-Bool})) {G-Base B-Bool}
  coerce-gnd-from⋆ .(⋆ ⇒ ⋆) {G-Fun} ℓ = proj (⋆ ⇒ ⋆) ℓ (gnd (cfun id⋆ id⋆)) {G-Fun}
  coerce-gnd-from⋆ .(⋆ `× ⋆) {G-Pair} ℓ = proj (⋆ `× ⋆) ℓ (gnd (cpair id⋆ id⋆)) {G-Pair}
  coerce-gnd-from⋆ .(⋆ `⊎ ⋆) {G-Sum} ℓ = proj (⋆ `⊎ ⋆) ℓ (gnd (csum id⋆ id⋆)) {G-Sum}
  
  coerce-to⋆ : (A : Type) → Label → Cast (A ⇒ ⋆)
  coerce-to⋆ A ℓ with eq-unk A
  ... | inj₁ eq rewrite eq = id⋆ 
  ... | inj₂ neq with ground? A
  ...     | inj₁ g = coerce-gnd-to⋆ A {g} ℓ
  ...     | inj₂ ng with ground A {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ = intmd (inj G (coerce-to-gnd A G {g}{c}{neq} ℓ) {g})

  coerce-from⋆ : (B : Type) → Label → Cast (⋆ ⇒ B)
  coerce-from⋆ B ℓ with eq-unk B
  ... | inj₁ eq rewrite eq = id⋆
  ... | inj₂ neq with ground? B
  ...     | inj₁ g = coerce-gnd-from⋆ B {g} ℓ
  ...     | inj₂ ng with ground B {neq}
  ...        | ⟨ G , ⟨ g , c ⟩ ⟩ = proj G ℓ (gnd (coerce-from-gnd G B {g}{Sym~ c}{neq} ℓ)) {g} 

  coerce-to-gnd .⋆ .Nat {G-Base B-Nat} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd .Nat .Nat {G-Base B-Nat} {nat~} ℓ = cid{Nat}{B-Nat}
  coerce-to-gnd .⋆ .𝔹 {G-Base B-Bool} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd .𝔹 .𝔹 {G-Base B-Bool} {bool~} ℓ = cid{𝔹}{B-Bool}
  coerce-to-gnd .⋆ .(⋆ ⇒ ⋆) {G-Fun} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ ⇒ A₂) .(⋆ ⇒ ⋆) {G-Fun} {fun~ c c₁} ℓ =
     cfun (coerce-from⋆ A₁ ℓ) (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd .⋆ .(⋆ `× ⋆) {G-Pair} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ `× A₂) .(⋆ `× ⋆) {G-Pair} {pair~ c c₁} ℓ =
     cpair (coerce-to⋆ A₁ ℓ) (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd .⋆ .(⋆ `⊎ ⋆) {G-Sum} {unk~L}{neq} ℓ = ⊥-elim (neq refl)
  coerce-to-gnd (A₁ `⊎ A₂) .(⋆ `⊎ ⋆) {G-Sum} {sum~ c c₁} ℓ =
     csum (coerce-to⋆ A₁ ℓ) (coerce-to⋆ A₂ ℓ)

  coerce-from-gnd .Nat .⋆ {G-Base B-Nat} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .Nat .Nat {G-Base B-Nat} {nat~} ℓ = cid{Nat}{B-Nat}
  coerce-from-gnd .𝔹 .⋆ {G-Base B-Bool} {unk~R}{neq} ℓ =  ⊥-elim (neq refl)
  coerce-from-gnd .𝔹 .𝔹 {G-Base B-Bool} {bool~} ℓ = cid{𝔹}{B-Bool}
  coerce-from-gnd .(⋆ ⇒ ⋆) .⋆ {G-Fun} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .(⋆ ⇒ ⋆) (B₁ ⇒ B₂) {G-Fun} {fun~ c c₁} ℓ =
     cfun (coerce-to⋆ B₁ ℓ) (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd .(⋆ `× ⋆) .⋆ {G-Pair} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .(⋆ `× ⋆) (B₁ `× B₂) {G-Pair} {pair~ c c₁} ℓ =
     cpair (coerce-from⋆ B₁ ℓ) (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd .(⋆ `⊎ ⋆) .⋆ {G-Sum} {unk~R}{neq} ℓ = ⊥-elim (neq refl)
  coerce-from-gnd .(⋆ `⊎ ⋆) (B₁ `⊎ B₂) {G-Sum} {sum~ c c₁} ℓ =
     csum (coerce-from⋆ B₁ ℓ) (coerce-from⋆ B₂ ℓ)

  coerce : (A : Type) → (B : Type) → ∀ {c : A ~ B} → Label → Cast (A ⇒ B)
  coerce .⋆ B {unk~L} ℓ = coerce-from⋆ B ℓ
  coerce A .⋆ {unk~R} ℓ = coerce-to⋆ A ℓ
  coerce Nat Nat {nat~} ℓ = intmd (gnd (cid {Nat} {B-Nat}))
  coerce 𝔹 𝔹 {bool~} ℓ = intmd (gnd (cid {𝔹} {B-Bool}))
  coerce (A ⇒ B) (A' ⇒ B') {fun~ c c₁} ℓ =
    intmd (gnd (cfun (coerce A' A {Sym~ c} (flip ℓ) ) (coerce B B' {c₁} ℓ)))
  coerce (A `× B) (A' `× B') {pair~ c c₁} ℓ =
    intmd (gnd (cpair (coerce A A' {c} ℓ ) (coerce B B' {c₁} ℓ)))
  coerce (A `⊎ B) (A' `⊎ B') {sum~ c c₁} ℓ =
    intmd (gnd (csum (coerce A A' {c} ℓ ) (coerce B B' {c₁} ℓ)  ))

  data InertGround : ∀ {A} → GroundCast A → Set where
    I-cfun : ∀{A B A' B'}{s : Cast (B ⇒ A)} {t : Cast (A' ⇒ B')}
          → InertGround (cfun{A}{B}{A'}{B'} s t)

  data ActiveGround : ∀ {A} → GroundCast A → Set where
    A-cpair : ∀{A B A' B'}{s : Cast (A ⇒ B)} {t : Cast (A' ⇒ B')}
          → ActiveGround (cpair{A}{B}{A'}{B'} s t)
    A-csum : ∀{A B A' B'}{s : Cast (A ⇒ B)} {t : Cast (A' ⇒ B')}
          → ActiveGround (csum{A}{B}{A'}{B'} s t)
    A-cid : ∀{B b}
          → ActiveGround (cid {B}{b})

  data InertIntmd : ∀ {A} → IntermediateCast A → Set where
    I-inj : ∀{A G i}{g : GroundCast (A ⇒ G)}
          → InertIntmd (inj {A} G g {i})
    I-gnd : ∀{A B}{g : GroundCast (A ⇒ B)}
          → InertGround g
          → InertIntmd (gnd {A}{B} g)

  data ActiveIntmd : ∀ {A} → IntermediateCast A → Set where
    A-gnd : ∀{A B}{g : GroundCast (A ⇒ B)}
          → ActiveGround g
          → ActiveIntmd (gnd {A}{B} g)
    A-cfail : ∀{A B G H ℓ}
          → ActiveIntmd (cfail {A}{B} G H ℓ)
    
  data Inert : ∀ {A} → Cast A → Set where
    I-intmd : ∀{A B}{i : IntermediateCast (A ⇒ B)}
          → InertIntmd i
          → Inert (intmd{A}{B} i)

  data Active : ∀ {A} → Cast A → Set where
    A-id⋆ : Active id⋆
    A-proj : ∀{B G ℓ g} {i : IntermediateCast (G ⇒ B)}
          → Active (proj{B} G ℓ i {g})
    A-intmd : ∀{A B}{i : IntermediateCast (A ⇒ B)}
          → ActiveIntmd i
          → Active (intmd{A}{B} i)

  
  ActiveOrInertGnd : ∀{A} → (c : GroundCast A) → ActiveGround c ⊎ InertGround c
  ActiveOrInertGnd cid = inj₁ A-cid
  ActiveOrInertGnd (cfun c d) = inj₂ I-cfun
  ActiveOrInertGnd (cpair c d) = inj₁ A-cpair
  ActiveOrInertGnd (csum c d) = inj₁ A-csum

  ActiveOrInertIntmd : ∀{A} → (c : IntermediateCast A) → ActiveIntmd c ⊎ InertIntmd c
  ActiveOrInertIntmd (inj G x) = inj₂ I-inj
  ActiveOrInertIntmd (gnd g) with ActiveOrInertGnd g
  ... | inj₁ a = inj₁ (A-gnd a)
  ... | inj₂ i = inj₂ (I-gnd i)
  ActiveOrInertIntmd (cfail G H x) = inj₁ A-cfail

  ActiveOrInert : ∀{A} → (c : Cast A) → Active c ⊎ Inert c
  ActiveOrInert id⋆ = inj₁ A-id⋆
  ActiveOrInert (proj G x x₁) = inj₁ A-proj
  ActiveOrInert (intmd i) with ActiveOrInertIntmd i
  ... | inj₁ a = inj₁ (A-intmd a)
  ... | inj₂ j = inj₂ (I-intmd j)
  
  import EfficientParamCasts
  module PCR = EfficientParamCasts Cast Inert Active ActiveOrInert
  open PCR

  plus1-suc : ∀{n} → n + 1 ≡ suc n
  plus1-suc {zero} = refl
  plus1-suc {suc n} = cong suc plus1-suc

  {- 
    Ugh, the following reasoning is tedious! Is there a better way? -Jeremy
  -}

  metric3 : ∀{sc sd sc1 sd1 n}
       → sc + sd + suc (sc1 + sd1) ≤ n
       → sc + sc1 ≤ n
  metric3{sc}{sd}{sc1}{sd1}{n} m =
    begin sc + sc1
               ≤⟨ m≤m+n (sc + sc1) (sd + (sd1 + 1)) ⟩
          (sc + sc1) + (sd + (sd1 + 1))
               ≤⟨ ≤-reflexive (+-assoc (sc) (sc1) (sd + (sd1 + 1))) ⟩
          sc + (sc1 + (sd + (sd1 + 1)))
               ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc})
                              (sym (+-assoc (sc1) (sd) (sd1 + 1)))) ⟩
          sc + ((sc1 + sd) + (sd1 + 1))
               ≤⟨ ≤-reflexive (cong₂ (_+_) ((refl{x = sc}))
                                         (cong₂ (_+_) (+-comm (sc1) (sd)) refl)) ⟩
          sc + ((sd + sc1) + (sd1 + 1))
               ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc})
                                (+-assoc (sd) (sc1) (sd1 + 1))) ⟩
          sc + (sd + (sc1 + (sd1 + 1)))
               ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc})
                            (cong₂ (_+_) (refl{x = sd})
                                 (sym (+-assoc (sc1) (sd1) 1)))) ⟩
          sc + (sd + ((sc1 + sd1) + 1))
               ≤⟨ ≤-reflexive (sym (+-assoc (sc) (sd) (sc1 + sd1 + 1))) ⟩
          (sc + sd) + ((sc1 + sd1) + 1)
               ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc + sd}) plus1-suc) ⟩
          (sc + sd) + suc (sc1 + sd1)
               ≤⟨ m ⟩
          n
    ∎  

  metric1 : ∀{sc sd sc1 sd1 n}
       → sc + sd + suc (sc1 + sd1) ≤ n
       → sc1 + sc ≤ n
  metric1{sc}{sd}{sc1}{sd1}{n} m =
    begin sc1 + sc
               ≤⟨ ≤-reflexive (+-comm sc1 sc) ⟩
          sc + sc1
               ≤⟨ metric3{sc} m ⟩
          n
    ∎  

  metric2 : ∀{sc sd sc1 sd1 n}
       → sc + sd + suc (sc1 + sd1) ≤ n 
       → sd + sd1 ≤ n
  metric2{sc}{sd}{sc1}{sd1}{n} m =
    begin
      sd + sd1
           ≤⟨ m≤m+n (sd + sd1) (sc + (sc1 + 1)) ⟩
      (sd + sd1) + (sc + (sc1 + 1))
           ≤⟨ ≤-reflexive (+-assoc sd sd1 (sc + (sc1 + 1))) ⟩
      sd + (sd1 + (sc + (sc1 + 1)))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd}) (sym (+-assoc sd1 sc (sc1 + 1)))) ⟩
      sd + ((sd1 + sc) + (sc1 + 1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd})
                             (cong₂ (_+_) (+-comm sd1 sc) (refl{x = sc1 + 1}))) ⟩
      sd + ((sc + sd1) + (sc1 + 1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd}) (+-assoc sc sd1 (sc1 + 1))) ⟩
      sd + (sc + (sd1 + (sc1 + 1)))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd})
                 (cong₂ (_+_) (refl{x = sc}) (sym (+-assoc sd1 sc1 1)))) ⟩
      sd + (sc + ((sd1 + sc1) + 1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sd})
                 (cong₂ (_+_) (refl{x = sc}) plus1-suc)) ⟩
      sd + (sc + (suc (sd1 + sc1)))
           ≤⟨  ≤-reflexive (sym (+-assoc sd sc (suc (sd1 + sc1)))) ⟩
      (sd + sc) + (suc (sd1 + sc1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (+-comm sd sc) (refl{x = suc (sd1 + sc1)})) ⟩
      (sc + sd) + (suc (sd1 + sc1))
           ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = sc + sd}) (cong suc (+-comm sd1 sc1))) ⟩
      (sc + sd) + suc (sc1 + sd1)          
           ≤⟨ m ⟩
      n
    ∎  

  metric4 : ∀{g h n : ℕ}
     → g + suc h ≤ n
     → g + h ≤ n
  metric4{g}{h}{n} p =
    begin
       g + h
          ≤⟨ m≤m+n (g + h) 1 ⟩
       (g + h) + 1
          ≤⟨ ≤-reflexive (+-assoc g h 1) ⟩
       g + (h + 1)
          ≤⟨  ≤-reflexive (cong₂ (_+_) (refl{x = g}) plus1-suc) ⟩
       g + suc h
          ≤⟨ p ⟩
       n
    ∎  

  metric5 : ∀{x i n : ℕ}
     → suc (x + suc i) ≤ n
     → suc (x + i) ≤ n
  metric5{x}{i}{n} p =
    begin
      suc (x + i)
        ≤⟨ ≤-reflexive (sym plus1-suc) ⟩
      (x + i) + 1
        ≤⟨ ≤-reflexive (+-assoc x i 1) ⟩
      x + (i + 1)
        ≤⟨ ≤-reflexive (cong₂ (_+_) refl plus1-suc) ⟩
      x + (suc i)
        ≤⟨ n≤1+n (x + suc i) ⟩
      suc (x + (suc i))
        ≤⟨ p ⟩
      n
    ∎  

  metric6 : ∀{x₁ x₂ n : ℕ}
     → x₁ + suc x₂ ≤ n
     → x₁ + x₂ ≤ n
  metric6{x₁}{x₂}{n} p =
    begin
       x₁ + x₂
          ≤⟨ m≤m+n (x₁ + x₂) 1  ⟩
       (x₁ + x₂) + 1
          ≤⟨ ≤-reflexive (+-assoc x₁ x₂ 1)  ⟩
       x₁ + (x₂ + 1)
          ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = x₁}) plus1-suc) ⟩
       x₁ + suc x₂
          ≤⟨ p ⟩
       n
    ∎  

  metric7 : ∀ {x i n : ℕ}
      → suc (x + suc i) ≤ n
      → suc (x + i) ≤ n
  metric7{x}{i}{n} p =
    begin
      suc (x + i)
          ≤⟨ ≤-reflexive (sym plus1-suc) ⟩
      (x + i) + 1
          ≤⟨ ≤-reflexive (+-assoc x i 1) ⟩
      x + (i + 1)
          ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = x}) plus1-suc) ⟩
      x + (suc i)
          ≤⟨ n≤1+n (x + suc i) ⟩
      suc (x + (suc i))
          ≤⟨ p ⟩
      n
    ∎  

  metric8 : ∀{g h n : ℕ}
      → suc (g + suc (suc h)) ≤ n
      → g + h ≤ n
  metric8{g}{h}{n} p =
    begin
      g + h
          ≤⟨ m≤m+n (g + h) (1 + 1) ⟩
      (g + h) + (1 + 1)
          ≤⟨ ≤-reflexive (+-assoc g h (1 + 1)) ⟩
      g + (h + (1 + 1))
          ≤⟨ ≤-reflexive (cong₂ (_+_) (refl{x = g}) (+-comm h 2)) ⟩
      g + (suc (suc h))
          ≤⟨ n≤1+n (g + suc (suc h)) ⟩
      suc (g + (suc (suc h)))
          ≤⟨ p ⟩
      n
    ∎  


  compose : ∀{A B C} → (n : ℕ) → (c : Cast (A ⇒ B)) → (d : Cast (B ⇒ C))
          → {m : size-cast c + size-cast d ≤ n } → Cast (A ⇒ C)

  compose-gnd : ∀{A B C} → (n : ℕ) → (c : GroundCast (A ⇒ B)) → (d : GroundCast (B ⇒ C))
               → {m : size-gnd c + size-gnd d ≤ n }
               → GroundCast (A ⇒ C)
  compose-gnd{A}{B}{C} zero c d {m} = ⊥-elim (plus-gnd-pos {A ⇒ B}{B ⇒ C}{c}{d} m)
  compose-gnd (suc n) cid h = h
  compose-gnd (suc n) (cfun c d) cid = cfun c d
  compose-gnd (suc n) (cfun c d) (cfun c₁ d₁) {s≤s m} =
     let sc1 = size-cast c₁ in let sd1 = size-cast d₁ in let sc = size-cast c in let sd = size-cast d in
     cfun (compose n c₁ c {metric1{sc}{sd}{sc1} m}) (compose n d d₁{metric2{sc}{sd} m})
  compose-gnd (suc n) (cpair c d) cid = cpair c d
  compose-gnd (suc n) (cpair c d) (cpair c₁ d₁) {s≤s m} =
    let sc1 = size-cast c₁ in let sd1 = size-cast d₁ in let sc = size-cast c in let sd = size-cast d in  
    cpair (compose n c c₁ {metric3{sc} m}) (compose n d d₁ {metric2{sc} m})
  compose-gnd (suc n) (csum c d) cid = csum c d
  compose-gnd (suc n) (csum c d) (csum c₁ d₁){s≤s m} =
    let sc1 = size-cast c₁ in let sd1 = size-cast d₁ in let sc = size-cast c in let sd = size-cast d in  
    csum (compose n c c₁ {metric3{sc} m}) (compose n d d₁ {metric2{sc}{sd} m})

  compose-intmd : ∀{A B C} → (n : ℕ) → (c : IntermediateCast (A ⇒ B))
          → (d : IntermediateCast (B ⇒ C))
          → {m : size-intmd c + size-intmd d ≤ n }
          → IntermediateCast (A ⇒ C)
  compose-intmd{A}{B}{C} zero c d {m} = ⊥-elim (plus-intmd-pos {A ⇒ B}{B ⇒ C}{c}{d} m)
  compose-intmd (suc n) (inj G x) (inj .⋆ (cid {.⋆} {()}))
  compose-intmd (suc n) (inj G x) (gnd (cid {.⋆} {()}))
  compose-intmd (suc n) (inj G x) (cfail G₁ H x₁) = (cfail G₁ H x₁)
  compose-intmd (suc n) (gnd g) (inj G h {x}){s≤s m} = inj G (compose-gnd n g h {metric4 m}) {x}  
  compose-intmd (suc n) (gnd g) (gnd h){s≤s m} = gnd (compose-gnd n g h {metric4 m})
  compose-intmd (suc n) (gnd g) (cfail G H x) = cfail G H x
  compose-intmd (suc n) (cfail G H x) j = cfail G H x

  compose{A}{B}{C} zero c d {m} = ⊥-elim (plus-cast-pos {A ⇒ B}{B ⇒ C}{c}{d} m)
  compose (suc n) id⋆ d = d
  compose (suc n) (proj G x x₁ {g}) id⋆ = (proj G x x₁ {g})
  compose (suc n) (proj {⋆} G ℓ (inj G₁ x {g1}) {g}) (proj H ℓ' i₂ {h}) {s≤s m} with gnd-eq? G₁ H {g1}{h}
  ... | inj₁ eq rewrite eq = proj G ℓ (compose-intmd n (gnd x) i₂ {metric5 m}) {g}
  ... | inj₂ neq = proj G ℓ (cfail G₁ H ℓ) {g}
  compose (suc n) (proj .⋆ ℓ (gnd cid) {G-Base ()}) (proj H ℓ' i₂ {h})
  compose (suc n) (proj G ℓ (cfail G₁ H₁ x) {g}) (proj H ℓ' i₂ {h}) =
     proj G ℓ (cfail G₁ H₁ x) {g}
  compose (suc n) (proj G ℓ x₁ {g}) (intmd x₂){s≤s m} =
     proj G ℓ (compose-intmd n x₁ x₂ {metric6 m}) {g}
  compose (suc n) (intmd (inj G x {g})) id⋆ = intmd (inj G x {g})
  compose (suc n) (intmd (inj G x {g})) (proj H ℓ i₂ {h}) {s≤s m} with gnd-eq? G H {g}{h}
  ... | inj₁ eq rewrite eq = intmd (compose-intmd n (gnd x) i₂ {metric7 m})
  ... | inj₂ neq = intmd (cfail G H ℓ)
  compose (suc n) (intmd (inj G i₁)) (intmd (inj .⋆ cid {G-Base ()}))
  compose (suc n) (intmd (inj G i₁)) (intmd (gnd (cid {.⋆} {()})))
  compose (suc n) (intmd (inj G i₁)) (intmd (cfail G₁ H ℓ)) = (intmd (cfail G₁ H ℓ))
  compose (suc n) (intmd (gnd g)) id⋆ = intmd (gnd g)
  compose (suc n) (intmd (gnd (cid {.⋆} {()}))) (proj G x x₁)
  compose (suc n) (intmd (gnd g)) (intmd (inj G h {x})) {s≤s m} =
     intmd (inj G (compose-gnd n g h {metric8 m}) {x})
  compose (suc n) (intmd (gnd g)) (intmd (gnd h)) {s≤s m} =
     intmd (gnd (compose-gnd n g h {metric8 m}))
  compose (suc n) (intmd (gnd g)) (intmd (cfail G H x)) = (intmd (cfail G H x))
  compose (suc n) (intmd (cfail G H x)) d = (intmd (cfail G H x))

  applyCast : ∀ {Γ A B} → (M : Γ ⊢ A) → (Value M) → (c : Cast (A ⇒ B)) → ∀ {a : Active c} → Γ ⊢ B
  applyCast M v id⋆ {a} = M
  applyCast M v (intmd (gnd cid)) {a} = M
  applyCast M v (intmd (cfail G H ℓ)) {a} = blame ℓ
  applyCast M v (intmd (gnd (cfun c d))) {A-intmd (A-gnd ())}
  applyCast M v (intmd (inj G x)) {A-intmd ()}
  applyCast M v (proj G ℓ i {g}) {a} with PCR.canonical⋆ M v
  ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ i' , meq ⟩ ⟩ ⟩ ⟩ rewrite meq =
     M' ⟨ compose (size-cast c + size-cast (proj G ℓ i {g})) c (proj G ℓ i {g}) {≤-reflexive refl} ⟩
  applyCast M v (intmd (gnd (cpair c d))) {a} =
    cons (fst M ⟨ c ⟩) (snd M ⟨ d ⟩)
  applyCast M v (intmd (gnd (csum{A₁}{B₁}{A₂}{B₂} c d))) {a} =
    let l = inl ((` Z) ⟨ c ⟩) in
    let r = inr ((` Z) ⟨ d ⟩) in
    case M (ƛ A₁ , l) (ƛ A₂ , r)

  funCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
  funCast M (proj G x x₁) {()} N
  funCast M (intmd (gnd cid)) {I-intmd (I-gnd ())} N
  funCast M (intmd (cfail G H ℓ)) {I-intmd ()} N
  funCast M (intmd (gnd (cfun c d))) {i} N =
    (M · (N ⟨ c ⟩)) ⟨ d ⟩

  fstCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ A'
  fstCast M (proj G x x₁) {()}
  fstCast M (intmd .(gnd _)) {I-intmd (I-gnd ())}

  sndCast : ∀ {Γ A A' B'} → Γ ⊢ A → (c : Cast (A ⇒ (A' `× B'))) → ∀ {i : Inert c} → Γ ⊢ B'
  sndCast M (proj G x x₁) {()}
  sndCast M (intmd .(gnd _)) {I-intmd (I-gnd ())}
  
  caseCast : ∀ {Γ A A' B' C} → Γ ⊢ A → (c : Cast (A ⇒ (A' `⊎ B'))) → ∀ {i : Inert c} → Γ ⊢ A' ⇒ C → Γ ⊢ B' ⇒ C → Γ ⊢ C
  caseCast L .(intmd (gnd _)) {I-intmd (I-gnd ())} M N
  
  baseNotInert : ∀ {A B} → (c : Cast (A ⇒ B)) → Base B → ¬ Inert c
  baseNotInert .(intmd (inj _ _)) () (I-intmd I-inj)
  baseNotInert .(intmd (gnd (cfun _ _))) () (I-intmd (I-gnd I-cfun))

  module Red = PCR.Reduction applyCast funCast fstCast sndCast caseCast baseNotInert
  open Red

  import GTLC2CC
  module Compile = GTLC2CC Cast (λ A B ℓ {c} → coerce A B {c} ℓ)

