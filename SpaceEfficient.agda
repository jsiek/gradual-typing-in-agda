open import Types hiding (_⊔_)
open import Labels
open import Variables
open import CastStructure
import EfficientParamCasts
open import Data.Nat {-using (ℕ; _≤_; _⊔_; z≤n; s≤s)-}
open import Data.Nat.Properties
open import Data.Nat.Solver
open Data.Nat.Properties.≤-Reasoning
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

{-

  A proof that the Efficient Parameterized Cast Calculus
  is indeed space efficient.

-}

module SpaceEfficient (ecs : EfficientCastStruct) where

  open EfficientCastStruct ecs
  open EfficientParamCasts ecs

  import ParamCastCalculus
  open ParamCastCalculus Cast
  open import EfficientParamCastAux precast

  c-height : ∀{Γ A} (M : Γ ⊢ A) → ℕ
  c-height (` x) = 0
  c-height (ƛ M) = c-height M
  c-height (L · M) = c-height L ⊔ c-height M
  c-height ($ x) = 0
  c-height (if L M N) = c-height L ⊔ c-height M ⊔ c-height N
  c-height (cons M N) = c-height M ⊔ c-height N
  c-height (fst M) = c-height M
  c-height (snd M) = c-height M
  c-height (inl M) = c-height M
  c-height (inr M) = c-height M
  c-height (case L M N) = c-height L ⊔ c-height M ⊔ c-height N
  c-height (M ⟨ c ⟩) = c-height M ⊔ height c
  c-height (blame ℓ) = 0

  plug-height : ∀ {Γ A B} (M : Γ ⊢ A) (M′ : Γ ⊢ A) (F : Frame A B)
      → c-height M′ ≤ c-height M
      → c-height (plug M′ F) ≤ c-height (plug M F)
  plug-height M M′ F M′≤M  = {!!}

  subst-height : ∀ {Γ A B} (N : Γ , A ⊢ B) (W : Γ ⊢ A)
      → c-height (N [ W ]) ≤ c-height N ⊔ c-height W
  subst-height N W = {!!}

  rename-height : ∀{Γ Δ A} (M : Γ ⊢ A) (ρ : ∀ {C} → Γ ∋ C → Δ ∋ C)
      → c-height M ≡ c-height (rename ρ M)
  rename-height (` x) ρ = refl
  rename-height (ƛ M) ρ rewrite rename-height M (ext ρ) = refl
  rename-height (L · M) ρ rewrite rename-height L ρ | rename-height M ρ = refl
  rename-height ($ x) ρ = refl
  rename-height (if L M N) ρ rewrite rename-height L ρ | rename-height M ρ
     | rename-height N ρ = refl
  rename-height (cons M N) ρ rewrite rename-height M ρ | rename-height N ρ = refl
  rename-height (fst M) ρ rewrite rename-height M ρ = refl
  rename-height (snd M) ρ rewrite rename-height M ρ = refl
  rename-height (inl M) ρ rewrite rename-height M ρ = refl
  rename-height (inr M) ρ rewrite rename-height M ρ = refl
  rename-height (case L M N) ρ rewrite rename-height L ρ | rename-height M ρ
     | rename-height N ρ = refl
  rename-height (M ⟨ c ⟩) ρ rewrite rename-height M ρ = refl
  rename-height (blame ℓ) ρ = refl

  module PreserveHeight
    (applyCast-height : ∀{Γ}{A B}{V}{v : Value {Γ} V}{c : Cast (A ⇒ B)}
        {a : Active c}
      → c-height (applyCast V v c {a}) ≤ c-height V ⊔ height c)
    (dom-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}{x : Cross c}
       → height (dom c x) ≤ height c)
    (cod-height : ∀{A B C D}{c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}{x : Cross c}
       → height (cod c x) ≤ height c)
    (fst-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}{x : Cross c}
       → height (fstC c x) ≤ height c)
    (snd-height : ∀{A B C D}{c : Cast (A `× B ⇒ C `× D)}{x : Cross c}
       → height (sndC c x) ≤ height c)
    (inlC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}{x : Cross c}
       → height (inlC c x) ≤ height c)
    (inrC-height : ∀{A B C D}{c : Cast (A `⊎ B ⇒ C `⊎ D)}{x : Cross c}
       → height (inrC c x) ≤ height c)
      where

    preserve-height : ∀ {Γ A} {M M′ : Γ ⊢ A} {ctx : ReductionCtx}
         → ctx / M —→ M′ → c-height M′ ≤ c-height M
    preserve-height (ξ {M = M₁}{M₁′}{F} M₁—→M₁′) =
      let IH = preserve-height M₁—→M₁′ in plug-height M₁ M₁′ F IH
    preserve-height (ξ-cast {M = M₁}{M₁′} M₁—→M₁′) =
      let IH = preserve-height M₁—→M₁′ in ⊔-mono-≤ IH ≤-refl
    preserve-height ξ-blame = z≤n
    preserve-height ξ-cast-blame = z≤n
    preserve-height (β{N = N}{W = W} vW) = subst-height N W
    preserve-height δ = z≤n
    preserve-height β-if-true = m≤m⊔n _ _
    preserve-height β-if-false = n≤m⊔n _ _
    preserve-height (β-fst vV vW) = m≤m⊔n _ _
    preserve-height (β-snd vV vW) = n≤m⊔n _ _
    preserve-height (β-caseL {V = V}{L}{M} vV) =
      begin
        c-height L ⊔ c-height V       ≤⟨ ≤-reflexive (⊔-comm (c-height L) _) ⟩ 
        c-height V ⊔ c-height L       ≤⟨ m≤m⊔n _ _ ⟩ 
        (c-height V ⊔ c-height L) ⊔ c-height M
      ∎ 
    preserve-height (β-caseR {V = V}{L}{M} vV) =
      begin
        c-height M ⊔ c-height V       ≤⟨ ≤-reflexive (⊔-comm (c-height M) _) ⟩ 
        c-height V ⊔ c-height M       ≤⟨ ⊔-mono-≤ (m≤m⊔n (c-height V) _) ≤-refl ⟩ 
        (c-height V ⊔ c-height L) ⊔ c-height M
      ∎ 
    preserve-height (cast v) = applyCast-height 
    preserve-height (fun-cast {V = V}{W}{c} vV vW {x}) =
      begin
        (c-height V ⊔ (c-height W ⊔ height (dom c x))) ⊔ height (cod c x)
          ≤⟨ ≤-reflexive (⊔-assoc (c-height V) _ _) ⟩
        c-height V ⊔ ((c-height W ⊔ height (dom c x)) ⊔ height (cod c x))
          ≤⟨ ⊔-monoʳ-≤  (c-height V) (≤-reflexive (⊔-assoc (c-height W) _ _)) ⟩
        c-height V ⊔ (c-height W ⊔ (height (dom c x) ⊔ height (cod c x)))
          ≤⟨ ⊔-monoʳ-≤  (c-height V) (⊔-monoʳ-≤ (c-height W) (⊔-least dom-height
                                                                      cod-height)) ⟩
        c-height V ⊔ (c-height W ⊔ height c)
          ≤⟨ ⊔-monoʳ-≤  (c-height V) (≤-reflexive (⊔-comm (c-height W) _)) ⟩
        c-height V ⊔ (height c ⊔ c-height W)
          ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height V) _ _)) ⟩
        (c-height V ⊔ height c) ⊔ c-height W
      ∎
    preserve-height (fst-cast {V = V} vV {x}) = ⊔-monoʳ-≤  (c-height V) fst-height
    preserve-height (snd-cast {V = V} vV {x}) = ⊔-monoʳ-≤  (c-height V) snd-height
    preserve-height (case-cast {V = V}{W₁}{W₂}{c} vV {x}) =
      begin
        (c-height V ⊔ (c-height (rename S_ W₁) ⊔ height (inlC c x))) ⊔
                      (c-height (rename S_ W₂) ⊔ height (inrC c x))
        ≤⟨ ⊔-mono-≤ (⊔-monoʳ-≤ (c-height V) (≤-reflexive (⊔-comm (c-height (rename S_ W₁)) _)))
               (≤-reflexive (⊔-comm (c-height (rename S_ W₂)) _)) ⟩
        (c-height V ⊔ (height (inlC c x) ⊔ c-height (rename S_ W₁))) ⊔
                      (height (inrC c x) ⊔ c-height (rename S_ W₂))
        ≤⟨ ≤-reflexive (⊔-assoc (c-height V) _ _) ⟩
        c-height V ⊔ ((height (inlC c x) ⊔ c-height (rename S_ W₁)) ⊔
                      (height (inrC c x) ⊔ c-height (rename S_ W₂)))
        ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-reflexive (⊔-assoc (height (inlC c x)) _ _)) ⟩
        c-height V ⊔ (height (inlC c x) ⊔ (c-height (rename S_ W₁) ⊔
                      (height (inrC c x) ⊔ c-height (rename S_ W₂))))
        ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoʳ-≤ (height (inlC c x))
                   (≤-reflexive (sym (⊔-assoc (c-height (rename S_ W₁)) _ _)))) ⟩        
        c-height V ⊔ (height (inlC c x) ⊔ ((c-height (rename S_ W₁) ⊔ height (inrC c x))
                          ⊔ c-height (rename S_ W₂)))
        ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoʳ-≤ (height (inlC c x)) (⊔-monoˡ-≤ (c-height (rename S_ W₂))
                   (≤-reflexive (⊔-comm (c-height (rename S_ W₁)) _)))) ⟩        
        c-height V ⊔ (height (inlC c x) ⊔ ((height (inrC c x) ⊔ c-height (rename S_ W₁))
                          ⊔ c-height (rename S_ W₂)))
        ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoʳ-≤ (height (inlC c x)) (≤-reflexive (⊔-assoc (height (inrC c x)) _ _))) ⟩ 
        c-height V ⊔ (height (inlC c x) ⊔ (height (inrC c x)
                ⊔ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂))))
        ≤⟨ ⊔-monoʳ-≤ (c-height V) (≤-reflexive (sym (⊔-assoc (height (inlC c x)) _ _))) ⟩
        c-height V ⊔ ((height (inlC c x) ⊔ height (inrC c x))
                ⊔ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂)))
        ≤⟨ ⊔-monoʳ-≤ (c-height V) (⊔-monoˡ-≤ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂))
                   (⊔-least inlC-height inrC-height)) ⟩
        c-height V ⊔ (height c ⊔ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂)))
        ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height V) _ _)) ⟩
        (c-height V ⊔ height c) ⊔ (c-height (rename S_ W₁) ⊔ c-height (rename S_ W₂))
        ≤⟨ ⊔-monoʳ-≤ (c-height V ⊔ height c) (⊔-mono-≤ (≤-reflexive (sym (rename-height W₁ S_)))
                     (≤-reflexive (sym (rename-height W₂ S_)))) ⟩
        (c-height V ⊔ height c) ⊔ (c-height W₁ ⊔ c-height W₂)
        ≤⟨ ≤-reflexive (sym (⊔-assoc (c-height V ⊔ height c) _ _)) ⟩
        ((c-height V ⊔ height c) ⊔ c-height W₁) ⊔ c-height W₂
      ∎
    preserve-height (compose-casts {M = M}{c}{d}) =
      begin
        c-height M ⊔ height (compose c d) ≤⟨ ⊔-monoʳ-≤ (c-height M) (compose-height c d) ⟩
        c-height M ⊔ (height c ⊔ height d) ≤⟨ ≤-reflexive (sym (⊔-assoc(c-height M) _ _)) ⟩
        (c-height M ⊔ height c) ⊔ height d
      ∎

  data NotCast : ∀{Γ A} → Γ ⊢ A → Set
  
  data MaybeCast : ∀{Γ A} → Γ ⊢ A → Set where
    notCast : ∀{Γ A}{M : Γ ⊢ A} → NotCast M → MaybeCast M
    isCast : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)} → NotCast M → MaybeCast (M ⟨ c ⟩)

  data NotCast where
    ncvar : ∀{Γ A}{∋x : Γ ∋ A} → NotCast (` ∋x)
    nclam : ∀{Γ B A}{N : Γ , A ⊢ B} → MaybeCast N → NotCast (ƛ N)
    ncapp : ∀{Γ A B}{L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A} → MaybeCast L → MaybeCast M → NotCast (L · M)
    nclit : ∀{Γ : Context}{A}{r : rep A}{p : Prim A} → NotCast {Γ} ($_ r {p})
    ncif : ∀{Γ A}{L : Γ ⊢ ` 𝔹}{M N : Γ ⊢ A} → MaybeCast L → MaybeCast M → MaybeCast N → NotCast (if L M N)
    nccons : ∀{Γ A B}{M : Γ ⊢ A}{N : Γ ⊢ B} → NotCast M → NotCast N → NotCast (cons M N)
    ncfst : ∀{Γ A B}{M : Γ ⊢ A `× B} → MaybeCast M → NotCast (fst M)
    ncsnd : ∀{Γ A B}{M : Γ ⊢ A `× B} → MaybeCast M → NotCast (snd M)
    ncinl : ∀{Γ A B}{M : Γ ⊢ A} → NotCast {Γ}{A `⊎ B} (inl M)
    ncinr : ∀{Γ A B}{M : Γ ⊢ B} → NotCast {Γ}{A `⊎ B} (inr M)
    nccase : ∀{Γ A B C}{L : Γ ⊢ A `⊎ B}{M : Γ ⊢ A ⇒ C}{N : Γ ⊢ B ⇒ C}
      → MaybeCast L → NotCast M → NotCast N → NotCast (case L M N)

  maybecast-size : ∀{Γ A} (M : Γ ⊢ A) → MaybeCast M → size M ≤ 1 + 4 * ideal-size M

  nocast-size : ∀{Γ A} (M : Γ ⊢ A) → NotCast M → size M ≤ 4 * ideal-size M
  nocast-size (` ∋x) ncvar = s≤s z≤n
  nocast-size (ƛ N) (nclam mcN) =
    let IH = maybecast-size N mcN in
    begin
      suc (size N)
      ≤⟨ s≤s IH ⟩
      suc (1 + 4 * (ideal-size N))
      ≤⟨ s≤s (s≤s (≤-step (≤-step ≤-refl))) ⟩
      4 + 4 * (ideal-size N)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 4 1 _ )) ⟩
      4 * suc (ideal-size N)
    ∎
  nocast-size (L · M) (ncapp mcL mcM) =
    let IH1 = maybecast-size L mcL in
    let IH2 = maybecast-size M mcM in
    begin
      1 + (size L + size M)
      ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
      1 + ((1 + 4 * ideal-size L) + (1 + 4 * ideal-size M))
      ≤⟨ ≤-reflexive (solve 2 (λ x y → con 1 :+ ((con 1 :+ con 4 :* x) :+ (con 1 :+ con 4 :* y))
                         := con 3 :+ ((con 4 :* x) :+ (con 4 :* y))) refl (ideal-size L) (ideal-size M)) ⟩
      3 + ((4 * ideal-size L) + (4 * ideal-size M))
      ≤⟨ ≤-step ≤-refl ⟩
      4 + ((4 * ideal-size L) + (4 * ideal-size M))
      ≤⟨ +-monoʳ-≤ 4 (≤-reflexive ((sym (*-distribˡ-+ 4 (ideal-size L) (ideal-size M) )))) ⟩
      4 + 4 * (ideal-size L + ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 4 1 _ )) ⟩
      4 * suc (ideal-size L + ideal-size M)
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
      1 + ((1 + 4 * ideal-size L) + (1 + 4 * ideal-size M) + (1 + 4 * ideal-size N))
      ≤⟨ ≤-reflexive (solve 3 (λ x y z → con 1 :+ ((con 1 :+ con 4 :* x) :+ (con 1 :+ con 4 :* y) :+ (con 1 :+ con 4 :* z)) := con 4 :+ con 4 :* (x :+ y :+ z)) refl (ideal-size L) (ideal-size M) (ideal-size N)) ⟩
      4 + 4 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 4 1 _ )) ⟩
      4 * suc (ideal-size L + ideal-size M + ideal-size N)
    ∎
    where open +-*-Solver
  nocast-size .(cons _ _) (nccons nc nc₁) = {!!}
  nocast-size .(fst _) (ncfst x) = {!!}
  nocast-size .(snd _) (ncsnd x) = {!!}
  nocast-size .(inl _) ncinl = {!!}
  nocast-size .(inr _) ncinr = {!!}
  nocast-size .(case _ _ _) (nccase x nc nc₁) = {!!}

  maybecast-size M (notCast x) = ≤-step (nocast-size M x)
  maybecast-size (M ⟨ c ⟩) (isCast x) = s≤s (nocast-size M x)

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
    compile-efficient (⟦ M , N ⟧) (⊢cons d d₁) = nccons (compile-efficient M d) (compile-efficient N d₁)
    compile-efficient (fst M at ℓ) (⊢fst d x) = ncfst (isCast (compile-efficient M d))
    compile-efficient (snd M at ℓ) (⊢snd d x) = ncsnd (isCast (compile-efficient M d))
    compile-efficient (inl M other B) (⊢inl d) = ncinl
    compile-efficient (inr M other A) (⊢inr d) = ncinr
    compile-efficient (case L of B₁ ⇒ M ∣ C₁ ⇒ N at ℓ) (⊢case d d₁ d₂ abc bc) =
      let IH1 = compile-efficient L d in 
      let IH2 = compile-efficient M d₁ in
      let IH3 = compile-efficient N d₂ in 
        nccase (isCast IH1) (nclam (isCast IH2)) (nclam (isCast IH3))

{-

  module EfficientCompile
    (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
    where

    open import GTLC
    open import GTLC2CC Cast cast

    compile-efficient : ∀{Γ A} (M : Γ ⊢G A) → size (compile M) ≤ 7 * ideal-size (compile M)
    compile-efficient (` x) = s≤s z≤n
    compile-efficient (ƛ A ˙ M) =
      let IH = compile-efficient M in
      begin
        suc (size (compile M))
        ≤⟨ s≤s (≤-step (≤-step (≤-step (≤-step (≤-step (≤-step IH)))))) ⟩
        7 + (7 * (ideal-size (compile M)))
        ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _ )) ⟩
        7 * (suc (ideal-size (compile M)))
      ∎
    compile-efficient (_·_at_ {Γ}{A}{A₁}{A₂}{B} L M ℓ {m}{cn}) =
      let IH1 = compile-efficient L in
      let IH2 = compile-efficient M in
      begin
        size (compile (_·_at_ {Γ}{A}{A₁}{A₂}{B} L M ℓ {m}{cn}))
        ≤⟨ ≤-refl ⟩
        suc (suc (size (compile L)) + suc (size (compile M)))
        ≤⟨ ≤-step (≤-step (≤-step (≤-step (≤-reflexive (cong suc (cong suc (+-suc _ _))))))) ⟩
        7 + (size (compile L) + size (compile M))
        ≤⟨ +-monoʳ-≤ 7 (+-mono-≤ IH1 IH2) ⟩
        7 + (7 * ideal-size (compile L) + 7 * ideal-size (compile M))
        ≤⟨ +-monoʳ-≤ 7 (≤-reflexive (sym (*-distribˡ-+ 7 (ideal-size (compile L)) _))) ⟩        
        7 + (7 * (ideal-size (compile L) + ideal-size (compile M)))
        ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _)) ⟩
        7 * suc (ideal-size (compile L) + ideal-size (compile M))
        ≤⟨ ≤-refl ⟩
        7 * ideal-size (compile (_·_at_ {Γ}{A}{A₁}{A₂}{B} L M ℓ {m}{cn}))
      ∎
    compile-efficient ($ x) = s≤s z≤n
    compile-efficient (if L M N ℓ) =
      let IH1 = compile-efficient L in
      let IH2 = compile-efficient M in
      let IH3 = compile-efficient N in
      begin
        suc ((suc (size (compile L)) + suc (size (compile M))) + suc (size (compile N)))
            ≤⟨ ≤-reflexive (solve 3 (λ x y z → con 1 :+ ((con 1 :+ x) :+ (con 1 :+ y)) :+ (con 1 :+ z)
                                 := con 4 :+ ((x :+ y) :+ z))
                            refl (size (compile L)) (size (compile M)) (size (compile N))) ⟩
        4 + (size (compile L) + size (compile M) + size (compile N))
            ≤⟨ +-mono-≤ {4}{7} (s≤s (s≤s (s≤s (s≤s z≤n)))) ≤-refl ⟩
        7 + (size (compile L) + size (compile M) + size (compile N))   ≤⟨ +-monoʳ-≤ 7 (+-mono-≤ (+-mono-≤ IH1 IH2) IH3) ⟩
        7 + (7 * ideal-size (compile L) + 7 * ideal-size (compile M) + 7 * ideal-size (compile N))
            ≤⟨ ≤-reflexive (cong (λ x → 7 + (x + 7 * ideal-size (compile N)))
                   (sym (*-distribˡ-+ 7 (ideal-size (compile L)) _))) ⟩ 
        7 + (7 * (ideal-size (compile L) + ideal-size (compile M)) + 7 * ideal-size (compile N))
            ≤⟨ +-monoʳ-≤ 7 (≤-reflexive (sym (*-distribˡ-+ 7 (ideal-size (compile L) + ideal-size (compile M)) _))) ⟩ 
        7 + (7 * ((ideal-size (compile L) + ideal-size (compile M)) + ideal-size (compile N)))
            ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _)) ⟩
        7 * (suc (ideal-size (compile L) + ideal-size (compile M) + ideal-size (compile N)))
      ∎
      where open +-*-Solver
    compile-efficient (cons M N) =
      let IH1 = compile-efficient M in
      let IH2 = compile-efficient N in
      begin
        1 + (size (compile M) + size (compile N))                     ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
        1 + (7 * ideal-size (compile M) + 7 * ideal-size (compile N)) ≤⟨ +-mono-≤ {1}{7} (s≤s z≤n) ≤-refl ⟩
        7 + (7 * ideal-size (compile M) + 7 * ideal-size (compile N))
                    ≤⟨ +-monoʳ-≤ 7 (≤-reflexive (sym (*-distribˡ-+ 7 (ideal-size (compile M)) _))) ⟩
        7 + (7 * (ideal-size (compile M) + ideal-size (compile N)))  ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _)) ⟩
        7 * (suc (ideal-size (compile M) + ideal-size (compile N)))
      ∎
    compile-efficient (fst {Γ}{A}{A₁}{A₂} M ℓ {m}) =
      let IH = compile-efficient M in
      begin
        2 + (size (compile M))               ≤⟨ s≤s (s≤s IH) ⟩
        2 + (7 * ideal-size (compile M))     ≤⟨ +-mono-≤ {2}{7} (s≤s (s≤s z≤n)) ≤-refl ⟩
        7 + (7 * (ideal-size (compile M)))   ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _)) ⟩        
        7 * (suc (ideal-size (compile M)))
      ∎
    compile-efficient (snd M ℓ) =
      let IH = compile-efficient M in
      begin
        2 + size (compile M)                  ≤⟨ s≤s (s≤s IH) ⟩
        2 + (7 * (ideal-size (compile M)))    ≤⟨ +-mono-≤ {2}{7} (s≤s (s≤s z≤n)) ≤-refl ⟩
        7 + (7 * (ideal-size (compile M)))    ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _)) ⟩        
        7 * (suc (ideal-size (compile M)))
      ∎
    compile-efficient (inl B M) =
      let IH = compile-efficient M in
      begin
        1 + (size (compile M))                ≤⟨ s≤s IH ⟩        
        1 + (7 * (ideal-size (compile M)))    ≤⟨ +-mono-≤ {1}{7} (s≤s z≤n) ≤-refl ⟩
        7 + (7 * (ideal-size (compile M)))    ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _)) ⟩        
        7 * (suc (ideal-size (compile M)))
      ∎
    compile-efficient (inr A M) =
      let IH = compile-efficient M in
      begin
        1 + (size (compile M))                ≤⟨ s≤s IH ⟩        
        1 + (7 * (ideal-size (compile M)))    ≤⟨ +-mono-≤ {1}{7} (s≤s z≤n) ≤-refl ⟩
        7 + (7 * (ideal-size (compile M)))    ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _)) ⟩
        7 * (suc (ideal-size (compile M)))
      ∎
    compile-efficient (case L M N ℓ) =
      let IH1 = compile-efficient L in
      let IH2 = compile-efficient M in
      let IH3 = compile-efficient N in
      begin
        suc (suc (suc (size (compile L))) + suc (suc (size (compile M))) + suc (suc (size (compile N))))
        ≤⟨ ≤-reflexive (solve 3
                 (λ x y z → con 1 :+ ((con 2 :+ x) :+ (con 2 :+ y) :+ (con 2 :+ z)) := con 7 :+ (x :+ y :+ z))
                 refl (size (compile L)) (size (compile M)) (size (compile N))) ⟩
        7 + (size (compile L) + size (compile M) + size (compile N))
        ≤⟨ +-monoʳ-≤ 7 (+-mono-≤ (+-mono-≤ IH1 IH2) IH3) ⟩
        7 + (7 * ideal-size (compile L) + 7 * ideal-size (compile M) + 7 * ideal-size (compile N))
        ≤⟨ +-monoʳ-≤ 7 (+-mono-≤ (≤-reflexive (sym
                  (*-distribˡ-+ 7 (ideal-size (compile L)) (ideal-size (compile M))))) ≤-refl) ⟩
        7 + (7 * (ideal-size (compile L) + ideal-size (compile M)) + 7 * ideal-size (compile N))
        ≤⟨ +-monoʳ-≤ 7 (≤-reflexive (sym (*-distribˡ-+ 7 (ideal-size (compile L) + ideal-size (compile M))
                (ideal-size (compile N))))) ⟩
        7 + (7 * ((ideal-size (compile L) + ideal-size (compile M)) + ideal-size (compile N)))
        ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 7 1 _)) ⟩
        7 * (suc (ideal-size (compile L) + ideal-size (compile M) + ideal-size (compile N)))
      ∎
      where open +-*-Solver

  plug-size : ∀{Γ}{A B}{k : ℕ} → (M : Γ ⊢ A) → (F : Frame A B)
            → (kp : 0 < k) → size (plug M F) ≤ k * ideal-size (plug M F)
  plug-size {Γ}{A} M F kp = {!!}

  preserve-size : ∀ {Γ A}{M M′ : Γ ⊢ A} {ctx : ReductionCtx}{k : ℕ}
         → ctx / M —→ M′
         → size M ≤ k * ideal-size M → (kp : 0 < k)
         → size M′ ≤ k * ideal-size M′
  preserve-size (ξ {M′ = M′}{F = F} M—→M′) szM≤7iszM kp = plug-size M′ F kp 
  preserve-size {k = k}(ξ-cast {c = c}{M = M}{M′} M—→M′) szM≤7iszM kp = H
    where
    G : size M ≤ k * ideal-size M
    G = begin
          size M              ≤⟨ n≤1+n _ ⟩
          suc (size M)        ≤⟨ szM≤7iszM ⟩
          k * ideal-size M
        ∎
    IH : size M′ ≤ k * ideal-size M′
    IH = preserve-size M—→M′ G kp
    H : suc (size M′) ≤ k * ideal-size M′
    H = {!!}
      

  preserve-size ξ-blame szM≤7iszM kp = {!!}
  preserve-size ξ-cast-blame szM≤7iszM kp = {!!}
  preserve-size (β x) szM≤7iszM kp = {!!}
  preserve-size δ szM≤7iszM kp = {!!}
  preserve-size β-if-true szM≤7iszM kp = {!!}
  preserve-size β-if-false szM≤7iszM kp = {!!}
  preserve-size (β-fst x x₁) szM≤7iszM kp = {!!}
  preserve-size (β-snd x x₁) szM≤7iszM kp = {!!}
  preserve-size (β-caseL x) szM≤7iszM kp = {!!}
  preserve-size (β-caseR x) szM≤7iszM kp = {!!}
  preserve-size (cast v) szM≤7iszM kp = {!!}
  preserve-size (fun-cast v x) szM≤7iszM kp = {!!}
  preserve-size (fst-cast v) szM≤7iszM kp = {!!}
  preserve-size (snd-cast v) szM≤7iszM kp = {!!}
  preserve-size (case-cast v) szM≤7iszM kp = {!!}
  preserve-size compose-casts szM≤7iszM kp = {!!}

-}
