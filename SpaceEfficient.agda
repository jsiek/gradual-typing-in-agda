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
    isCast : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}
       → NotCast M → MaybeCast (M ⟨ c ⟩)
    castVal : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}
       → MaybeCast M → Value M → MaybeCast (M ⟨ c ⟩)

  data NotCast where
    ncvar : ∀{Γ A}{∋x : Γ ∋ A} → NotCast (` ∋x)
    nclam : ∀{Γ B A}{N : Γ , A ⊢ B} → MaybeCast N → NotCast (ƛ N)
    ncapp : ∀{Γ A B}{L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}
          → MaybeCast L → MaybeCast M → NotCast (L · M)
    nclit : ∀{Γ : Context}{A}{r : rep A}{p : Prim A} → NotCast {Γ} ($_ r {p})
    ncif : ∀{Γ A}{L : Γ ⊢ ` 𝔹}{M N : Γ ⊢ A}
          → MaybeCast L → MaybeCast M → MaybeCast N → NotCast (if L M N)
    nccons : ∀{Γ A B}{M : Γ ⊢ A}{N : Γ ⊢ B}
          → MaybeCast M → MaybeCast N → NotCast (cons M N)
    ncfst : ∀{Γ A B}{M : Γ ⊢ A `× B} → MaybeCast M → NotCast (fst M)
    ncsnd : ∀{Γ A B}{M : Γ ⊢ A `× B} → MaybeCast M → NotCast (snd M)
    ncinl : ∀{Γ A B}{M : Γ ⊢ A} → MaybeCast M → NotCast {Γ}{A `⊎ B} (inl M)
    ncinr : ∀{Γ A B}{M : Γ ⊢ B} → MaybeCast M → NotCast {Γ}{A `⊎ B} (inr M)
    nccase : ∀{Γ A B C}{L : Γ ⊢ A `⊎ B}{M : Γ ⊢ A ⇒ C}{N : Γ ⊢ B ⇒ C}
           → MaybeCast L → MaybeCast M → MaybeCast N → NotCast (case L M N)
    ncblame : ∀{Γ A ℓ} → NotCast {Γ}{A} (blame {Γ}{A} ℓ)

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

  preserve-maybecast : ∀ {Γ A}{M M′ : Γ ⊢ A} {ctx : ReductionCtx}
         → MaybeCast M
         → ctx / M —→ M′
         → MaybeCast M′

  rename-value : ∀ {Γ Δ A} (M : Γ ⊢ A) (ρ : ∀{B} → Γ ∋ B → Δ ∋ B)
        → Value M → Value (rename ρ M)
  rename-simple : ∀ {Γ Δ A} (M : Γ ⊢ A) (ρ : ∀{B} → Γ ∋ B → Δ ∋ B)
        → SimpleValue M → SimpleValue (rename ρ M)
  rename-simple (ƛ N) ρ V-ƛ = V-ƛ
  rename-simple ($_ r {p}) ρ V-const = V-const
  rename-simple (cons M N) ρ (V-pair x x₁) = (V-pair (rename-value M ρ x) (rename-value N ρ x₁))
  rename-simple (inl M) ρ (V-inl x) = (V-inl (rename-value M ρ x))
  rename-simple (inr M) ρ (V-inr x) = (V-inr (rename-value M ρ x))
  
  rename-value M ρ (S-val sM) = S-val (rename-simple M ρ sM)
  rename-value (V ⟨ c ⟩) ρ (V-cast {i = i} sV) = V-cast {i = i} (rename-simple V ρ sV)

  subst-value : ∀ {Γ Δ A} (M : Γ ⊢ A) (σ : ∀{B} → Γ ∋ B → Δ ⊢ B)
        → Value M → Value (subst σ M)
        
  subst-simple : ∀ {Γ Δ A} (M : Γ ⊢ A) (σ : ∀{B} → Γ ∋ B → Δ ⊢ B)
        → SimpleValue M → SimpleValue (subst σ M)
  subst-simple (ƛ N) σ V-ƛ = V-ƛ
  subst-simple ($_ r {p}) σ V-const = V-const
  subst-simple (cons M N) σ (V-pair x x₁) =
     V-pair (subst-value M σ x) (subst-value N σ x₁)
  subst-simple (inl M) σ (V-inl x) = V-inl (subst-value M σ x)
  subst-simple (inr M) σ (V-inr x) = V-inr (subst-value M σ x)
  
  subst-value M σ (S-val x) = S-val (subst-simple M σ x)
  subst-value (M ⟨ c ⟩) σ (V-cast {i = i} x) = V-cast {i = i} (subst-simple M σ x)

  rename-notcast : ∀ {Γ Δ A} (N : Γ ⊢ A) (ρ : ∀{B} → Γ ∋ B → Δ ∋ B)
         →  NotCast N → NotCast (rename ρ N)
  rename-maybecast : ∀ {Γ Δ A} (N : Γ ⊢ A) (ρ : ∀{B} → Γ ∋ B → Δ ∋ B)
         →  MaybeCast N → MaybeCast (rename ρ N)
         
  rename-notcast (` ∋x) ρ ncvar = ncvar
  rename-notcast (ƛ N) ρ (nclam x) = nclam (rename-maybecast N (ext ρ) x)
  rename-notcast (L · M) ρ (ncapp x x₁) = ncapp (rename-maybecast L ρ x) (rename-maybecast M ρ x₁)
  rename-notcast .($ _) ρ nclit = nclit
  rename-notcast (if L M N) ρ (ncif x x₁ x₂) =
      ncif (rename-maybecast L ρ x) (rename-maybecast M ρ x₁) (rename-maybecast N ρ x₂)
  rename-notcast (cons M N) ρ (nccons x x₁) =
      nccons (rename-maybecast M ρ x) (rename-maybecast N ρ x₁)
  rename-notcast (fst M) ρ (ncfst x) = ncfst (rename-maybecast M ρ x)
  rename-notcast (snd M) ρ (ncsnd x) = ncsnd (rename-maybecast M ρ x)
  rename-notcast (inl M) ρ (ncinl x) = ncinl (rename-maybecast M ρ x)
  rename-notcast (inr M) ρ (ncinr x) = ncinr (rename-maybecast M ρ x)
  rename-notcast (case L M N) ρ (nccase x x₁ x₂) =
      nccase (rename-maybecast L ρ x) (rename-maybecast M ρ x₁) (rename-maybecast N ρ x₂)
  rename-notcast (blame ℓ) ρ ncblame = ncblame
  
  rename-maybecast N ρ (notCast x) = notCast (rename-notcast N ρ x)
  rename-maybecast (M ⟨ c ⟩) ρ (isCast x) = isCast (rename-notcast M ρ x)
  rename-maybecast (M ⟨ c ⟩) ρ (castVal mcN vM) = castVal (rename-maybecast M ρ mcN ) (rename-value M ρ vM)

  OKSubst : ∀{Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → Set
  OKSubst {Γ}{Δ} σ = ∀ {A} (x : Γ ∋ A)
                   → (NotCast (σ x)) ⊎ (MaybeCast (σ x) × Value (σ x))

  OKSubst-exts : ∀ {Γ Δ A} (σ : ∀{B} → Γ ∋ B → Δ ⊢ B)
         → OKSubst σ → OKSubst (exts σ {B = A})
  OKSubst-exts σ okσ Z = inj₁ ncvar
  OKSubst-exts σ okσ (S ∋x)
      with okσ ∋x
  ... | inj₁ xx = inj₁ (rename-notcast (σ ∋x) S_ xx)
  ... | inj₂ (⟨ yy , zz ⟩) = inj₂ (⟨ (rename-maybecast (σ ∋x) S_ yy) , (rename-value (σ ∋x) S_ zz) ⟩)

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
  
  preserve-maybecast mcM M-→M′ = {!!}

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
