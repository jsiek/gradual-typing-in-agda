open import Types
open import Variables
open import CastStructure
open import Labels
import EquivCast

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

module EquivLamBLamC where

open import GroundCast renaming (struct to sB)
module LamB = CastStructure.CastCalc sB
open CastStruct sB renaming (Cast to CastB)

open import GroundCoercions renaming (struct to sC)
module LamC = CastStructure.CastCalc sC
open CastStruct sC renaming (Cast to CastC)

module EquivBC = EquivCast sB sC

data _≈_ : ∀{A B} → CastB (A ⇒ B) → CastC (A ⇒ B) → Set where

   ≈-id : ∀{A}{a : Atomic A}{ℓ : Label}{c : A ~ A}
        → cast A A ℓ c ≈ id {A}{a}

   ≈-inj : ∀{A}{ℓ : Label}{c : A ~ ⋆}{g : Ground A}
         → cast A ⋆ ℓ c ≈ inj A {g}
         
   ≈-proj : ∀{A}{ℓ : Label}{c : ⋆ ~ A}{g : Ground A}
         → cast ⋆ A ℓ c ≈ proj A ℓ {g}

   ≈-fun : ∀{A B C D}{ℓ : Label}{cn : A ⇒ B ~ C ⇒ D}{ca : C ~ A}{bd : B ~ D}{c : CastC (C ⇒ A)}{d : CastC (B ⇒ D)}
          → cast C A ℓ ca ≈ c
          → cast B D ℓ bd ≈ d
          → cast (A ⇒ B) (C ⇒ D) ℓ (fun~ ca bd) ≈ cfun c d

   ≈-pair : ∀{A B C D}{ℓ : Label}{cn : A `× B ~ C `× D}{ac : A ~ C}{bd : B ~ D}{c : CastC (A ⇒ C)}{d : CastC (B ⇒ D)}
          → cast A C ℓ ac ≈ c
          → cast B D ℓ bd ≈ d
          → cast (A `× B) (C `× D) ℓ (pair~ ac bd) ≈ cpair c d

   ≈-sum : ∀{A B C D}{ℓ : Label}{cn : A `⊎ B ~ C `⊎ D}{ac : A ~ C}{bd : B ~ D}{c : CastC (A ⇒ C)}{d : CastC (B ⇒ D)}
          → cast A C ℓ ac ≈ c
          → cast B D ℓ bd ≈ d
          → cast (A `⊎ B) (C `⊎ D) ℓ (sum~ ac bd) ≈ csum c d

   ≈-inj-seq : ∀{A G}{nA : A ≢ ⋆}{g : Ground G}{¬gA : ¬ Ground A}{ag : A ~ G}{gs : G ~ ⋆}{ℓ : Label}{c : CastC (A ⇒ G)}{d : CastC (G ⇒ ⋆)}{as : A ~ ⋆}
          → cast A G ℓ ag ≈ c
          → cast G ⋆ ℓ gs ≈ d
          → cast A ⋆ ℓ as ≈ cseq c d

   ≈-proj-seq : ∀{A G}{nA : A ≢ ⋆}{g : Ground G}{¬gA : ¬ Ground A}{sg : ⋆ ~ G}{ga : G ~ A}{ℓ : Label}{c : CastC (⋆ ⇒ G)}{d : CastC (G ⇒ A)}{sa : ⋆ ~ A}
          → cast ⋆ G ℓ sg ≈ c
          → cast G A ℓ ga ≈ d
          → cast ⋆ A ℓ sa ≈ cseq c d

inert-equiv : ∀{A B : Type}{c₁ : CastB (A ⇒ B)}{c₂ : CastC (A ⇒ B)}
            → CastStruct.Inert sB c₁ → c₁ ≈ c₂ → CastStruct.Inert sC c₂
inert-equiv {A} {⋆} (I-inj gA (cast A ⋆ ℓ as)) ≈-inj = I-inj
inert-equiv {A} {⋆} (I-inj gA (cast A ⋆ ℓ as)) (≈-inj-seq {¬gA = ¬gA} c₁≈c₂ c₁≈c₃) = ⊥-elim (contradiction gA ¬gA)
inert-equiv (I-fun _) (≈-fun c₁≈c₂ c₁≈c₃) = I-fun

active-equiv : ∀{A B : Type}{c₁ : CastB (A ⇒ B)}{c₂ : CastC (A ⇒ B)}
            → CastStruct.Active sB c₁ → c₁ ≈ c₂ → CastStruct.Active sC c₂
active-equiv {A} {.A} (A-id .(cast A A _ _)) ≈-id = A-id
active-equiv {.⋆} {.⋆} (A-id .(cast ⋆ ⋆ _ _)) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-id .(cast ⋆ ⋆ _ _)) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-inj .(cast ⋆ ⋆ _ _) x x₁) ≈-id = A-id
active-equiv {A} {.⋆} (A-inj .(cast A ⋆ _ _) ¬gA x₁) (≈-inj{g = gA}) = ⊥-elim (contradiction gA ¬gA)
active-equiv {A} {.⋆} (A-inj .(cast A ⋆ _ _) x x₁) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-inj .(cast ⋆ ⋆ _ _) x x₁) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {.⋆} (A-proj .(cast ⋆ ⋆ _ _) x) ≈-id = A-id
active-equiv {.⋆} {B} (A-proj .(cast ⋆ B _ _) x) ≈-proj = A-proj
active-equiv {.⋆} {.⋆} (A-proj .(cast ⋆ ⋆ _ _) x) (≈-inj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.⋆} {B} (A-proj .(cast ⋆ B _ _) x) (≈-proj-seq c₁≈c₂ c₁≈c₃) = A-seq
active-equiv {.(_ `× _)} {.(_ `× _)} (A-pair .(cast (_ `× _) (_ `× _) _ _)) (≈-pair c₁≈c₂ c₁≈c₃) = A-pair
active-equiv {.(_ `⊎ _)} {.(_ `⊎ _)} (A-sum .(cast (_ `⊎ _) (_ `⊎ _) _ _)) (≈-sum c₁≈c₂ c₁≈c₃) = A-sum

dom-equiv : ∀{A B C D : Type}{c₁ : CastB ((A ⇒ B) ⇒ (C ⇒ D))}{i₁ : CastStruct.Inert sB c₁}
                             {c₂ : CastC ((A ⇒ B) ⇒ (C ⇒ D))}{i₂ : CastStruct.Inert sC c₂}
          → c₁ ≈ c₂ 
          → (CastStruct.dom sB c₁ i₁) ≈ (CastStruct.dom sC c₂ i₂)
dom-equiv {c₁ = cast .(_ ⇒ _) .(_ ⇒ _) ℓ c} {I-fun _} {cfun c₂ d₂} {I-fun} (≈-fun c₁≈c₂ c₁≈c₃) = c₁≈c₂

cod-equiv : ∀{A B C D : Type}{c₁ : CastB ((A ⇒ B) ⇒ (C ⇒ D))}{i₁ : CastStruct.Inert sB c₁}
                             {c₂ : CastC ((A ⇒ B) ⇒ (C ⇒ D))}{i₂ : CastStruct.Inert sC c₂}
          → c₁ ≈ c₂ 
          → (CastStruct.cod sB c₁ i₁) ≈ (CastStruct.cod sC c₂ i₂)
cod-equiv {c₁ = cast .(_ ⇒ _) .(_ ⇒ _) ℓ c} {I-fun _} {cfun c₂ d₂} {I-fun} (≈-fun c₁≈c₂ c₁≈c₃) = c₁≈c₃

fst-equiv : ∀{A B C D : Type}{c₁ : CastB ((A `× B) ⇒ (C `× D))}{i₁ : CastStruct.Inert sB c₁}
                             {c₂ : CastC ((A `× B) ⇒ (C `× D))}{i₂ : CastStruct.Inert sC c₂}
          → c₁ ≈ c₂ 
          → (CastStruct.fstC sB c₁ i₁) ≈ (CastStruct.fstC sC c₂ i₂)
fst-equiv {c₁ = cast .(_ `× _) .(_ `× _) ℓ c} {()} {cpair c₂ d₂} {()} (≈-pair c₁≈c₂ c₁≈c₃)

snd-equiv : ∀{A B C D : Type}{c₁ : CastB ((A `× B) ⇒ (C `× D))}{i₁ : CastStruct.Inert sB c₁}
                             {c₂ : CastC ((A `× B) ⇒ (C `× D))}{i₂ : CastStruct.Inert sC c₂}
          → c₁ ≈ c₂ 
          → (CastStruct.sndC sB c₁ i₁) ≈ (CastStruct.sndC sC c₂ i₂)
snd-equiv {c₁ = cast .(_ `× _) .(_ `× _) ℓ c} {()} {cpair c₂ d₂} {()} (≈-pair c₁≈c₂ c₁≈c₃)

inl-equiv : ∀{A B C D : Type}{c₁ : CastB ((A `⊎ B) ⇒ (C `⊎ D))}{i₁ : CastStruct.Inert sB c₁}
                             {c₂ : CastC ((A `⊎ B) ⇒ (C `⊎ D))}{i₂ : CastStruct.Inert sC c₂}
          → c₁ ≈ c₂ 
          → (CastStruct.inlC sB c₁ i₁) ≈ (CastStruct.inlC sC c₂ i₂)
inl-equiv {c₁ = cast .(_ `⊎ _) .(_ `⊎ _) ℓ c} {()} {csum c₂ d₂} {()} (≈-sum c₁≈c₂ c₁≈c₃)

inr-equiv : ∀{A B C D : Type}{c₁ : CastB ((A `⊎ B) ⇒ (C `⊎ D))}{i₁ : CastStruct.Inert sB c₁}
                             {c₂ : CastC ((A `⊎ B) ⇒ (C `⊎ D))}{i₂ : CastStruct.Inert sC c₂}
          → c₁ ≈ c₂ 
          → (CastStruct.inrC sB c₁ i₁) ≈ (CastStruct.inrC sC c₂ i₂)
inr-equiv {c₁ = cast .(_ `⊎ _) .(_ `⊎ _) ℓ c} {()} {csum c₂ d₂} {()} (≈-sum c₁≈c₂ c₁≈c₃)

module EqBC = EquivBC.Equiv _≈_ inert-equiv active-equiv dom-equiv cod-equiv fst-equiv snd-equiv inl-equiv inr-equiv


open LamB using (`_; _·_; $_; V-ƛ; V-const; V-pair; V-inl; V-inr; V-cast) renaming (rename to rename₁;
       _⊢_ to _⊢₁_; ƛ_ to ƛ₁_; _⟨_⟩ to _⟨_⟩₁;
       if to if₁; cons to cons₁; fst to fst₁; snd to snd₁;
       inl to inl₁; inr to inr₁; case to case₁; blame to blame₁; _[_] to _[_]₁;
       _—→_ to _—→₁_)
open LamC using ()
     renaming (rename to rename₂;
       _⊢_ to _⊢₂_; `_ to ``_; ƛ_ to ƛ₂_; _·_ to _●_; $_ to #_;
       if to if₂; cons to cons₂; fst to fst₂; snd to snd₂; _[_] to _[_]₂;
       inl to inl₂; inr to inr₂; case to case₂; _⟨_⟩ to _⟨_⟩₂;
       blame to blame₂;
       _—→_ to _—→₂_)

open EqBC renaming (_≈_ to _≊_)


ground-eq : ∀{A nA1 nA2 G1 G2 g1 g2 eq1 eq2}
          → ground A {nA1} ≡ ⟨ G1 , ⟨ g1 , eq1 ⟩ ⟩
          → ground A {nA2} ≡ ⟨ G2 , ⟨ g2 , eq2 ⟩ ⟩
          → G1 ≡ G2
ground-eq {⋆}{nA1} eq1 eq2 = ⊥-elim (nA1 refl)
ground-eq {` x} refl refl = refl
ground-eq {A ⇒ A₁} refl refl = refl
ground-eq {A `× A₁} refl refl = refl
ground-eq {A `⊎ A₁} refl refl = refl

ground-unique : ∀{G1 G2 A}{g1 : Ground G1}{g2 : Ground G2} → G1 ~ A → G2 ~ A → A ≢ ⋆ → G1 ≡ G2
ground-unique {G1} {G2} {⋆} {g1} {g2} G1~A G2~A A≢⋆ = ⊥-elim (A≢⋆ refl)
ground-unique {.(` x)} {G2} {` x} {g1} {g2} base~ base~ A≢⋆ = refl
ground-unique {G1} {G2} {A ⇒ A₁} {G-Fun} {G-Fun} G1~A G2~A A≢⋆ = refl
ground-unique {G1} {G2} {A `× A₁} {G-Pair} {G-Pair} G1~A G2~A A≢⋆ = refl
ground-unique {G1} {G2} {A `⊎ A₁} {G-Sum} {G-Sum} G1~A G2~A A≢⋆ = refl

applyCast-equiv : ∀{A B : Type}{M₁ : ∅ ⊢₁ A}{M₂ : ∅ ⊢₂ A}{vM₁ : LamB.Value M₁}{vM₂ : LamC.Value M₂}
                          {c₁ : CastB (A ⇒ B)}{a₁ : CastStruct.Active sB c₁}
                          {c₂ : CastC (A ⇒ B)}{a₂ : CastStruct.Active sC c₂}
              → M₁ ≊ M₂
              → c₁ ≈ c₂
              → CastStruct.applyCast sB M₁ vM₁ c₁ {a₁} ≊ CastStruct.applyCast sC M₂ vM₂ c₂ {a₂}
applyCast-equiv {A} {.A} {_} {_} {vM₁} {vM₂} {.(cast A A _ _)} {A-id .(cast A A _ _)} {.id} {a₂} ≈-lit ≈-id = ≈-lit
applyCast-equiv {A} {.A} {_} {_} {vM₁} {vM₂} {.(cast A A _ _)} {A-id {a = a} .(cast A A _ _)} {.id} {a₂} (≈-cast M₁≅M₂ c≈d) ≈-id =
    ≈-cast M₁≅M₂ c≈d
applyCast-equiv {.⋆} {.⋆} {_} {_} {vM₁} {vM₂} {.(cast ⋆ ⋆ _ _)} {A-id {a = a} .(cast ⋆ ⋆ _ _)} {.(cseq _ _)} {a₂}
    (≈-cast M₁≅M₂ c≈d) (≈-inj-seq {nA = nA} c₁≈c₂ c₁≈c₃) = ⊥-elim (nA refl)
applyCast-equiv {.⋆} {.⋆} {_} {_} {vM₁} {vM₂} {.(cast ⋆ ⋆ _ _)} {A-id {a = a} .(cast ⋆ ⋆ _ _)} {.(cseq _ _)} {a₂}
    (≈-cast M₁≅M₂ c≈d) (≈-proj-seq {nA = nA} c₁≈c₂ c₁≈c₃) = ⊥-elim (nA refl)
applyCast-equiv {.⋆} {.⋆} {M₁} {M₂} {vM₁} {vM₂} {.(cast ⋆ ⋆ x₁ _)} {A-inj (cast .⋆ .⋆ x₁ x₂) x nd} {.id} {a₂} M₁≅M₂ ≈-id =
    ⊥-elim (nd refl)
applyCast-equiv {A} {.⋆} {M₁} {M₂} {vM₁} {vM₂} {.(cast A ⋆ ℓ _)} {A-inj (cast A .⋆ ℓ _) ngA A≢⋆} {.(cseq _ _)} {a₂} M₁≅M₂
    (≈-inj-seq {g = g1}{ag = A~G} c₁≈c₂ c₁≈c₃)
    with ground A {A≢⋆}
... | ⟨ G , ⟨ gG , A~G' ⟩ ⟩
    with ground-unique {g1 = g1}{g2 = gG} (Sym~ A~G) (Sym~ A~G') A≢⋆
... | refl = ≈-cast (≈-cast M₁≅M₂ c₁≈c₂) c₁≈c₃
applyCast-equiv {.⋆} {.⋆} {M₁} {M₂} {vM₁} {vM₂} {.(cast ⋆ ⋆ x₁ _)} {A-inj (cast .⋆ .⋆ x₁ x₂) x nd} {.(cseq _ _)} {a₂} M₁≅M₂
    (≈-proj-seq {nA = nA} c₁≈c₂ c₁≈c₃) = ⊥-elim (nA refl)
applyCast-equiv {.⋆} {.⋆} {M₁} {M₂} {vM₁} {vM₂} {.(cast ⋆ ⋆ x₁ _)} {A-proj (cast .⋆ .⋆ x₁ x₂) B≢⋆} {.id} {a₂} M₁≅M₂ ≈-id =
    ⊥-elim (B≢⋆ refl)
applyCast-equiv {.⋆} {B} {M₁} {M₂} {vM₁} {vM₂} {.(cast ⋆ B x₁ _)} {A-proj (cast .⋆ B x₁ x₂) B≢⋆} {.(proj B x₁)} {a₂} M₁≅M₂ (≈-proj{g = gB})
    with ground? B
... | yes b-g
    with GroundCast.PCR.canonical⋆ M₁ vM₁
... | ⟨ G , ⟨ V , ⟨ c' , ⟨ i , meq ⟩ ⟩ ⟩ ⟩
    with gnd-eq? G B {inert-ground c' i} {b-g}
... | yes ap-b = {!!}
... | no ap-b = {!!}
applyCast-equiv {.⋆} {B} {M₁} {M₂} {vM₁} {vM₂} {.(cast ⋆ B x₁ _)} {A-proj (cast .⋆ B x₁ x₂) B≢⋆} {.(proj B x₁)} {a₂}
    M₁≅M₂ (≈-proj{g = gB})
    | no b-ng = {!!}
applyCast-equiv {.⋆} {.⋆} {M₁} {M₂} {vM₁} {vM₂} {.(cast ⋆ ⋆ x₁ _)} {A-proj (cast .⋆ .⋆ x₁ x₂) B≢⋆} {.(cseq _ _)} {a₂} M₁≅M₂ (≈-inj-seq c₁≈c₂ c₁≈c₃) = {!!}
applyCast-equiv {.⋆} {B} {M₁} {M₂} {vM₁} {vM₂} {.(cast ⋆ B x₁ _)} {A-proj (cast .⋆ B x₁ x₂) B≢⋆} {.(cseq _ _)} {a₂} M₁≅M₂ (≈-proj-seq c₁≈c₂ c₁≈c₃) = {!!}
applyCast-equiv {.(_ `× _)} {.(_ `× _)} {M₁} {M₂} {vM₁} {vM₂} {.(cast (_ `× _) (_ `× _) x _)} {A-pair (cast .(_ `× _) .(_ `× _) x x₁)} {.(cpair _ _)} {a₂} M₁≅M₂ (≈-pair c₁≈c₂ c₁≈c₃) =
    ≈-cons (≈-cast (≈-fst M₁≅M₂) c₁≈c₂) (≈-cast (≈-snd M₁≅M₂) c₁≈c₃)
applyCast-equiv {.(_ `⊎ _)} {.(_ `⊎ _)} {M₁} {M₂} {vM₁} {vM₂} {.(cast (_ `⊎ _) (_ `⊎ _) x _)} {A-sum (cast .(_ `⊎ _) .(_ `⊎ _) x x₁)} {.(csum _ _)} {a₂} M₁≅M₂ (≈-sum c₁≈c₂ c₁≈c₃) =
    ≈-case M₁≅M₂ (≈-lam (≈-inl (≈-cast ≈-var c₁≈c₂))) (≈-lam (≈-inr (≈-cast ≈-var c₁≈c₃)))

{-
applyCast-equiv {vM₁ = V-ƛ} {vM₂} {.(cast (_ ⇒ _) ⋆ _ _)} {A-inj .(cast (_ ⇒ _) ⋆ _ _) x x₁} {.(cseq _ _)} {a₂}
    (≈-lam M₁≅M₂) (≈-inj-seq {G = ⋆ ⇒ ⋆}{ag = fun~ _ _}{unk~R} c₁≈c₂ c₁≈c₃) = ≈-cast (≈-cast (≈-lam M₁≅M₂) c₁≈c₂) c₁≈c₃
applyCast-equiv {vM₁ = V-const} {vM₂} {a₁ = A-id _}{a₂ = a₂} ≈-lit (≈-id {a = A-Base}) = ≈-lit
applyCast-equiv {A} {vM₁ = V-const} {vM₂} {a₁ = A-inj _ _ A≢⋆}{a₂ = a₂} ≈-lit (≈-inj-seq{G = G}{nA = nA}{g = gG}{ag = A~G} c₁≈c₂ c₁≈c₃)
    with ground A {A≢⋆} 
... | ⟨ G1 , ⟨ g1 , ag1 ⟩ ⟩
    with ground-unique {g1 = g1}{g2 = gG} (Sym~ ag1) (Sym~ (A~G)) A≢⋆
... | refl =    
    ≈-cast (≈-cast ≈-lit c₁≈c₂) c₁≈c₃
applyCast-equiv {vM₁ = V-pair vM₁ vM₃} {vM₂}{a₁ = A-pair _}{a₂ = A-pair} (≈-cons M₁≅M₂ M₁≅M₃) (≈-pair c₁≈c₂ c₁≈c₃) =
    ≈-cons (≈-cast (≈-fst (≈-cons M₁≅M₂ M₁≅M₃)) c₁≈c₂) (≈-cast (≈-snd (≈-cons M₁≅M₂ M₁≅M₃)) c₁≈c₃)
applyCast-equiv {A} {vM₁ = V-pair vM₁ vM₃} {vM₂}{a₁ = A-inj _ ng nd}{a₂ = a₂}
    (≈-cons M₁≅M₂ M₁≅M₃) (≈-inj-seq {g = G-Pair}{ag = pair~ _ _} c₁≈c₂ c₁≈c₃)
    with ground A {nd}
... | ⟨ G , ⟨ gG , ag ⟩ ⟩ =    
    ≈-cast (≈-cast (≈-cons M₁≅M₂ M₁≅M₃) c₁≈c₂) c₁≈c₃
applyCast-equiv {vM₁ = V-inl vM₁} {vM₂} (≈-inl M₁≅M₂) (≈-sum c₁≈c₂ c₁≈c₃) = {!!}
applyCast-equiv {A} {vM₁ = V-inl vM₁} {vM₂} {a₁ = A-inj _ ng nd} (≈-inl M₁≅M₂) (≈-inj-seq {g = G-Sum}{ag = sum~ _ _} c₁≈c₂ c₁≈c₃)
    with ground A {nd}
... | ⟨ G , ⟨ gG , ag ⟩ ⟩ =  ≈-cast (≈-cast (≈-inl M₁≅M₂) c₁≈c₂) c₁≈c₃
applyCast-equiv {vM₁ = V-inr vM₁} {vM₂} (≈-inr M₁≅M₂) (≈-sum c₁≈c₂ c₁≈c₃) = {!!}
applyCast-equiv {A} {vM₁ = V-inr vM₁} {vM₂} {a₁ = A-inj _ ng nd} (≈-inr M₁≅M₂) (≈-inj-seq {g = G-Sum}{ag = sum~ _ _} c₁≈c₂ c₁≈c₃)
    with ground A {nd}
... | ⟨ G , ⟨ gG , ag ⟩ ⟩ =  {!!}
applyCast-equiv {vM₁ = V-cast vM₁} {vM₂} M₁≅M₂ c₁≈c₂ = {!!}
-}
