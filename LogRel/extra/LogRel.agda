{-# OPTIONS --rewriting #-}
module LogRel.extra.LogRel where

{-

Stuff that is true and might be handy in the future, but wasn't needed
for the proof of the gradual guarantee.

-}

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import InjProj.CastCalculus
open import InjProj.CastDeterministic
open import InjProj.Reduction
open import InjProj.Precision
open import StepIndexedLogic
open import LogRel.LogRel

𝒱-dyn-any-≺ : ∀{V}{V′}{G}{A′}{d : gnd⇒ty G ⊑ A′}
   → 𝒱⟦ ★ , A′ , unk⊑{G}{A′} d ⟧ ≺ (V ⟨ G !⟩) V′ 
     ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≺ V V′)
𝒱-dyn-any-≺ {V}{V′}{G}{A′}{d} = 
  𝒱⟦ ★ , A′ , unk⊑ d ⟧ ≺ (V ⟨ G !⟩) V′
     ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X
    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X  ⟩
  # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
    ⩦⟨ Goal ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≺ V V′)
  ∎
  where
  X = inj₁ ((★ , A′ , unk⊑ d) , ≺ , (V ⟨ G !⟩) , V′)
  Goal : # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
         ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≺ V V′)
  Goal
      with G ≡ᵍ G
  ... | yes refl = (≡ᵒ-refl refl)
  ... | no neq = ⊥-elim (neq refl)

𝒱-dyn-any-≻ : ∀{V}{V′}{G}{A′}{d : gnd⇒ty G ⊑ A′}
   → 𝒱⟦ ★ , A′ , unk⊑{G}{A′} d ⟧ ≻ (V ⟨ G !⟩) V′ 
     ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≻ V V′)
𝒱-dyn-any-≻ {V}{V′}{G}{A′}{d} = 
  𝒱⟦ ★ , A′ , unk⊑ d ⟧ ≻ (V ⟨ G !⟩) V′
     ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X
    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X  ⟩
  # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
    ⩦⟨ Goal ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≻ V V′)
  ∎
  where
  X = inj₁ ((★ , A′ , unk⊑ d) , ≻ , (V ⟨ G !⟩) , V′)
  Goal : # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
         ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≻ V V′)
  Goal
      with G ≡ᵍ G
  ... | yes refl = cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
            (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱
                        (inj₁ ((gnd⇒ty G , A′ , d) , ≻ , V , V′)))))
  ... | no neq = ⊥-elim (neq refl)

reduction-≺ : ∀{c}{M}{N}{M′}{i}
  → #(ℰ⟦ c ⟧ ≺ M M′) (suc i)
  → (M→N : M —→ N)
  → #(ℰ⟦ c ⟧ ≺ N M′) i
reduction-≺ {c} {M} {N} {M′} {zero} ℰMM′si M→N = tz (ℰ⟦ c ⟧ ≺ N M′)
reduction-≺ {c} {M} {N} {M′} {suc i} ℰMM′ssi M→N
    with ℰMM′ssi
... | inj₁ (N₂ , M→N₂ , ▷ℰN₂M′) rewrite deterministic M→N M→N₂ = ▷ℰN₂M′
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (m , _)) =
      ⊥-elim (value-irreducible m M→N)

reduction*-≺ : ∀{c}{M}{N}{M′}{i}
  → (M→N : M —↠ N)
  → #(ℰ⟦ c ⟧ ≺ M M′) (len M→N + i)
  → #(ℰ⟦ c ⟧ ≺ N M′) i
reduction*-≺ {c} {M} {.M} {M′} {i} (.M END) ℰMM′ = ℰMM′
reduction*-≺ {c} {M} {N} {M′} {i} (.M —→⟨ M→L ⟩ L→N) ℰMM′ =
  let ℰLM′ = reduction-≺ ℰMM′ M→L in
  reduction*-≺ L→N ℰLM′ 

reduction-≻ : ∀{c}{M}{N}{M′}{i}
  → #(ℰ⟦ c ⟧ ≻ M M′) (suc i)
  → (M→N : M —→ N)
  → #(ℰ⟦ c ⟧ ≻ N M′) i
reduction-≻ {c} {M} {N} {M′} {zero} ℰMM′si M→N = tz (ℰ⟦ c ⟧ ≻ N M′)
reduction-≻ {c} {M} {N} {M′} {suc i} ℰMM′si M→N
    with ℰMM′si
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      inj₁ (N′ , M′→N′ , reduction-≻ ▷ℰMN′ M→N)
... | inj₂ (inj₁ M′→blame) = inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (m′ , V , (.V END) , v , 𝒱VM′)) =
      ⊥-elim (value-irreducible v M→N)
... | inj₂ (inj₂ (m′ , V , (.M —→⟨ M→M₁ ⟩ M₁→V) , v , 𝒱VM′))
    with deterministic M→N M→M₁
... | refl =
    let 𝒱VM′si = down (𝒱⟦ c ⟧ ≻ V M′) (suc (suc i)) 𝒱VM′ (suc i) (n≤1+n _) in
    inj₂ (inj₂ (m′ , V , M₁→V , v , 𝒱VM′si)) 

ℰ-reduction : ∀{c}{M}{N}{M′}{i}{dir}
  → #(ℰ⟦ c ⟧ dir M M′) (suc i)
  → (M→N : M —→ N)
  → #(ℰ⟦ c ⟧ dir N M′) i
ℰ-reduction {c} {M} {N} {M′} {i} {≺} ℰMM′ M→N = reduction-≺ ℰMM′ M→N
ℰ-reduction {c} {M} {N} {M′} {i} {≻} ℰMM′ M→N = reduction-≻ ℰMM′ M→N

anti-reduction-≺ : ∀{c}{M}{N}{M′}{i}
  → #(ℰ⟦ c ⟧ ≺ N M′) i
  → (M→N : M —↠ N)
  → #(ℰ⟦ c ⟧ ≺ M M′) (len M→N + i)
anti-reduction-≺ {c} {M} {.M} {M′} {i} ℰ≺NM′si (.M END) = ℰ≺NM′si
anti-reduction-≺ {c} {M} {N} {M′} {i} ℰ≺NM′si (_—→⟨_⟩_ M {L}{N} M→L L→*N) =
  let IH : # (ℰ⟦ c ⟧ ≺ L M′) (len L→*N + i)
      IH = anti-reduction-≺ ℰ≺NM′si (L→*N) in
  inj₁ (L , M→L , IH)

anti-reduction-≻ : ∀{c}{M}{M′}{N′}{i}
  → #(ℰ⟦ c ⟧ ≻ M N′) i
  → (M′→N′ : M′ —↠ N′)
  → #(ℰ⟦ c ⟧ ≻ M M′) (len M′→N′ + i)
anti-reduction-≻ {c} {M} {M′} {.M′} {i} ℰ≻MN′ (.M′ END) = ℰ≻MN′
anti-reduction-≻ {c} {M} {M′}{N′} {i} ℰ≻MN′ (_—→⟨_⟩_ M′ {L′}{N′} M′→L′ L′→*N′)=
  let IH : # (ℰ⟦ c ⟧ ≻ M L′) (len L′→*N′ + i)
      IH = anti-reduction-≻ ℰ≻MN′ (L′→*N′) in
  inj₁ (L′ , M′→L′ , IH)
