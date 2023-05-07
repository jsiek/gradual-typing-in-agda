{-# OPTIONS --rewriting #-}
module LogRel.CastGradualGuarantee where

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
open import LogRel.Cast
open import LogRel.CastDeterministic
open import StepIndexedLogic
open import LogRel.CastLogRel

{-
 Analogous to sem-type-safety.
-}

ℰ-steps : ∀{c : Prec}
    (k : ℕ)
  → (M M′ : Term)
  → #(ℰ⟦ c ⟧ M M′) (suc k)
  → (∃[ V ] ∃[ V′ ] Σ[ M→V ∈ M —↠ V ] Σ[ M′→V′ ∈ M′ —↠ V′ ]
        (len M→V + len M′→V′ ≤ k) × ∃[ m ] #(𝒱⟦ c ⟧ V V′) (suc m))
    ⊎ (M′ —↠ blame)
    ⊎ (∃[ N ] ∃[ N′ ]  Σ[ M→N ∈ M —↠ N ] Σ[ M′→N′ ∈ M′ —↠ N′ ]
        len M→N + len M′→N′ ≡ k)
ℰ-steps {c} zero M M′ ℰMM′sk
    with ⇔-to (ℰ-suc{c}{k = 0}) ℰMM′sk
... | inj₁ 𝒱MM′ =
      inj₁ (M , M′ , (M END) , (M′ END) , ≤-refl , zero , 𝒱MM′ )
... | inj₂ (inj₁ ((N , M→N) , presL)) =
      inj₂ (inj₂ (M , M′ , (M END) , (M′ END) , refl))
... | inj₂ (inj₂ (inj₁ ((N′ , M′→N′) , presR))) =
      inj₂ (inj₂ (M , M′ , (M END) , (M′ END) , refl))
... | inj₂ (inj₂ (inj₂ isBlame)) = 
      inj₂ (inj₁ (blame END))
ℰ-steps {c} (suc k) M M′ ℰMM′sk
    with ⇔-to (ℰ-suc{c}{k = suc k}) ℰMM′sk
... | inj₁ 𝒱MM′ =
      inj₁ (M , M′ , (M END) , (M′ END) , z≤n , suc k , 𝒱MM′)
... | inj₂ (inj₂ (inj₂ isBlame)) =
      inj₂ (inj₁ (blame END))
... | inj₂ (inj₁ ((N , M→N) , presL))
    with ℰ-steps k N M′ (presL N (suc (suc k)) ≤-refl M→N)
... | inj₁ (V , V′ , N→V , M′→V′ , lt , m , 𝒱VV′) =
     inj₁ (V , V′ , (M —→⟨ M→N ⟩ N→V) , M′→V′ , s≤s lt , m , 𝒱VV′)
... | inj₂ (inj₁ M′→blame) = inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (L , L′ , N→L , M′→L′ , eq)) =
      inj₂ (inj₂ (L , L′ , (M —→⟨ M→N ⟩ N→L) , M′→L′ , cong suc eq))
ℰ-steps {c} (suc k) M M′ ℰMM′sk
    | inj₂ (inj₂ (inj₁ ((N′ , M′→N′) , presR)))
    with ℰ-steps k M N′ (presR N′ (suc (suc k)) ≤-refl M′→N′)
... | inj₁ (V , V′ , M→V , N′→V′ , lt , m , 𝒱VV′) =
      inj₁ (V , V′ , M→V , (M′ —→⟨ M′→N′ ⟩ N′→V′) , LT , m , 𝒱VV′)
      where
      LT : len M→V + suc (len N′→V′) ≤ suc k
      LT = ≤-trans (≤-reflexive (+-suc (len M→V) (len N′→V′))) (s≤s lt)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′ —→⟨ M′→N′ ⟩ N′→blame))
... | inj₂ (inj₂ (L , L′ , M→L , N′→L , refl)) =
      inj₂ (inj₂ (L , L′ , M→L , (M′ —→⟨ M′→N′ ⟩ N′→L) ,
                  +-suc (len M→L) (len N′→L) ))





