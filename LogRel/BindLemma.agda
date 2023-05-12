{-# OPTIONS --rewriting #-}
module LogRel.BindLemma where

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
open import InjProj.Precision
open import InjProj.CastDeterministic
open import StepIndexedLogic
open import InjProj.CastSafe
open import LogRel.LogRel

LRᵥ→LRₜ-down-one-≺ : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}
                      {F}{F′}{i}{M}{N}{M′}
   → M —→ N
   → (∀ j V V′ → j ≤ suc i → M —↠ V → Value V → M′ —↠ V′ → Value V′
       → # (≺ ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
       → # (≺ ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
   → (∀ j V V′ → j ≤ i → N —↠ V → Value V → M′ —↠ V′ → Value V′
       →  # (≺ ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
       → # (≺ ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
LRᵥ→LRₜ-down-one-≺ {B}{B′}{c}{A}{A′}{d}{F}{F′}{i}{M}{N}{M′} M→N LRᵥ→LRₜsi
   j V V′ j≤i M→V v M′→V′ v′ 𝒱j =
   LRᵥ→LRₜsi j V V′ (≤-trans j≤i (n≤1+n i)) (M —→⟨ M→N ⟩ M→V) v M′→V′ v′ 𝒱j

LRᵥ→LRₜ-down-one-≻ : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}
                       {F}{F′}{i}{M}{M′}{N′}
   → M′ —→ N′
   → (∀ j V V′ → j ≤ suc i → M —↠ V → Value V → M′ —↠ V′ → Value V′
       → # (≻ ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
       → # (≻ ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
   → (∀ j V V′ → j ≤ i → M —↠ V → Value V → N′ —↠ V′ → Value V′
       →  # (≻ ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
       → # (≻ ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
LRᵥ→LRₜ-down-one-≻ {B}{B′}{c}{A}{A′}{d}{F}{F′}{i}{M}{N}{M′} M′→N′ LRᵥ→LRₜsi
   j V V′ j≤i M→V v M′→V′ v′ 𝒱j =
   LRᵥ→LRₜsi j V V′ (≤-trans j≤i (n≤1+n i)) M→V v (N —→⟨ M′→N′ ⟩ M′→V′) v′ 𝒱j

LRₜ-bind-step : ∀{B}{B′}{c : B ⊑ B′}{A}{A′}{d : A ⊑ A′}
                 {F}{F′}{M}{M′}{i}{dir}
   → #(dir ∣ M ⊑ᴸᴿₜ M′ ⦂ d) i
   → (∀ j V V′ → j ≤ i → M —↠ V → Value V → M′ —↠ V′ → Value V′
         → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ d) j
         → #(dir ∣ (F ⦉ V ⦊) ⊑ᴸᴿₜ (F′ ⦉ V′ ⦊) ⦂ c) j)
   → #(dir ∣ (F ⦉ M ⦊) ⊑ᴸᴿₜ (F′ ⦉ M′ ⦊) ⦂ c) i
LRₜ-bind-step {B}{B′}{c}{A}{A′}{d}{F} {F′} {M} {M′} {zero} {dir} ℰMM′sz LRᵥ→LRₜj =
    tz (dir ∣ (F ⦉ M ⦊) ⊑ᴸᴿₜ (F′ ⦉ M′ ⦊) ⦂ c)
LRₜ-bind-step {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≺} ℰMM′si LRᵥ→LRₜj
    with ⇔-to (LRₜ-suc{dir = ≺}) ℰMM′si
... | inj₁ (N , M→N , ▷ℰNM′) =
     let IH = LRₜ-bind-step{c = c}{d = d}{F}{F′}{N}{M′}{i}{≺} ▷ℰNM′
                (LRᵥ→LRₜ-down-one-≺{c = c}{d = d}{F}{F′}{i}{M}{N}{M′}
                     M→N LRᵥ→LRₜj) in
      ⇔-fro (LRₜ-suc{dir = ≺}) (inj₁ ((F ⦉ N ⦊) , ξ′ F refl refl M→N , IH))
... | inj₂ (inj₂ (m , inj₁ M′→blame)) = inj₂ (inj₁ (ξ-blame₃ F′ M′→blame refl))
LRₜ-bind-step {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≺} ℰMM′si LRᵥ→LRₜj 
    | inj₂ (inj₂ (m , inj₂ (V′ , M′→V′ , v′ , 𝒱MV′))) =
      let ℰFMF′V′ = LRᵥ→LRₜj (suc i) M V′ ≤-refl (M END) m M′→V′ v′ 𝒱MV′ in
      anti-reduction-≺-R ℰFMF′V′ (ξ′* F′ M′→V′)
LRₜ-bind-step {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≺} ℰMM′si LRᵥ→LRₜj 
    | inj₂ (inj₁ M′→blame) = inj₂ (inj₁ (ξ-blame₃ F′ M′→blame refl))
LRₜ-bind-step {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≻} ℰMM′si LRᵥ→LRₜj 
    with ⇔-to (LRₜ-suc{dir = ≻}) ℰMM′si
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      let ℰFMFN′ : # (≻ ∣ (F ⦉ M ⦊) ⊑ᴸᴿₜ (F′ ⦉ N′ ⦊) ⦂ c) i
          ℰFMFN′ = LRₜ-bind-step{c = c}{d = d}{F}{F′}{M}{N′}{i}{≻} ▷ℰMN′ 
                   (LRᵥ→LRₜ-down-one-≻{c = c}{d = d}{F}{F′} M′→N′ LRᵥ→LRₜj) in
      inj₁ ((F′ ⦉ N′ ⦊) , (ξ′ F′ refl refl M′→N′) , ℰFMFN′)
... | inj₂ (inj₁ isBlame)
    with F′
... | □ = inj₂ (inj₁ isBlame)
... | ` F″ = inj₁ (blame , ξ-blame F″ , LRₜ-blame-step{dir = ≻})
LRₜ-bind-step {B}{B′}{c}{A}{A′}{d}{F}{F′}{M}{M′}{suc i}{≻} ℰMM′si LRᵥ→LRₜj 
    | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱VM′)) =
    let xx = LRᵥ→LRₜj (suc i) V M′ ≤-refl M→V v (M′ END) m′ 𝒱VM′ in
    anti-reduction-≻-L xx (ξ′* F M→V)
