{-# OPTIONS --rewriting #-}
module LogRel.CastCompatibilityDir2 where

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
open import LogRel.CastReduction
open import LogRel.CastPrec2
open import LogRel.CastDeterministic
open import StepIndexedLogic
open import LogRel.CastLogRelDir2
open import LogRel.CastBindDir2

{---------------- Compatibility Lemmas ----------------------------------------}

compatible-nat : ∀{Γ}{n : ℕ}
   → Γ ⊨ $ (Num n) ⊑ $ (Num n) ⦂ ($ₜ ′ℕ , $ₜ ′ℕ , base⊑)
compatible-nat {Γ}{n} =
  (λ γ γ′ → 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))) ,
  (λ γ γ′ → 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl)))

compatible-bool : ∀{Γ}{b : 𝔹}
   → Γ ⊨ $ (Bool b) ⊑ $ (Bool b) ⦂ ($ₜ ′𝔹 , $ₜ ′𝔹 , base⊑)
compatible-bool {Γ}{b} =
  (λ γ γ′ → 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))) ,
  (λ γ γ′ → 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl)))

compatible-blame : ∀{Γ}{A}{M}
   → map proj₁ Γ ⊢ M ⦂ A
     -------------------------------
   → Γ ⊨ M ⊑ blame ⦂ (A , A , Refl⊑)
compatible-blame ⊢M = (λ γ γ′ → ℰ-blame) , (λ γ γ′ → ℰ-blame)

lookup-𝓖 : ∀{dir} (Γ : List Prec) → (γ γ′ : Subst)
  → ∀ {A}{A′}{A⊑A′}{y} → Γ ∋ y ⦂ (A , A′ , A⊑A′)
  → 𝓖⟦ Γ ⟧ dir γ γ′ ⊢ᵒ 𝒱⟦ (A , A′ , A⊑A′) ⟧ dir (γ y) (γ′ y)
lookup-𝓖 {dir} (.(A , A′ , A⊑A′) ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
lookup-𝓖 {dir} (B ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {suc y} ∋y =
   Sᵒ (lookup-𝓖 Γ (λ x → γ (suc x)) (λ x → γ′ (suc x)) ∋y)

compatibility-var : ∀ {Γ A A′ A⊑A′ x}
  → Γ ∋ x ⦂ (A , A′ , A⊑A′)
    -------------------------------
  → Γ ⊨ ` x ⊑ ` x ⦂ (A , A′ , A⊑A′)
compatibility-var {Γ}{A}{A′}{A⊑A′}{x} ∋x = LT , GT
  where
  LT : Γ ∣ ≺ ⊨ ` x ⊑ ` x ⦂ (A , A′ , A⊑A′)
  LT γ γ′ rewrite sub-var γ x | sub-var γ′ x = 𝒱⇒ℰ (lookup-𝓖 Γ γ γ′ ∋x)

  GT : Γ ∣ ≻ ⊨ ` x ⊑ ` x ⦂ (A , A′ , A⊑A′)
  GT γ γ′ rewrite sub-var γ x | sub-var γ′ x = 𝒱⇒ℰ (lookup-𝓖 Γ γ γ′ ∋x)

proj : ∀ {Γ}{c}
  → (dir : Dir)
  → (M M′ : Term)
  → Γ ⊨ M ⊑ M′ ⦂ c
  → Γ ∣ dir ⊨ M ⊑ M′ ⦂ c
proj {Γ} {c} ≺ M M′ M⊑M′ = proj₁ M⊑M′
proj {Γ} {c} ≻ M M′ M⊑M′ = proj₂ M⊑M′

compatible-lambda : ∀{Γ : List Prec}{A}{B}{C}{D}{N N′ : Term}
     {c : A ⊑ C}{d : B ⊑ D}
   → ((A , C , c) ∷ Γ) ⊨ N ⊑ N′ ⦂ (B , D , d)
     ------------------------------------------------
   → Γ ⊨ (ƛ N) ⊑ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ =
  (λ γ γ′ → ⊢ℰλNλN′) , (λ γ γ′ → ⊢ℰλNλN′)
 where
 ⊢ℰλNλN′ : ∀{dir}{γ}{γ′} → 𝓖⟦ Γ ⟧ dir γ γ′
            ⊢ᵒ ℰ⟦ A ⇒ B , C ⇒ D , fun⊑ c d ⟧ dir (⟪ γ ⟫ (ƛ N)) (⟪ γ′ ⟫ (ƛ N′))
 ⊢ℰλNλN′ {dir}{γ}{γ′} =
     𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI ▷𝓔N[W]N′[W′]))
  where
  ▷𝓔N[W]N′[W′] : ∀{W W′} → ▷ᵒ 𝒱⟦ A , C , c ⟧ dir W W′ ∷ 𝓖⟦ Γ ⟧ dir γ γ′
        ⊢ᵒ ▷ᵒ ℰ⟦ B , D , d ⟧ dir ((⟪ ext γ ⟫ N) [ W ]) ((⟪ ext γ′ ⟫ N′) [ W′ ])
  ▷𝓔N[W]N′[W′] {W}{W′} =
      appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI ((proj dir N N′ ⊨N⊑N′) (W • γ) (W′ • γ′)))))) Zᵒ

compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
   → Γ ⊨ M ⊑ M′ ⦂ (A , A′ , c)
     ----------------------------------
   → Γ ⊨ L · M ⊑ L′ · M′ ⦂ (B , B′ , d)
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′} ⊨L⊑L′ ⊨M⊑M′ =
 (λ γ γ′ → ⊢ℰLM⊑LM′) , λ γ γ′ → ⊢ℰLM⊑LM′
 where
 ⊢ℰLM⊑LM′ : ∀{dir}{γ}{γ′} → 𝓖⟦ Γ ⟧ dir γ γ′
                      ⊢ᵒ ℰ⟦ B , B′ , d ⟧ dir (⟪ γ ⟫ (L · M)) (⟪ γ′ ⟫ (L′ · M′))
 ⊢ℰLM⊑LM′ {dir}{γ}{γ′} = ⊢ᵒ-intro λ n 𝒫n →
  ℰ-bind-step{B , B′ , d}{A ⇒ B , A′ ⇒ B′ , fun⊑ c d}
             {F = ` (□· (⟪ γ ⟫ M))}{F′ = ` (□· (⟪ γ′ ⟫ M′))}
  (⊢ᵒ-elim ((proj dir L L′ ⊨L⊑L′) γ γ′) n 𝒫n)
  λ j V V′ j≤n L→V v L′→V′ v′ 𝒱VV′j →
  ℰ-bind-step{B , B′ , d}{A , A′ , c}
             {F = ` (v ·□)}{F′ = ` (v′ ·□)}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) j
   (down (Πᵒ (𝓖⟦ Γ ⟧ dir γ γ′)) n 𝒫n j j≤n))
   λ i W W′ i≤j M→W w M′→W′ w′ 𝒱WW′i →
     Goal{v = v}{v′}{w = w}{w′} i≤j 𝒱VV′j 𝒱WW′i
   where
   Goal : ∀{V}{V′}{v : Value V}{v′ : Value V′}
           {W}{W′}{w : Value W}{w′ : Value W′}{i}{j}
     → i ≤ j
     → # (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′) j
     → # (𝒱⟦ A , A′ , c ⟧ dir W W′) i
     → # (ℰ⟦ B , B′ , d ⟧ dir ((` (v ·□)) ⦉ W ⦊) ((` (v′ ·□)) ⦉ W′ ⦊)) i
   Goal {V} {V′} {v} {v′} {W} {W′} {w}{w′}{zero} {j} i≤j 𝒱VV′j 𝒱WW′i =
     tz (ℰ⟦ B , B′ , d ⟧ dir (value v · W) (value v′ · W′))
   Goal {V} {V′} {v} {v′} {W} {W′} {w}{w′}{suc i} {suc j}
       (s≤s i≤j) 𝒱VV′sj 𝒱WW′si
       with 𝒱-fun-elim-step{A}{B}{A′}{B′}{c}{d}{V}{V′}{dir}{j}{i} 𝒱VV′sj i≤j
   ... | N , N′ , refl , refl , body =
       let 𝒱WW′i = down (𝒱⟦ A , A′ , c ⟧ dir W W′)(suc i)𝒱WW′si i (n≤1+n i) in
       let ℰNWNW′i = body{W}{W′} 𝒱WW′i in
       anti-reduction{B , B′ , d}{i = i}{dir = dir} ℰNWNW′i (β w) (β w′)

compatible-inj-L : ∀{Γ}{G A′}{c : gnd⇒ty G ⊑ A′}{M M′}
   → Γ ⊨ M ⊑ M′ ⦂ (gnd⇒ty G , A′ , c)
     ---------------------------------------------
   → Γ ⊨ M ⟨ G !⟩ ⊑ M′ ⦂ (★ , A′ , unk⊑{G}{A′} c)
compatible-inj-L{Γ}{G}{A′}{c}{M}{M′} ⊨M⊑M′ =
  (λ γ γ′ → ℰMGM′) , (λ γ γ′ → ℰMGM′)
  where
  ℰMGM′ : ∀ {γ}{γ′}{dir}
    → 𝓖⟦ Γ ⟧ dir γ γ′ ⊢ᵒ ℰ⟦ ★ , A′ , unk⊑ c ⟧ dir (⟪ γ ⟫ M ⟨ G !⟩) (⟪ γ′ ⟫ M′)
  ℰMGM′{γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   ℰ-bind-step{★ , A′ , unk⊑ c}{gnd⇒ty G , A′ , c}
              {F = ` (□⟨ G !⟩)}{F′ = □}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
   𝒱⇒ℰ-step{★ , A′ , unk⊑ c}{V ⟨ G !⟩}{V′}{dir}{j}
   (𝒱-dyn-L-step{G}{A′}{c}{V}{V′}{dir}{j} 𝒱VV′j)

compatible-inj-R : ∀{Γ}{G}{c : ★ ⊑ gnd⇒ty G }{M M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , gnd⇒ty G , c)
   → Γ ⊨ M ⊑ M′ ⟨ G !⟩ ⦂ (★ , ★ , unk⊑unk)
compatible-inj-R{Γ}{G}{c}{M}{M′} ⊨M⊑M′
    with unk⊑gnd-inv c
... | d , refl = (λ γ γ′ → ℰMM′G) , λ γ γ′ → ℰMM′G
  where
  ℰMM′G : ∀{γ}{γ′}{dir}
    → 𝓖⟦ Γ ⟧ dir γ γ′ ⊢ᵒ ℰ⟦ ★ , ★ , unk⊑unk ⟧ dir (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′ ⟨ G !⟩)
  ℰMM′G {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   ℰ-bind-step{★ , ★ , unk⊑unk}{★ , gnd⇒ty G , unk⊑ d}
              {F = □}{F′ = ` (□⟨ G !⟩)}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
   𝒱⇒ℰ-step{★ , ★ , unk⊑unk}{V}{V′ ⟨ G !⟩}{dir}{j}
   (𝒱-dyn-R-step{G}{unk⊑ d}{V}{V′}{dir}{j} 𝒱VV′j)

compatible-proj-L : ∀{Γ}{H}{A′}{c : gnd⇒ty H ⊑ A′}{M}{M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , A′ ,  unk⊑ c)
   → Γ ⊨ M ⟨ H ?⟩ ⊑ M′ ⦂ (gnd⇒ty H , A′ , c)
compatible-proj-L {Γ}{H}{A′}{c}{M}{M′} ⊨M⊑M′ =
  (λ γ γ′ → ℰMHM′) , λ γ γ′ → ℰMHM′
  where
  ℰMHM′ : ∀{γ}{γ′}{dir} → 𝓖⟦ Γ ⟧ dir γ γ′
       ⊢ᵒ ℰ⟦ gnd⇒ty H , A′ , c ⟧ dir (⟪ γ ⟫ M ⟨ H ?⟩) (⟪ γ′ ⟫ M′)
  ℰMHM′ {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   ℰ-bind-step{gnd⇒ty H , A′ , c}{★ , A′ , unk⊑ c}
              {F = ` (□⟨ H ?⟩)}{F′ = □}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j → Goal{j}{V}{V′}{dir} 𝒱VV′j 
   where
   Goal : ∀{j}{V}{V′}{dir}
       → #(𝒱⟦ ★ , A′ , unk⊑ c ⟧ dir V V′) j
       → #(ℰ⟦ gnd⇒ty H , A′ , c ⟧ dir (V ⟨ H ?⟩) V′) j
   Goal {zero} {V} {V′}{dir} 𝒱VV′j =
       tz (ℰ⟦ gnd⇒ty H , A′ , c ⟧ dir (V ⟨ H ?⟩) V′)
   Goal {suc j} {V} {V′}{≺} 𝒱VV′j
       with 𝒱-dyn-any-elim-step{V}{V′}{≺}{j}{H}{A′}{c} 𝒱VV′j
   ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′sj =
       let V₁HH→V₁ = collapse{H}{V = V₁} v₁ refl in
       let 𝒱V₁V′j = down (𝒱⟦ gnd⇒ty H , A′ , c ⟧ ≺ V₁ V′) (suc j) 𝒱V₁V′sj
                          j (n≤1+n j) in
       let ℰV₁V′j = 𝒱⇒ℰ-step{gnd⇒ty H , A′ , c}{V₁}{V′}{≺}{j} 𝒱V₁V′j in
       anti-reduction-≺ ℰV₁V′j (unit V₁HH→V₁)
   Goal {suc j} {V} {V′}{≻} 𝒱VV′j
       with 𝒱-dyn-any-elim-step{V}{V′}{≻}{j}{H}{A′}{c} 𝒱VV′j
   ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′sj =
       let V₁HH→V₁ = collapse{H}{V = V₁} v₁ refl in
       inj₂ (inj₂ (v′ , V₁ , unit V₁HH→V₁ , v₁ , 𝒱V₁V′sj))

compatible-proj-R : ∀{Γ}{H}{c : ★ ⊑ gnd⇒ty H}{M}{M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , ★ , unk⊑unk)
   → Γ ⊨ M ⊑ M′ ⟨ H ?⟩ ⦂ (★ , gnd⇒ty H , c)
compatible-proj-R {Γ}{H}{c}{M}{M′} ⊨M⊑M′
    with unk⊑gnd-inv c
... | d , refl = (λ γ γ′ → ℰMM′H) , λ γ γ′ → ℰMM′H
    where
    ℰMM′H : ∀{γ}{γ′}{dir} → 𝓖⟦ Γ ⟧ dir γ γ′
        ⊢ᵒ ℰ⟦ ★ , gnd⇒ty H , unk⊑ d ⟧ dir (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′ ⟨ H ?⟩)
    ℰMM′H {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
     ℰ-bind-step{★ , gnd⇒ty H , c}{★ , ★ , unk⊑unk}
                {F = □}{F′ = ` □⟨ H ?⟩}
                {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
     (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
     λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
     Goal {j}{V}{V′}{dir} 𝒱VV′j 
     where
     {-
        M′⟨ H ?⟩  -->*   V′⟨ G !⟩⟨ H ?⟩  --> V′     if G = H
        ⊑                                --> blame  if G ≠ H
        M         -->*   V ⟨ G !⟩
     -}
     Goal : ∀{j}{V}{V′}{dir}
        → # (𝒱⟦ ★ , ★ , unk⊑unk ⟧ dir V V′) j
        → # (ℰ⟦ ★ , gnd⇒ty H , unk⊑ d ⟧ dir V (V′ ⟨ H ?⟩)) j
     Goal {zero} {V} {V′}{dir} 𝒱VV′j =
         tz (ℰ⟦ ★ , gnd⇒ty H , unk⊑ d ⟧ dir V (V′ ⟨ H ?⟩))
     Goal {suc j} {V ⟨ G !⟩} {V′ ⟨ H₂ !⟩}{dir} 𝒱VV′j
         with G ≡ᵍ H₂ | 𝒱VV′j
     ... | no neq | ()
     ... | yes refl | v , v′ , 𝒱VV′
         with G ≡ᵍ G
     ... | no neq = ⊥-elim (neq refl)
     ... | yes refl
         with G ≡ᵍ H
     ... | no neq
         with dir
     ... | ≺ = inj₂ (inj₁ (unit (collide v′ neq refl)))
     ... | ≻ = 
         anti-reduction-≻ (ℰ-blame-step{★ , gnd⇒ty H , unk⊑ d}{≻})
                          (unit (collide v′ neq refl))
     Goal {suc j} {V ⟨ G !⟩} {V′ ⟨ H₂ !⟩}{dir} 𝒱VV′j
         | yes refl | v , v′ , 𝒱VV′ | yes refl
         | yes refl 
         with dir
     ... | ≺
         with G ≡ᵍ G
     ... | no neq = ⊥-elim (neq refl)
     ... | yes refl 
         with gnd-prec-unique d Refl⊑
     ... | refl =
           let x = {!!} in
           let 𝒱VV′j : # (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ ≺ V V′) j
               𝒱VV′j = 𝒱VV′ in
           let 𝒱VV′sj : # (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ ≺ V V′) (suc j)
               𝒱VV′sj = {!!} in
           --𝒱⇒ℰ-step{★ , gnd⇒ty G , unk⊑ d}{V ⟨ G !⟩}{V′ ⟨ G !⟩ ⟨ G ?⟩}{≺} {!!}
           let ℰVGV′GG : # (ℰ⟦ ★ , gnd⇒ty H , unk⊑ d ⟧ ≺
                                 (V ⟨ G !⟩) (V′ ⟨ G !⟩ ⟨ G ?⟩)) (suc j )
               ℰVGV′GG = {!!} in
           {!ℰVGV′GG!}
{-  
           inj₂ (inj₂ ((v 〈 G 〉) , inj₂ (V′ , unit (collapse v′ refl) , v′ ,
               v , v′ , 𝒱VV′sj)))
-}               
     Goal {suc j} {V ⟨ G !⟩} {V′ ⟨ H₂ !⟩}{dir} 𝒱VV′j
         | yes refl | v , v′ , 𝒱VV′ | yes refl
         | yes refl 
         | ≻
         with gnd-prec-unique d Refl⊑
     ... | refl =
         let 𝒱VGV′ = 𝒱-dyn-L-step{G}{gnd⇒ty G}{d} 𝒱VV′ in
         anti-reduction-≻ (𝒱⇒ℰ-step{V = V ⟨ G !⟩}{V′}{≻} 𝒱VGV′)
                          (unit (collapse v′ refl))
     
