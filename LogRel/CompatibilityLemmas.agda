{-# OPTIONS --rewriting #-}
module LogRel.CompatibilityLemmas where

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
open import InjProj.Reduction
open import InjProj.Precision
open import InjProj.CastDeterministic
open import StepIndexedLogic
open import LogRel.LogRel
open import LogRel.BindLemma

{---------------- Compatibility Lemmas ----------------------------------------}

compatible-literal : ∀{Γ}{c}{ι}
   → Γ ⊨ $ c ⊑ᴸᴿ $ c ⦂ ($ₜ ι , $ₜ ι , base⊑)
compatible-literal {Γ}{c}{ι} =
  (λ γ γ′ → LRᵥ⇒LRₜ LRᵥ-base-intro) , (λ γ γ′ → LRᵥ⇒LRₜ LRᵥ-base-intro)

compatible-blame : ∀{Γ}{A}{M}
   → map proj₁ Γ ⊢ M ⦂ A
     -------------------------------
   → Γ ⊨ M ⊑ᴸᴿ blame ⦂ (A , A , Refl⊑)
compatible-blame{Γ}{A}{M} ⊢M = (λ γ γ′ → LRₜ-blame) , (λ γ γ′ → LRₜ-blame)

lookup-⊑ᴸᴿ : ∀{dir} (Γ : List Prec) → (γ γ′ : Subst)
  → ∀ {A}{A′}{A⊑A′}{y} → Γ ∋ y ⦂ (A , A′ , A⊑A′)
  → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ (γ y) ⊑ᴸᴿᵥ (γ′ y) ⦂ A⊑A′
lookup-⊑ᴸᴿ {dir} (.(A , A′ , A⊑A′) ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
lookup-⊑ᴸᴿ {dir} (B ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {suc y} ∋y =
   Sᵒ (lookup-⊑ᴸᴿ Γ (λ x → γ (suc x)) (λ x → γ′ (suc x)) ∋y)

compatibility-var : ∀ {Γ A A′ A⊑A′ x}
  → Γ ∋ x ⦂ (A , A′ , A⊑A′)
    -------------------------------
  → Γ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
compatibility-var {Γ}{A}{A′}{A⊑A′}{x} ∋x = LT , GT
  where
  LT : Γ ∣ ≼ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
  LT γ γ′ rewrite sub-var γ x | sub-var γ′ x = LRᵥ⇒LRₜ (lookup-⊑ᴸᴿ Γ γ γ′ ∋x)

  GT : Γ ∣ ≽ ⊨ ` x ⊑ᴸᴿ ` x ⦂ (A , A′ , A⊑A′)
  GT γ γ′ rewrite sub-var γ x | sub-var γ′ x = LRᵥ⇒LRₜ (lookup-⊑ᴸᴿ Γ γ γ′ ∋x)

compatible-lambda : ∀{Γ : List Prec}{A}{B}{C}{D}{N N′ : Term}
     {c : A ⊑ C}{d : B ⊑ D}
   → ((A , C , c) ∷ Γ) ⊨ N ⊑ᴸᴿ N′ ⦂ (B , D , d)
     ------------------------------------------------
   → Γ ⊨ (ƛ N) ⊑ᴸᴿ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ =
  (λ γ γ′ → ⊢ℰλNλN′) , (λ γ γ′ → ⊢ℰλNλN′)
 where
 ⊢ℰλNλN′ : ∀{dir}{γ}{γ′} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
            ⊢ᵒ (dir ∣ (⟪ γ ⟫ (ƛ N)) ⊑ᴸᴿₜ (⟪ γ′ ⟫ (ƛ N′)) ⦂ fun⊑ c d)
 ⊢ℰλNλN′ {dir}{γ}{γ′} =
     {- This case is easier to prove using the step-indexed logic -}
     LRᵥ⇒LRₜ (substᵒ (≡ᵒ-sym LRᵥ-fun)
          (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI {P = ▷ᵒ (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c)}
            (appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI ((proj dir N N′ ⊨N⊑N′)
                                            (W • γ) (W′ • γ′))))))
                  Zᵒ)))

compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ᴸᴿ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (A , A′ , c)
     ----------------------------------
   → Γ ⊨ L · M ⊑ᴸᴿ L′ · M′ ⦂ (B , B′ , d)
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′} ⊨L⊑L′ ⊨M⊑M′ =
 (λ γ γ′ → ⊢ℰLM⊑LM′) , λ γ γ′ → ⊢ℰLM⊑LM′
 where
 ⊢ℰLM⊑LM′ : ∀{dir}{γ}{γ′} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
                             ⊢ᵒ dir ∣ ⟪ γ ⟫ (L · M) ⊑ᴸᴿₜ ⟪ γ′ ⟫ (L′ · M′) ⦂ d
 ⊢ℰLM⊑LM′ {dir}{γ}{γ′} = ⊢ᵒ-intro λ n 𝒫n →
  LRₜ-bind{c = d}{d = fun⊑ c d}
               {F = ` (□· (⟪ γ ⟫ M))}{F′ = ` (□· (⟪ γ′ ⟫ M′))}
  (⊢ᵒ-elim ((proj dir L L′ ⊨L⊑L′) γ γ′) n 𝒫n)
  λ j V V′ j≤n L→V v L′→V′ v′ 𝒱VV′j →
  LRₜ-bind{c = d}{d = c}{F = ` (v ·□)}{F′ = ` (v′ ·□)}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) j
   (down (Πᵒ (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)) n 𝒫n j j≤n))
   λ i W W′ i≤j M→W w M′→W′ w′ 𝒱WW′i →
     Goal{v = v}{v′}{w = w}{w′} i≤j 𝒱VV′j 𝒱WW′i
   where
   Goal : ∀{V}{V′}{v : Value V}{v′ : Value V′}
           {W}{W′}{w : Value W}{w′ : Value W′}{i}{j}
     → i ≤ j
     → # (dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ fun⊑ c d) j
     → # (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c) i
     → # (dir ∣ V · W ⊑ᴸᴿₜ V′ · W′ ⦂ d) i
   Goal {V} {V′} {v} {v′} {W} {W′} {w}{w′}{zero} {j} i≤j 𝒱VV′j 𝒱WW′i =
     tz (dir ∣ (value v · W) ⊑ᴸᴿₜ (value v′ · W′) ⦂ d)
   Goal {V} {V′} {v} {v′} {W} {W′} {w}{w′}{suc i} {suc j}
       (s≤s i≤j) 𝒱VV′sj 𝒱WW′si
       with LRᵥ-fun-elim-step{A}{B}{A′}{B′}{c}{d}{V}{V′}{dir}{j}{i} 𝒱VV′sj i≤j
   ... | N , N′ , refl , refl , body =
       let 𝒱WW′i = down (dir ∣ W ⊑ᴸᴿᵥ W′ ⦂ c)(suc i)𝒱WW′si i (n≤1+n i) in
       let ℰNWNW′i = body{W}{W′} 𝒱WW′i in
       anti-reduction{c = d}{i = i}{dir = dir} ℰNWNW′i (β w) (β w′)

compatible-inj-L : ∀{Γ}{G A′}{c : gnd⇒ty G ⊑ A′}{M M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (gnd⇒ty G , A′ , c)
     ---------------------------------------------
   → Γ ⊨ M ⟨ G !⟩ ⊑ᴸᴿ M′ ⦂ (★ , A′ , unk⊑{G}{A′} c)
compatible-inj-L{Γ}{G}{A′}{c}{M}{M′} ⊨M⊑M′ =
  (λ γ γ′ → ℰMGM′) , (λ γ γ′ → ℰMGM′)
  where
  ℰMGM′ : ∀ {γ}{γ′}{dir}
   → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ (dir ∣ (⟪ γ ⟫ M ⟨ G !⟩) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′) ⦂ unk⊑ c)
  ℰMGM′{γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   LRₜ-bind{c = unk⊑ c}{d = c}{F = ` (□⟨ G !⟩)}{F′ = □}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
   LRᵥ⇒LRₜ-step{★}{A′}{unk⊑ c}{V ⟨ G !⟩}{V′}{dir}{j}
   (LRᵥ-inject-L-intro{G}{A′}{c}{V}{V′}{dir}{j} 𝒱VV′j)

compatible-inj-R : ∀{Γ}{G}{c : ★ ⊑ gnd⇒ty G }{M M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , gnd⇒ty G , c)
   → Γ ⊨ M ⊑ᴸᴿ M′ ⟨ G !⟩ ⦂ (★ , ★ , unk⊑unk)
compatible-inj-R{Γ}{G}{c}{M}{M′} ⊨M⊑M′
    with unk⊑gnd-inv c
... | d , refl = (λ γ γ′ → ℰMM′G) , λ γ γ′ → ℰMM′G
  where
  ℰMM′G : ∀{γ}{γ′}{dir}
    → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′) ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′ ⟨ G !⟩) ⦂ unk⊑unk
  ℰMM′G {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   LRₜ-bind{c = unk⊑unk}{d = unk⊑ d}{F = □}{F′ = ` (□⟨ G !⟩)}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
   LRᵥ⇒LRₜ-step{★}{★}{unk⊑unk}{V}{V′ ⟨ G !⟩}{dir}{j}
   (LRᵥ-inject-R-intro{G}{unk⊑ d}{V}{V′}{j} 𝒱VV′j )

compatible-proj-L : ∀{Γ}{H}{A′}{c : gnd⇒ty H ⊑ A′}{M}{M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , A′ ,  unk⊑ c)
   → Γ ⊨ M ⟨ H ?⟩ ⊑ᴸᴿ M′ ⦂ (gnd⇒ty H , A′ , c)
compatible-proj-L {Γ}{H}{A′}{c}{M}{M′} ⊨M⊑M′ =
  (λ γ γ′ → ℰMHM′) , λ γ γ′ → ℰMHM′
  where
  ℰMHM′ : ∀{γ}{γ′}{dir} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
       ⊢ᵒ dir ∣ (⟪ γ ⟫ M ⟨ H ?⟩) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′) ⦂ c
  ℰMHM′ {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
   LRₜ-bind{c = c}{d = unk⊑ c}{F = ` (□⟨ H ?⟩)}{F′ = □}
              {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
   (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
   λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j → Goal{j}{V}{V′}{dir} 𝒱VV′j 
   where
   Goal : ∀{j}{V}{V′}{dir}
       → #(dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑ c) j
       → #(dir ∣ (V ⟨ H ?⟩) ⊑ᴸᴿₜ V′ ⦂ c) j
   Goal {zero} {V} {V′}{dir} 𝒱VV′j =
       tz (dir ∣ (V ⟨ H ?⟩) ⊑ᴸᴿₜ V′ ⦂ c)
   Goal {suc j} {V} {V′}{≼} 𝒱VV′sj
       with LRᵥ-dyn-any-elim-≼{V}{V′}{j}{H}{A′}{c} 𝒱VV′sj
   ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′j =
       let ℰV₁V′j = LRᵥ⇒LRₜ-step{gnd⇒ty H}{A′}{c}{V₁}{V′}{≼}{j} 𝒱V₁V′j in
       let V₁HH→V₁ = collapse{H}{V = V₁} v₁ refl in
       anti-reduction-≼-L-one ℰV₁V′j V₁HH→V₁
   Goal {suc j} {V} {V′}{≽} 𝒱VV′sj
       with LRᵥ-dyn-any-elim-≽{V}{V′}{j}{H}{A′}{c} 𝒱VV′sj
   ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′sj =
      {-
         have:
         ≽ ∣ V₁⟨ H !⟩         ⊑ᵥ  V′     at (suc j)     (1)

         need to show
         ≽ ∣ V₁⟨ H !⟩⟨ H ?⟩   ⊑ₜ  V′     at (suc j)

         We unfold the definition of ⊑ₜ in the ≽ direction and note that
         V′ is a value and 
         V₁⟨ H !⟩⟨ H ?⟩   -->  V₁
         So it remains to prove that
         V₁               ⊑ᵥ  V′         at (suc j)
         which we have by this definition and (1).

      -}
       let V₁HH→V₁ = collapse{H}{V = V₁} v₁ refl in
       inj₂ (inj₂ (v′ , V₁ , unit V₁HH→V₁ , v₁ , 𝒱V₁V′sj))

compatible-proj-R : ∀{Γ}{H}{c : ★ ⊑ gnd⇒ty H}{M}{M′}
   → Γ ⊨ M ⊑ᴸᴿ M′ ⦂ (★ , ★ , unk⊑unk)
   → Γ ⊨ M ⊑ᴸᴿ M′ ⟨ H ?⟩ ⦂ (★ , gnd⇒ty H , c)
compatible-proj-R {Γ}{H}{c}{M}{M′} ⊨M⊑M′
    with unk⊑gnd-inv c
... | d , refl = (λ γ γ′ → ℰMM′H) , λ γ γ′ → ℰMM′H
    where
    ℰMM′H : ∀{γ}{γ′}{dir} → (Γ ∣ dir ⊨ γ ⊑ᴸᴿ γ′)
             ⊢ᵒ dir ∣ (⟪ γ ⟫ M) ⊑ᴸᴿₜ (⟪ γ′ ⟫ M′ ⟨ H ?⟩) ⦂ unk⊑ d
    ℰMM′H {γ}{γ′}{dir} = ⊢ᵒ-intro λ n 𝒫n →
     LRₜ-bind{c = c}{d = unk⊑unk}{F = □}{F′ = ` □⟨ H ?⟩}
                {⟪ γ ⟫ M}{⟪ γ′ ⟫ M′}{n}{dir}
     (⊢ᵒ-elim ((proj dir M M′ ⊨M⊑M′) γ γ′) n 𝒫n)
     λ j V V′ j≤n M→V v M′→V′ v′ 𝒱VV′j →
     Goal {j}{V}{V′}{dir} 𝒱VV′j 
     where
     Goal : ∀{j}{V}{V′}{dir}
        → # (dir ∣ V ⊑ᴸᴿᵥ V′ ⦂ unk⊑unk) j
        → # (dir ∣ V ⊑ᴸᴿₜ (V′ ⟨ H ?⟩) ⦂ unk⊑ d) j
     Goal {zero} {V} {V′}{dir} 𝒱VV′j =
         tz (dir ∣ V ⊑ᴸᴿₜ (V′ ⟨ H ?⟩) ⦂ unk⊑ d)
     Goal {suc j} {V₁ ⟨ G !⟩} {V′₁ ⟨ H₂ !⟩}{dir} 𝒱VV′sj
         {-
            M′⟨ H ?⟩  -->*   V′₁⟨ G !⟩⟨ H ?⟩
            ⊑
            M         -->*   V₁⟨ G !⟩
         -}
         with G ≡ᵍ H₂ | 𝒱VV′sj
     ... | no neq | ()
     ... | yes refl | v₁ , v′ , 𝒱V₁V′₁j
         with G ≡ᵍ G
     ... | no neq = ⊥-elim (neq refl)
     ... | yes refl
         with G ≡ᵍ H
         {-------- Case G ≢ H ---------}
         {-
            V₁⟨ G !⟩    ⊑     V′₁⟨ G !⟩  at (suc j)
            V₁          ⊑     V′₁        at j

            nts.
            V₁⟨ G !⟩    ⊑     V′₁⟨ G !⟩⟨ H ?⟩   at (suc j)
         -}
     ... | no neq
         with dir
         {-------- Subcase ≼ ---------}
         {-
            have V′₁⟨ G !⟩⟨ H ?⟩  -->*  blame
         -}
     ... | ≼ = inj₂ (inj₁ (unit (collide v′ neq refl)))
         {-------- Subcase ≽ ---------}
         {-
            V′₁ ⟨ G !⟩⟨ H ?⟩  -->  blame

            via anti-reduction, suffices to show
            V₁ ⟨ G !⟩   ⊑     blame     at  j
            which we have by LRₜ-blame-step.
         -}
     ... | ≽ = anti-reduction-≽-R-one (LRₜ-blame-step{★}{gnd⇒ty H}{unk⊑ d}{≽})
                                      (collide v′ neq refl)
     Goal {suc j} {V₁ ⟨ G !⟩} {V′₁ ⟨ H₂ !⟩}{dir} 𝒱VV′sj
         | yes refl | v₁ , v′ , 𝒱V₁V′₁j | yes refl
         {-------- Case G ≡ H ---------}
         {-
            V₁⟨ G !⟩    ⊑     V′₁⟨ G !⟩  at (suc j)
            V₁          ⊑     V′₁        at j

            nts.
            V₁⟨ G !⟩    ⊑     V′₁⟨ G !⟩⟨ G ?⟩   at (suc j)
         -}
         | yes refl 
         with dir
         {-------- Subcase ≼ ---------}
     ... | ≼
         with G ≡ᵍ G
     ... | no neq = ⊥-elim (neq refl)
     ... | yes refl 
         with gnd-prec-unique d Refl⊑
     ... | refl =
         {-
           recall
           V₁          ⊑     V′₁        at j

           have:
           V₁⟨ G !⟩ is a value
           V′₁ ⟨ G !⟩⟨ G ?⟩  -->*  V′₁
           V₁ is a value
           V₁⟨ G !⟩    ⊑ᵥ     V′₁       at (suc j)
               by reasoning equivalent to LRᵥ-inject-L-intro-≼
         -}
           let V₁G⊑V′₁sj = v₁ , v′ , 𝒱V₁V′₁j in
           inj₂ (inj₂ (v₁ 〈 G 〉 ,
                       (V′₁ , unit (collapse v′ refl) , v′ , V₁G⊑V′₁sj)))
     Goal {suc j} {V₁ ⟨ G !⟩} {V′₁ ⟨ H₂ !⟩}{dir} 𝒱VV′sj
         | yes refl | v₁ , v′ , 𝒱V₁V′₁j | yes refl
         | yes refl 
         {-------- Subcase ≽ ---------}
         | ≽
         with gnd-prec-unique d Refl⊑
     ... | refl =
         {-
            recall
            V₁          ⊑     V′₁        at j
             
            nts.
            V₁⟨ G !⟩    ⊑ₜ     V′₁⟨ G !⟩⟨ G ?⟩   at (suc j)

            V′₁ ⟨ G !⟩⟨ G ?⟩  -->   V′₁
            
            via anti-reduction, suffices to show
            V₁⟨ G !⟩    ⊑ₜ     V′₁               at j
            so it suffices to show (via LRᵥ⇒LRₜ-step)
            V₁⟨ G !⟩    ⊑ᵥ     V′₁               at j
            which we have by LRᵥ-inject-L-intro-≽
         -}
         let 𝒱VGV′j = LRᵥ-inject-L-intro-≽ {G}{gnd⇒ty G}{d} 𝒱V₁V′₁j in
         let ℰVGV′j = LRᵥ⇒LRₜ-step{V = V₁ ⟨ G !⟩}{V′₁}{≽} 𝒱VGV′j in
         anti-reduction-≽-R-one ℰVGV′j (collapse v′ refl)

