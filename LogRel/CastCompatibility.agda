{-# OPTIONS --rewriting #-}
module LogRel.CastCompatibility where

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
open import LogRel.CastDeterministic
open import StepIndexedLogic
open import LogRel.CastLogRel
open import LogRel.CastBind

{---------------- Compatibility Lemmas ----------------------------------------}

compatible-nat : ∀{Γ}{n : ℕ}
   → Γ ⊨ $ (Num n) ⊑ $ (Num n) ⦂ ($ₜ ′ℕ , $ₜ ′ℕ , base⊑)
compatible-nat {Γ}{n} γ γ′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))

compatible-bool : ∀{Γ}{b : 𝔹}
   → Γ ⊨ $ (Bool b) ⊑ $ (Bool b) ⦂ ($ₜ ′𝔹 , $ₜ ′𝔹 , base⊑)
compatible-bool {Γ}{b} γ γ′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))

compatible-blame : ∀{Γ}{A}{M}
   → map proj₁ Γ ⊢ M ⦂ A
     -------------------------------
   → Γ ⊨ M ⊑ blame ⦂ (A , A , Refl⊑)
compatible-blame ⊢M γ γ′ = ℰ-blame

lookup-𝓖 : (Γ : List Prec) → (γ γ′ : Subst)
  → ∀ {A}{A′}{A⊑A′}{y} → Γ ∋ y ⦂ (A , A′ , A⊑A′)
  → 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ 𝒱⟦ (A , A′ , A⊑A′) ⟧ (γ y) (γ′ y)
lookup-𝓖 (.(A , A′ , A⊑A′) ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
lookup-𝓖 (B ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {suc y} ∋y =
   Sᵒ (lookup-𝓖 Γ (λ x → γ (suc x)) (λ x → γ′ (suc x)) ∋y)

compatibility-var : ∀ {Γ A A′ A⊑A′ x}
  → Γ ∋ x ⦂ (A , A′ , A⊑A′)
    -------------------------------
  → Γ ⊨ ` x ⊑ ` x ⦂ (A , A′ , A⊑A′)
compatibility-var {Γ}{A}{A′}{A⊑A′}{x} ∋x γ γ′
    rewrite sub-var γ x | sub-var γ′ x = 𝒱⇒ℰ (lookup-𝓖 Γ γ γ′ ∋x)


compatible-lambda : ∀{Γ : List Prec}{A}{B}{C}{D}{N N′ : Term}
     {c : A ⊑ C}{d : B ⊑ D}
   → ((A , C , c) ∷ Γ) ⊨ N ⊑ N′ ⦂ (B , D , d)
     ------------------------------------------------
   → Γ ⊨ (ƛ N) ⊑ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ γ γ′ = ⊢ℰλNλN′
 where
 ⊢ℰλNλN′ : 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⟦ A ⇒ B , C ⇒ D , fun⊑ c d ⟧ (⟪ γ ⟫ (ƛ N))
                                                         (⟪ γ′ ⟫ (ƛ N′))
 ⊢ℰλNλN′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI ▷𝓔N[W]N′[W′]))
  where
  ▷𝓔N[W]N′[W′] : ∀{W W′} → ▷ᵒ 𝒱⟦ A , C , c ⟧ W W′ ∷ 𝓖⟦ Γ ⟧ γ γ′
          ⊢ᵒ  ▷ᵒ ℰ⟦ B , D , d ⟧ ((⟪ ext γ ⟫ N) [ W ]) ((⟪ ext γ′ ⟫ N′) [ W′ ])
  ▷𝓔N[W]N′[W′] {W}{W′} =
      appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI (⊨N⊑N′ (W • γ) (W′ • γ′)))))) Zᵒ

compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
   → Γ ⊨ M ⊑ M′ ⦂ (A , A′ , c)
     ----------------------------------
   → Γ ⊨ L · M ⊑ L′ · M′ ⦂ (B , B′ , d)
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′} ⊨L⊑L′ ⊨M⊑M′ γ γ′ =
 ⊢ℰLM⊑LM′
 where
 ⊢ℰLM⊑LM′ : 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⟦ B , B′ , d ⟧ (⟪ γ ⟫ (L · M)) (⟪ γ′ ⟫ (L′ · M′))
 ⊢ℰLM⊑LM′ = ℰ-bind {F = ` (□· (⟪ γ ⟫ M))}{` (□· (⟪ γ′ ⟫ M′))} (⊨L⊑L′ γ γ′)
     (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰVM)))
  where
  𝓟₁ = λ V V′ → 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
           ∷ (⟪ γ′ ⟫ L′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
  ⊢ℰVM : ∀{V}{V′} → 𝓟₁ V V′ ⊢ᵒ ℰ⟦ B , B′ , d ⟧ (V · ⟪ γ ⟫ M) (V′ · ⟪ γ′ ⟫ M′) 
  ⊢ℰVM {V}{V′} = ⊢ᵒ-sucP Zᵒ λ 𝒱VV′sn →
   let (v , v′) = 𝒱⇒Value (A ⇒ B , A′ ⇒ B′ , fun⊑ c d) V V′ 𝒱VV′sn in
   ℰ-bind {F = ` (v ·□)}{F′ = ` (v′ ·□)} (Sᵒ (Sᵒ (Sᵒ (⊨M⊑M′ γ γ′))))
           (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰVWVW′)) )
   where
   𝓟₂ = λ V V′ W W′ → 𝒱⟦ A , A′ , c ⟧ W W′
          ∷ (⟪ γ′ ⟫ M′ —↠ W′)ᵒ ∷ (⟪ γ ⟫ M —↠ W)ᵒ
          ∷ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
          ∷ (⟪ γ′ ⟫ L′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ L —↠ V)ᵒ
          ∷ 𝓖⟦ Γ ⟧ γ γ′ 
   ⊢ℰVWVW′ : ∀{V V′ W W′} → 𝓟₂ V V′ W W′ ⊢ᵒ ℰ⟦ B , B′ , d ⟧ (V · W) (V′ · W′)
   ⊢ℰVWVW′ {V}{V′}{W}{W′} =
    let ⊢𝒱VV′ : 𝓟₂ V V′ W W′ ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
        ⊢𝒱VV′ = Sᵒ (Sᵒ (Sᵒ Zᵒ)) in
    let ⊢𝒱WW′ : 𝓟₂ V V′ W W′ ⊢ᵒ 𝒱⟦ A , A′ , c ⟧ W W′
        ⊢𝒱WW′ = Zᵒ in
    ⊢ᵒ-sucP ⊢𝒱WW′ λ 𝒱WW′sn →
    let (w , w′) = 𝒱⇒Value (A , A′ , c) W W′ 𝒱WW′sn in
    𝒱-fun-elim ⊢𝒱VV′ λ {N N′ refl refl 𝒱WW′→ℰNW →
    let pres-L : 𝓟₂ (ƛ N) (ƛ N′) W W′
                 ⊢ᵒ preserve-L (B , B′ , d) (ƛ N · W) (ƛ N′ · W′)
        pres-L = Λᵒ[ M₁ ] →ᵒI (constᵒE Zᵒ λ {ƛN·W→M₁ →
         let 𝒫₃ = ((ƛ N · W) —→ M₁)ᵒ ∷ 𝓟₂ (ƛ N) (ƛ N′) W W′ in
         let ⊢▷ℰNWNW′ : 𝓟₂ (ƛ N) (ƛ N′) W W′
                        ⊢ᵒ ▷ᵒ ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ])
             ⊢▷ℰNWNW′ = appᵒ 𝒱WW′→ℰNW (monoᵒ ⊢𝒱WW′) in
         let M₁=N[W] = deterministic ƛN·W→M₁ (β w) in
         let F₁ = (λ X → 𝓟₂ (ƛ N) (ƛ N′) W W′
                         ⊢ᵒ ▷ᵒ ℰ⟦ B , B′ , d ⟧ X (⟪ W′ • id ⟫ N′)) in
         let ⊢▷ℰM₁N[W′] : 𝓟₂ (ƛ N) (ƛ N′) W W′
                          ⊢ᵒ ▷ᵒ ℰ⟦ B , B′ , d ⟧ M₁ (N′ [ W′ ])
             ⊢▷ℰM₁N[W′] = subst F₁ (sym M₁=N[W]) ⊢▷ℰNWNW′ in
         let 𝒫₄ = ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ]) ∷ 𝒫₃ in
         let pres-R : 𝒫₄ ⊢ᵒ preserve-R (B , B′ , d) (N [ W ]) (ƛ N′ · W′)
             pres-R = Λᵒ[ M₁′ ] →ᵒI (constᵒE Zᵒ λ {ƛN′·W′→M₁′ →
              let M₁′=N′[W′] = deterministic ƛN′·W′→M₁′ (β w′) in
              let 𝒫₅ = ((ƛ N′ · W′) —→ M₁′)ᵒ ∷  𝒫₄ in
              let ▷ℰNWN′W′ : 𝒫₅ ⊢ᵒ ▷ᵒ ℰ⟦ (B , B′ , d) ⟧  (N [ W ]) (N′ [ W′ ])
                  ▷ℰNWN′W′ = Sᵒ (Sᵒ (Sᵒ ⊢▷ℰNWNW′)) in
              let F₂ = λ M → 𝒫₅ ⊢ᵒ ▷ᵒ ℰ⟦ (B , B′ , d) ⟧  (N [ W ]) M in
              subst F₂ (sym M₁′=N′[W′]) ▷ℰNWN′W′
              }) in
         let conc′ : ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ]) ∷ 𝒫₃
                     ⊢ᵒ ℰ⟦ B , B′ , d ⟧ (N [ W ]) (ƛ N′ · W′)
             conc′ = substᵒ (≡ᵒ-sym ℰ-stmt)
                      (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , β w′) ,ᵒ pres-R)))) in
         let conc : 𝒫₃ ⊢ᵒ ▷ᵒ ℰ⟦ (B , B′ , d) ⟧ (N [ W ]) (ƛ N′ · W′) 
             conc = ▷→▷{𝒫₃}{ℰ⟦ (B , B′ , d) ⟧ (N [ W ]) (N′ [ W′ ])}
                        (Sᵒ ⊢▷ℰNWNW′) conc′ in
         subst (λ M → 𝒫₃ ⊢ᵒ ▷ᵒ ℰ⟦ (B , B′ , d) ⟧ M (ƛ N′ · W′)) (sym M₁=N[W])
               conc
         }) in
    substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , (β w)) ,ᵒ pres-L)))
    }

compatible-inj-L : ∀{Γ}{G A′}{c : gnd⇒ty G ⊑ A′}{M M′}
   → Γ ⊨ M ⊑ M′ ⦂ (gnd⇒ty G , A′ , c)
     ------------------------------------
   → Γ ⊨ M ⟨ G !⟩ ⊑ M′ ⦂ (★ , A′ , unk⊑)
compatible-inj-L{Γ}{G}{A′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
  ℰ-bind{F = ` □⟨ G !⟩}{□} (⊨M⊑M′ γ γ′)
      (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰV⟨G!⟩V′)))
  where
  𝒫₁ = λ V V′ → 𝒱⟦ gnd⇒ty G , A′ , c ⟧ V V′
               ∷ (⟪ γ′ ⟫ M′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
  ⊢ℰV⟨G!⟩V′ : ∀{V V′} → 𝒫₁ V V′ ⊢ᵒ  ℰ⟦ ★ , A′ , unk⊑ ⟧ (V ⟨ G !⟩) V′
  ⊢ℰV⟨G!⟩V′ = 𝒱⇒ℰ (𝒱-dyn-L Zᵒ)

compatible-inj-R : ∀{Γ}{G}{c : ★ ⊑ gnd⇒ty G }{M M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , gnd⇒ty G , c)
   → Γ ⊨ M ⊑ M′ ⟨ G !⟩ ⦂ (★ , ★ , unk⊑)
compatible-inj-R{Γ}{G}{c }{M}{M′} ⊨M⊑M′ γ γ′ =
  ℰ-bind{F = □}{` □⟨ G !⟩}
    (⊨M⊑M′ γ γ′) (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰVV′⟨G!⟩)))
  where
  𝒫₁ = λ V V′ → 𝒱⟦ ★ , gnd⇒ty G , c ⟧ V V′
               ∷ (⟪ γ′ ⟫ M′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
  ⊢ℰVV′⟨G!⟩ : ∀{V V′} → 𝒫₁ V V′ ⊢ᵒ  ℰ⟦ ★ , ★ , unk⊑ ⟧ V (V′ ⟨ G !⟩)
  ⊢ℰVV′⟨G!⟩ = 𝒱⇒ℰ (𝒱-dyn-R Zᵒ)

compatible-proj-L : ∀{Γ}{H}{A′}{c : gnd⇒ty H ⊑ A′}{M}{M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , A′ ,  unk⊑)
   → Γ ⊨ M ⟨ H ?⟩ ⊑ M′ ⦂ (gnd⇒ty H , A′ , c)
compatible-proj-L {Γ}{H}{A′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
  ℰ-bind{F = ` □⟨ H ?⟩}{□} (⊨M⊑M′ γ γ′)
     (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰV⟨H?⟩V′)))
  where
  𝒫₁ = λ V V′ A′ → 𝒱⟦ ★ , A′ , unk⊑ ⟧ V V′
               ∷ (⟪ γ′ ⟫ M′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
  ⊢ℰV⟨H?⟩V′ : ∀{V V′ A′ H c}
     → 𝒫₁ V V′ A′ ⊢ᵒ  ℰ⟦ gnd⇒ty H , A′ , c ⟧ (V ⟨ H ?⟩) V′
  ⊢ℰV⟨H?⟩V′ {V} {V′} {★} {$ᵍ ι} {()}
  ⊢ℰV⟨H?⟩V′ {V} {V′} {★} {★⇒★} {()}
  ⊢ℰV⟨H?⟩V′ {V} {V′} {$ₜ ι} {$ᵍ .ι} {base⊑} =
    𝒱-dyn-base-elim Zᵒ Goal
    where
    Goal : ∀{V₁} {k} → V ≡ (V₁ ⟨ $ᵍ ι !⟩) → V′ ≡ $ k
       → 𝒫₁ V V′ ($ₜ ι) ⊢ᵒ Value V₁ ᵒ ×ᵒ (▷ᵒ 𝒱⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ V₁ ($ k))
       → 𝒫₁ V V′ ($ₜ ι) ⊢ᵒ ℰ⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ (V ⟨ $ᵍ ι ?⟩) V′
    Goal {V₁}{k} refl refl ⊢v₁×▷𝒱V₁k =
      ⊢ᵒ-sucP (proj₁ᵒ ⊢v₁×▷𝒱V₁k) λ v₁ →
      substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , (collapse v₁ refl))
         ,ᵒ (Λᵒ[ N ] (→ᵒI Goal2)))))
      where
      Goal2 : ∀{N} → (V₁ ⟨ $ᵍ ι !⟩ ⟨ $ᵍ ι ?⟩ —→ N)ᵒ
                     ∷ 𝒫₁ (V₁ ⟨ $ᵍ ι !⟩) ($ k) ($ₜ ι)
                     ⊢ᵒ ▷ᵒ ℰ⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ N ($ k)
      Goal2 {N} =
        ⊢ᵒ-sucP Zᵒ λ {red →
        ⊢ᵒ-sucP (proj₁ᵒ (Sᵒ ⊢v₁×▷𝒱V₁k)) λ { v₁ →
        let N≡V₁ = collapse-inv v₁ red in
        subst (λ N → (((V₁ ⟨ $ᵍ ι !⟩) ⟨ $ᵍ ι ?⟩) —→ N) ᵒ ∷
                𝒫₁ (V₁ ⟨ $ᵍ ι !⟩) V′ ($ₜ ι)
                ⊢ᵒ (▷ᵒ ℰ⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ N V′)) (sym N≡V₁)
          (▷→▷ (proj₂ᵒ (Sᵒ ⊢v₁×▷𝒱V₁k)) (𝒱⇒ℰ Zᵒ))
        }}
    
  ⊢ℰV⟨H?⟩V′ {V} {V′} {A′ ⇒ B′} {★⇒★} {fun⊑ unk⊑ unk⊑} =
    𝒱-dyn-fun-elim2{V = V}{V′} Zᵒ Goal
    where
    Goal : ∀ {V₁} → V ≡ (V₁ ⟨ ★⇒★ !⟩)
       → 𝒫₁ V V′ (A′ ⇒ B′) ⊢ᵒ Value V₁ ᵒ ×ᵒ Value V′ ᵒ
          ×ᵒ (▷ᵒ 𝒱⟦ ★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑ ⟧ V₁ V′)
       → 𝒫₁ V V′ (A′ ⇒ B′)
          ⊢ᵒ ℰ⟦ ★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑ ⟧ (V ⟨ ★⇒★ ?⟩) V′
    Goal {V₁} refl ⊢v₁×v′×▷𝒱V₁V′ =
      ⊢ᵒ-sucP (proj₁ᵒ ⊢v₁×v′×▷𝒱V₁V′) λ v₁ →
      substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , (collapse v₁ refl))
         ,ᵒ (Λᵒ[ N ] (→ᵒI Goal2)))))
      where
      Goal2 : ∀{N} → (V₁ ⟨ ★⇒★ !⟩ ⟨ ★⇒★ ?⟩ —→ N)ᵒ
                     ∷ 𝒫₁ (V₁ ⟨ ★⇒★ !⟩) V′ (A′ ⇒ B′)
                     ⊢ᵒ ▷ᵒ ℰ⟦ ★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑ ⟧ N V′
      Goal2 {N} =
        ⊢ᵒ-sucP Zᵒ λ {red →
        ⊢ᵒ-sucP (proj₁ᵒ (Sᵒ ⊢v₁×v′×▷𝒱V₁V′)) λ { v₁ →
        let N≡V₁ = collapse-inv v₁ red in
        subst (λ N → (((V₁ ⟨ ★⇒★ !⟩) ⟨ ★⇒★ ?⟩) —→ N) ᵒ ∷
                𝒫₁ (V₁ ⟨ ★⇒★ !⟩) V′ (A′ ⇒ B′)
                ⊢ᵒ (▷ᵒ ℰ⟦ ★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑ ⟧ N V′)) (sym N≡V₁)
          (▷→▷ (proj₂ᵒ (proj₂ᵒ (Sᵒ ⊢v₁×v′×▷𝒱V₁V′))) (𝒱⇒ℰ Zᵒ))
        }}

compatible-proj-R : ∀{Γ}{H′}{c : ★ ⊑ gnd⇒ty H′}{M}{M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , ★ , unk⊑)
   → Γ ⊨ M ⊑ M′ ⟨ H′ ?⟩ ⦂ (★ , gnd⇒ty H′ , c)
compatible-proj-R {Γ}{H′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
  ℰ-bind{F = □}{` □⟨ H′ ?⟩} (⊨M⊑M′ γ γ′)
     (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰVV′⟨H?⟩)))
  where
  𝒫₁ = λ V V′ → 𝒱⟦ ★ , ★ , unk⊑ ⟧ V V′
                 ∷ (⟪ γ′ ⟫ M′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′  
  ⊢ℰVV′⟨H?⟩ : ∀{V V′ H′ c}
     → 𝒫₁ V V′ ⊢ᵒ ℰ⟦ ★ , gnd⇒ty H′ , c ⟧ V (V′ ⟨ H′ ?⟩)
  ⊢ℰVV′⟨H?⟩ {V} {V′} {H′} {unk⊑} =
    𝒱-dyn-dyn-elim Zᵒ Goal
    where
    Goal : ∀ {V₁ V₁′} {G} → V ≡ (V₁ ⟨ G !⟩) → V′ ≡ (V₁′ ⟨ G !⟩)
       → 𝒫₁ V V′ ⊢ᵒ Value V₁ ᵒ ×ᵒ Value V₁′ ᵒ
           ×ᵒ (▷ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V₁′)
       → 𝒫₁ V V′ ⊢ᵒ ℰ⟦ ★ , gnd⇒ty H′ , unk⊑ ⟧ V (V′ ⟨ H′ ?⟩)
    Goal {V₁}{V₁′}{G} refl refl ⊢v₁×v₁′×▷𝒱V₁V₁′
        with G ≡ᵍ H′
    ... | no neq =
        ⊢ᵒ-sucP (proj₁ᵒ (proj₂ᵒ ⊢v₁×v₁′×▷𝒱V₁V₁′)) λ v₁′ →
        substᵒ (≡ᵒ-sym ℰ-stmt)
        (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , collide v₁′ neq refl)
          ,ᵒ (Λᵒ[ N′ ] (→ᵒI Goal2))))))
     where
     Goal2 : ∀{N′}
        → (V′ ⟨ H′ ?⟩ —→ N′)ᵒ ∷ 𝒫₁ V V′
           ⊢ᵒ ▷ᵒ ℰ⟦ ★ , gnd⇒ty H′ , unk⊑ ⟧ V N′
     Goal2 {N′} =
       ⊢ᵒ-sucP Zᵒ λ {red →
       ⊢ᵒ-sucP (proj₁ᵒ (proj₂ᵒ (Sᵒ ⊢v₁×v₁′×▷𝒱V₁V₁′))) λ { v₁′ →
       let N′≡blame = collide-inv neq v₁′ red in
       subst (λ N′ → (((V₁′ ⟨ G !⟩) ⟨ H′ ?⟩) —→ N′) ᵒ ∷
                        𝒫₁ (V₁ ⟨ G !⟩) (V₁′ ⟨ G !⟩)
                       ⊢ᵒ (▷ᵒ ℰ⟦ ★ , gnd⇒ty H′ , unk⊑ ⟧ (V₁ ⟨ G !⟩) N′))
             (sym N′≡blame)
       (monoᵒ ℰ-blame)
       }}
       
    Goal {V₁}{V₁′}{G} refl refl ⊢v₁×v₁′×▷𝒱V₁V₁′ | yes refl =
        ⊢ᵒ-sucP (proj₁ᵒ (proj₂ᵒ ⊢v₁×v₁′×▷𝒱V₁V₁′)) λ v₁′ →
        substᵒ (≡ᵒ-sym ℰ-stmt)
        (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , collapse v₁′ refl)
          ,ᵒ (Λᵒ[ N′ ] (→ᵒI Goal2))))))
     where
     Goal2 : ∀{N′}
        → (V′ ⟨ H′ ?⟩ —→ N′)ᵒ ∷ 𝒫₁ V V′
           ⊢ᵒ ▷ᵒ ℰ⟦ ★ , gnd⇒ty H′ , unk⊑ ⟧ V N′
     Goal2 {N′} =
       ⊢ᵒ-sucP Zᵒ λ {red →
       ⊢ᵒ-sucP (proj₁ᵒ (proj₂ᵒ (Sᵒ ⊢v₁×v₁′×▷𝒱V₁V₁′))) λ { v₁′ →
       let N′≡V₁′ = collapse-inv v₁′ red in
       let ⊢▷𝒱V₁V₁′ = (proj₂ᵒ (proj₂ᵒ (Sᵒ ⊢v₁×v₁′×▷𝒱V₁V₁′))) in
       subst (λ N′ → (((V₁′ ⟨ G !⟩) ⟨ G ?⟩) —→ N′) ᵒ
                     ∷ 𝒫₁ (V₁ ⟨ G !⟩) (V₁′ ⟨ G !⟩)
                     ⊢ᵒ (▷ᵒ ℰ⟦ ★ , gnd⇒ty G , unk⊑ ⟧ (V₁ ⟨ G !⟩) N′))
             (sym N′≡V₁′)
       (▷→▷ ⊢▷𝒱V₁V₁′ (𝒱⇒ℰ (𝒱-dyn-L Zᵒ)))
       }}
       
