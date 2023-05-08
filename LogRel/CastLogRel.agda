{-# OPTIONS --rewriting #-}
module LogRel.CastLogRel where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
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
open import EquivalenceRelation

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Prec × Term × Term) ⊎ (Prec × Term × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

ℰˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A⊑B ⟧ M M′ = (inj₂ (A⊑B , M , M′)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A⊑B ⟧ V V′ = (inj₁ (A⊑B , V , V′)) ∈ zeroˢ

pre-𝒱 : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 (.★ , ★ , unk⊑) (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = let g = gnd⇒ty G in
                 (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (𝒱ˢ⟦ (g , g , Refl⊑) ⟧ V V′))
... | no neq = ⊥ ˢ
pre-𝒱 (.★ , $ₜ ι′ , unk⊑) (V ⟨ $ᵍ ι !⟩) ($ c)
    with ($ᵍ ι) ≡ᵍ ($ᵍ ι′)
... | yes refl = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ ($ₜ ι , $ₜ ι , Refl⊑) ⟧ V ($ c))
... | no new = ⊥ ˢ
pre-𝒱 (.★ , A′ ⇒ B′ , unk⊑) (V ⟨ ★⇒★ !⟩) V′ =
    (Value V)ˢ ×ˢ (Value V′)ˢ
    ×ˢ ▷ˢ (𝒱ˢ⟦ (★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑) ⟧ V V′)
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) = (c ≡ c′) ˢ
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (𝒱ˢ⟦ (A , A′ , A⊑A′) ⟧ W W′)
                  →ˢ ▷ˢ (ℰˢ⟦ (B , B′ , B⊑B′) ⟧ (N [ W ]) (N′ [ W′ ])) 
pre-𝒱 (A , A′ , A⊑A′) V V′ = ⊥ ˢ

pre-ℰ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ c M M′ =
       pre-𝒱 c M M′
    ⊎ˢ ((reducible M)ˢ ×ˢ (∀ˢ[ N ] (M —→ N)ˢ →ˢ ▷ˢ (ℰˢ⟦ c ⟧ N M′)))
    ⊎ˢ ((reducible M′)ˢ ×ˢ (∀ˢ[ N′ ] (M′ —→ N′)ˢ →ˢ ▷ˢ (ℰˢ⟦ c ⟧ M N′)))
    ⊎ˢ (Blame M′)ˢ

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (c , V , V′)) = pre-𝒱 c V V′
pre-ℰ⊎𝒱 (inj₂ (c , M , M′)) = pre-ℰ c M M′

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X

𝒱⟦_⟧ : (c : Prec) → Term → Term → Setᵒ
𝒱⟦ c ⟧ V V′ = ℰ⊎𝒱 (inj₁ (c , V , V′))

ℰ⟦_⟧ : (c : Prec) → Term → Term → Setᵒ
ℰ⟦ c ⟧ M M′ = ℰ⊎𝒱 (inj₂ (c , M , M′))

preserve-L : Prec → Term → Term → Setᵒ
preserve-L c M M′ = (∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ c ⟧ N M′)))

preserve-R : Prec → Term → Term → Setᵒ
preserve-R c M M′ = (∀ᵒ[ N′ ] ((M′ —→ N′)ᵒ →ᵒ ▷ᵒ (ℰ⟦ c ⟧ M N′)))

ℰ-def : Prec → Term → Term → Setᵒ
ℰ-def c M M′ = ((𝒱⟦ c ⟧ M M′)
      ⊎ᵒ ((reducible M)ᵒ ×ᵒ preserve-L c M M′)
      ⊎ᵒ ((reducible M′)ᵒ ×ᵒ preserve-R c M M′)
      ⊎ᵒ (Blame M′)ᵒ)

ℰ-stmt : ∀{c}{M}{M′} → ℰ⟦ c ⟧ M M′ ≡ᵒ ℰ-def c M M′
ℰ-stmt {c}{M}{M′} =
  let X₁ = inj₁ (c , M , M′) in
  let X₂ = inj₂ (c , M , M′) in
  ℰ⟦ c ⟧ M M′                                                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 X₂                                      ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₂ ⟩
  # (pre-ℰ⊎𝒱 X₂) (ℰ⊎𝒱 , ttᵖ)
                                  ⩦⟨ cong-⊎ᵒ ((≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 X₁)))
                                       (cong-⊎ᵒ (≡ᵒ-refl refl) (≡ᵒ-refl refl)) ⟩
  ℰ-def c M M′
  ∎

ℰ-suc : ∀{c}{M}{M′}{k}
  → #(ℰ⟦ c ⟧ M M′) (suc k) ⇔ #(ℰ-def c M M′) (suc k)
ℰ-suc {c}{M}{M′}{k} = ≡ᵒ⇒⇔{k = suc k} (ℰ-stmt{c}{M}{M′})

{------------- Related values are syntactic values ----------------------------}

𝒱⇒Value : ∀ {k} c M M′
   → # (𝒱⟦ c ⟧ M M′) (suc k)
     ------------------------
   → Value M × Value M′
𝒱⇒Value {k} (.★ , ★ , unk⊑) (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
𝒱⇒Value {k} (.★ , $ₜ ι′ , unk⊑) (V ⟨ $ᵍ ι !⟩) ($ c) 𝒱MM′
    with  ($ᵍ ι) ≡ᵍ ($ᵍ ι′)
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , _ = (v 〈 $ᵍ ι′ 〉) , ($̬ c)
𝒱⇒Value {k} (.★ , A′ ⇒ B′ , unk⊑) (V ⟨ ★⇒★ !⟩) V′ 𝒱VV′
    with 𝒱VV′
... | v , v′ , _ = (v 〈 ★⇒★ 〉) , v′
𝒱⇒Value {k} ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
𝒱⇒Value {k} ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱VV′ =
    (ƛ̬ N) , (ƛ̬ N′)

{--------- Equations, intro, and elim rules for 𝒱 ----------------------------}

𝒱-base : ∀{ι}{c}{c′} → 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ ($ c) ($ c′) ≡ᵒ (c ≡ c′) ᵒ
𝒱-base{ι}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

𝒱-base-intro : ∀{𝒫}{ι}{c} → 𝒫 ⊢ᵒ 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ ($ c) ($ c)
𝒱-base-intro{ι}{c} = substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl)

𝒱-base-elim : ∀{𝒫}{ι}{ι′}{c}{V}{V′}{R}
  → 𝒫 ⊢ᵒ 𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ V V′
  → (∀ k → ι ≡ ι′ → V ≡ $ k → V′ ≡ $ k → 𝒫 ⊢ᵒ R)
    -------------------------------------------
  → 𝒫 ⊢ᵒ R
𝒱-base-elim{𝒫}{ι}{ι′}{c}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ → G 𝒱VV′ ⊢𝒱VV′ cont
  where
  G : ∀{ι}{ι′}{c}{V}{V′}{n} →  #(𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ V V′) (suc n)
    → 𝒫 ⊢ᵒ 𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ V V′
    → (∀ k → ι ≡ ι′ → V ≡ $ k → V′ ≡ $ k → 𝒫 ⊢ᵒ R)
    → 𝒫 ⊢ᵒ R
  G {ι} {.ι} {base⊑} {$ k} {$ k′} {n} refl ⊢𝒱kk cont = cont k refl refl refl

𝒱-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}
   → (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ (ƛ N) (ƛ N′))
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (𝒱⟦ A , A′ , A⊑A′ ⟧ W W′))
                         →ᵒ (▷ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ (N [ W ]) (N′ [ W′ ])))))
𝒱-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′} =
   let X = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , ƛ N , ƛ N′) in
   (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ (ƛ N) (ƛ N′))      ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                              ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                                 ⩦⟨ ≡ᵒ-refl refl ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (𝒱⟦ A , A′ , A⊑A′ ⟧ W W′))
                      →ᵒ (▷ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ (N [ W ]) (N′ [ W′ ])))))    ∎

𝒱-fun-elim : ∀{𝒫}{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
   → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀{W W′} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A , A′ , c ⟧ W W′))
                             →ᵒ (▷ᵒ (ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ]))))
             → 𝒫 ⊢ᵒ R)
     --------------------------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-fun-elim {𝒫}{A}{B}{A′}{B′}{c}{d}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ { 𝒱VV′sn → G {V}{V′} 𝒱VV′sn ⊢𝒱VV′ cont }
  where
  G : ∀{V}{V′}{n}
     → # (𝒱⟦  A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
     → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀{W W′} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A , A′ , c ⟧ W W′))
                             →ᵒ (▷ᵒ (ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ]))))
             → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G {ƛ N}{ƛ N′}{n} 𝒱VV′ ⊢𝒱VV′ cont = cont N N′ refl refl λ {W}{W′} →
     instᵒ (instᵒ (substᵒ 𝒱-fun ⊢𝒱VV′) W) W′ 

𝒱-dyn-base : ∀{V}{ι}{k}
   → 𝒱⟦ ★ , $ₜ ι , unk⊑ ⟧ (V ⟨ $ᵍ ι !⟩) ($ k)
     ≡ᵒ (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ ($ₜ ι , $ₜ ι , Refl⊑) ⟧ V ($ k))
𝒱-dyn-base{V} {ι}{k} =
  let X = inj₁ ((★ , $ₜ ι , unk⊑) , (V ⟨ $ᵍ ι !⟩) , ($ k)) in
  𝒱⟦ ★ , $ₜ ι , unk⊑ ⟧ (V ⟨ $ᵍ ι !⟩) ($ k)
    ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X
    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X  ⟩
  # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
    ⩦⟨ EQ1 ⟩
  (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ ($ₜ ι , $ₜ ι , Refl⊑) ⟧ V ($ k)) ∎
  where
  X = inj₁ ((★ , $ₜ ι , unk⊑) , (V ⟨ $ᵍ ι !⟩) , ($ k))
  EQ1 : # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
    ≡ᵒ (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ ($ₜ ι , $ₜ ι , Refl⊑) ⟧ V ($ k))
  EQ1
      with ($ᵍ ι) ≡ᵍ ($ᵍ ι)
  ... | no neq = ⊥-elim (neq refl)    
  ... | yes refl = ≡ᵒ-refl refl

𝒱-dyn-base-elim : ∀{𝒫}{ι}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , $ₜ ι , unk⊑ ⟧ V V′
   → (∀{V₁}{k} → V ≡ V₁ ⟨ $ᵍ ι !⟩ → V′ ≡ ($ k)
         → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ ▷ᵒ 𝒱⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ V₁ ($ k) → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-base-elim {𝒫}{ι}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ { 𝒱VV′sn → G 𝒱VV′sn ⊢𝒱VV′ cont }
  where
  G : ∀{V}{V′}{n}
     → # (𝒱⟦ ★ , $ₜ ι , unk⊑ ⟧ V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , $ₜ ι , unk⊑ ⟧ V V′
     → (∀{V₁}{k} → V ≡ V₁ ⟨ $ᵍ ι !⟩ → V′ ≡ ($ k)
        → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ ▷ᵒ 𝒱⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ V₁ ($ k) → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G {V₁ ⟨ $ᵍ ι′ !⟩}{$ k}{n} 𝒱VV′ ⊢𝒱VV′ cont
      with ($ᵍ ι′) ≡ᵍ ($ᵍ ι)
  ... | no neq = ⊥-elim 𝒱VV′
  ... | yes refl = cont refl refl (substᵒ (𝒱-dyn-base{V₁}{ι}{k}) ⊢𝒱VV′)
  G {L · M}{V′}{n} () ⊢𝒱VV′ cont
  G {ƛ N}{V′}{n} () ⊢𝒱VV′ cont
  G {` x}{V′}{n} () ⊢𝒱VV′ cont
  G {V₁ ⟨ H ?⟩}{V′}{n} () ⊢𝒱VV′ cont

Value-inj-inv : ∀{V}{G}
   → Value (V ⟨ G !⟩)
   → Value V
Value-inj-inv {V} {G} (v 〈 .G 〉) = v

𝒱-dyn-fun : ∀{A′}{B′}{V}{V′}
   → 𝒱⟦ ★ , A′ ⇒ B′ , unk⊑ ⟧ (V ⟨ ★⇒★ !⟩) V′
     ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
        ×ᵒ ▷ᵒ (𝒱⟦ (★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑) ⟧ V V′)
𝒱-dyn-fun {A′}{B′}{V}{V′} =
  let X = inj₁ ((★ , A′ ⇒ B′ , unk⊑) , (V ⟨ ★⇒★ !⟩) , V′) in
  𝒱⟦ ★ , A′ ⇒ B′ , unk⊑ ⟧ (V ⟨ ★⇒★ !⟩) V′
     ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X
    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X  ⟩
  # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
    ⩦⟨ ≡ᵒ-refl refl ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ
        ×ᵒ ▷ᵒ (𝒱⟦ (★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑) ⟧ V V′)
  ∎ 

𝒱-dyn-fun-elim : ∀{𝒫}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ ⇒ ★ , unk⊑ ⟧ V V′
   → (∀{V₁} → V ≡ V₁ ⟨ ★⇒★ !⟩ 
         → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ (Value V′)ᵒ
             ×ᵒ ▷ᵒ 𝒱⟦ ★ ⇒ ★ , ★ ⇒ ★ , fun⊑ unk⊑ unk⊑ ⟧ V₁ V′ → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-fun-elim {𝒫}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ { 𝒱VV′sn → G 𝒱VV′sn ⊢𝒱VV′ cont }
  where
  G : ∀{V}{V′}{n}
     → # (𝒱⟦ ★ , ★ ⇒ ★ , unk⊑ ⟧ V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ ⇒ ★ , unk⊑ ⟧ V V′
     → (∀{V₁} → V ≡ V₁ ⟨ ★⇒★ !⟩
        → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ (Value V′)ᵒ
                ×ᵒ ▷ᵒ 𝒱⟦ ★ ⇒ ★ , ★ ⇒ ★ , fun⊑ unk⊑ unk⊑ ⟧ V₁ V′
        → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G {V₁ ⟨ ★⇒★ !⟩}{V′}{n} 𝒱V!V′ ⊢𝒱V!V′ cont =
    let ⊢𝒱VV′ = substᵒ 𝒱-dyn-fun ⊢𝒱V!V′ in
    cont refl ⊢𝒱VV′

𝒱-dyn-fun-elim2 : ∀{𝒫}{V}{V′}{R}{A}{B}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A ⇒ B , unk⊑ ⟧ V V′
   → (∀{V₁} → V ≡ V₁ ⟨ ★⇒★ !⟩ 
         → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ (Value V′)ᵒ
             ×ᵒ ▷ᵒ 𝒱⟦ ★ ⇒ ★ , A ⇒ B , fun⊑ unk⊑ unk⊑ ⟧ V₁ V′ → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-fun-elim2 {𝒫}{V}{V′}{R}{A}{B} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ { 𝒱VV′sn → G 𝒱VV′sn ⊢𝒱VV′ cont }
  where
  G : ∀{V}{V′}{n}
     → # (𝒱⟦ ★ , A ⇒ B , unk⊑ ⟧ V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A ⇒ B , unk⊑ ⟧ V V′
     → (∀{V₁} → V ≡ V₁ ⟨ ★⇒★ !⟩
        → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ (Value V′)ᵒ
                ×ᵒ ▷ᵒ 𝒱⟦ ★ ⇒ ★ , A ⇒ B , fun⊑ unk⊑ unk⊑ ⟧ V₁ V′
        → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G {V₁ ⟨ ★⇒★ !⟩}{V′}{n} 𝒱V!V′ ⊢𝒱V!V′ cont =
    let ⊢𝒱VV′ = substᵒ 𝒱-dyn-fun ⊢𝒱V!V′ in
    cont refl ⊢𝒱VV′

𝒱-dyn-dyn : ∀{V}{V′}{G}
   → 𝒱⟦ ★ , ★ , unk⊑ ⟧ (V ⟨ G !⟩) (V′ ⟨ G !⟩)
     ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
         ×ᵒ (▷ᵒ (𝒱⟦ (gnd⇒ty G , gnd⇒ty G , Refl⊑) ⟧ V V′))
𝒱-dyn-dyn {V}{V′}{G} =
  let X = inj₁ ((★ , ★ , unk⊑) , (V ⟨ G !⟩) , (V′ ⟨ G !⟩)) in 
  𝒱⟦ ★ , ★ , unk⊑ ⟧ (V ⟨ G !⟩) (V′ ⟨ G !⟩)
    ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X
    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X  ⟩
  # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
    ⩦⟨ EQ ⟩
   (Value V)ᵒ ×ᵒ (Value V′)ᵒ
         ×ᵒ (▷ᵒ (𝒱⟦ (gnd⇒ty G , gnd⇒ty G , Refl⊑) ⟧ V V′)) ∎
  where
  X = inj₁ ((★ , ★ , unk⊑) , (V ⟨ G !⟩) , (V′ ⟨ G !⟩))
  EQ : # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
    ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
         ×ᵒ (▷ᵒ (𝒱⟦ (gnd⇒ty G , gnd⇒ty G , Refl⊑) ⟧ V V′))
  EQ
      with G ≡ᵍ G
  ... | yes refl = ≡ᵒ-refl refl
  ... | no neq = ⊥-elim (neq refl)

𝒱-dyn-R : ∀{𝒫}{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , gnd⇒ty G , c ⟧ V V′
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑ ⟧ V (V′ ⟨ G !⟩)
𝒱-dyn-R {𝒫} {$ᵍ ι} {unk⊑} {V} {V′} ⊢𝒱VV′ =
  𝒱-dyn-base-elim ⊢𝒱VV′ G
  where
  G : ∀{V₁} {k} → V ≡ (V₁ ⟨ $ᵍ ι !⟩) → V′ ≡ $ k
     → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ (▷ᵒ 𝒱⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ V₁ ($ k))
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑ ⟧ V (V′ ⟨ $ᵍ ι !⟩)
  G {V₁} {k} refl refl ⊢v₁×𝒱V₁k =
    substᵒ (≡ᵒ-sym 𝒱-dyn-dyn)
      (proj₁ᵒ ⊢v₁×𝒱V₁k ,ᵒ (constᵒI ($̬ k) ,ᵒ proj₂ᵒ ⊢v₁×𝒱V₁k))
𝒱-dyn-R {𝒫} {★⇒★} {unk⊑} {V} {V′} ⊢𝒱VV′ = 𝒱-dyn-fun-elim ⊢𝒱VV′ G
  where
  G : ∀ {V₁} → V ≡ (V₁ ⟨ ★⇒★ !⟩)
     → 𝒫 ⊢ᵒ Value V₁ ᵒ ×ᵒ Value V′ ᵒ
          ×ᵒ (▷ᵒ 𝒱⟦ ★ ⇒ ★ , ★ ⇒ ★ , fun⊑ unk⊑ unk⊑ ⟧ V₁ V′)
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑ ⟧ V (V′ ⟨ ★⇒★ !⟩)
  G {V₁} refl ⊢v×v′×▷𝒱V₁V′ = substᵒ (≡ᵒ-sym 𝒱-dyn-dyn) ⊢v×v′×▷𝒱V₁V′

𝒱-dyn-dyn-elim : ∀{𝒫}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑ ⟧ V V′
   → (∀{V₁}{V₁′}{G} → V ≡ V₁ ⟨ G !⟩ → V′ ≡ V₁′ ⟨ G !⟩
         → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ (Value V₁′)ᵒ
             ×ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V₁′ → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-dyn-elim {𝒫}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ → G 𝒱VV′ ⊢𝒱VV′ cont
  where
  G : ∀{V}{V′}{n}
     → # (𝒱⟦ ★ , ★ , unk⊑ ⟧ V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑ ⟧ V V′
     → (∀{V₁}{V₁′}{G} → V ≡ V₁ ⟨ G !⟩ → V′ ≡ V₁′ ⟨ G !⟩
         → 𝒫 ⊢ᵒ (Value V₁)ᵒ ×ᵒ (Value V₁′)ᵒ
             ×ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V₁′ → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G {V₁ ⟨ G !⟩}{V₁′ ⟨ H !⟩}{n} 𝒱VV′ ⊢𝒱VV′ cont
      with G ≡ᵍ H
  ... | no neq = ⊥-elim 𝒱VV′
  ... | yes refl = cont refl refl (substᵒ 𝒱-dyn-dyn ⊢𝒱VV′)

𝒱-dyn-L : ∀{𝒫}{G}{A′}{c : gnd⇒ty G ⊑ A′}{V}{V′}
   → 𝒫 ⊢ᵒ 𝒱⟦ gnd⇒ty G , A′ , c ⟧ V V′
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A′ , unk⊑ ⟧ (V ⟨ G !⟩) V′
𝒱-dyn-L {𝒫} {$ᵍ ι} {$ₜ ι′} {c} {V} {V′} 𝒱VV′ =
  𝒱-base-elim 𝒱VV′ λ {k refl refl refl → G}
  where
  G : ∀{k} → 𝒫 ⊢ᵒ 𝒱⟦ ★ , $ₜ ι , unk⊑ ⟧ ($ k ⟨ $ᵍ ι !⟩) ($ k)
  G {k} = substᵒ (≡ᵒ-sym 𝒱-dyn-base) (constᵒI ($̬ k) ,ᵒ monoᵒ 𝒱-base-intro)
𝒱-dyn-L {𝒫} {★⇒★} {A′ ⇒ B′} {fun⊑ unk⊑ unk⊑} {V} {V′} ⊢𝒱VV′ =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ →
  let (v , v′) = 𝒱⇒Value (★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑) V V′ 𝒱VV′ in
  substᵒ (≡ᵒ-sym 𝒱-dyn-fun) (constᵒI v ,ᵒ (constᵒI v′ ,ᵒ monoᵒ ⊢𝒱VV′))

{----------- Relate Open Terms ------------------------------------------------}

𝓖⟦_⟧ : (Γ : List Prec) → Subst → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ σ′ = []
𝓖⟦ c ∷ Γ ⟧ σ σ′ = (𝒱⟦ c ⟧ (σ 0) (σ′ 0))
                     ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x)) (λ x → σ′ (suc x))

_⊨_⊑_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst) → 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⟦ c ⟧ (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

{--------------- Related values are related expressions -----------------------}

𝒱⇒ℰ : ∀{c : Prec}{𝒫}{V V′}
   → 𝒫 ⊢ᵒ 𝒱⟦ c ⟧ V V′
     -----------------
   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ V V′
𝒱⇒ℰ {c}{𝒫}{V}{V′} ⊢𝒱VV′ = substᵒ (≡ᵒ-sym ℰ-stmt) (inj₁ᵒ ⊢𝒱VV′)

{--------------- Blame on the right -------------------------------------------}

ℰ-blame : ∀{𝒫}{c}{M} → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ M blame
ℰ-blame {𝒫}{c}{M} = substᵒ (≡ᵒ-sym ℰ-stmt)
                            (inj₂ᵒ (inj₂ᵒ (inj₂ᵒ (constᵒI isBlame))))

