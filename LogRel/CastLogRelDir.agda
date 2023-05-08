{-# OPTIONS --rewriting #-}
module LogRel.CastLogRelDir where

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
open import LogRel.CastReduction
open import StepIndexedLogic
open import EquivalenceRelation

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

data Dir : Set where
  ≺ : Dir
  ≻ : Dir

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

ℰˢ⟦_⟧ : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A⊑B ⟧ dir M M′ = (inj₂ (A⊑B , dir , M , M′)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A⊑B ⟧ dir V V′ = (inj₁ (A⊑B , dir , V , V′)) ∈ zeroˢ

pre-𝒱 : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 (.★ , ★ , unk⊑) dir (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = let g = gnd⇒ty G in
                 (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (𝒱ˢ⟦ (g , g , Refl⊑) ⟧ dir V V′))
... | no neq = ⊥ ˢ
pre-𝒱 (.★ , $ₜ ι′ , unk⊑) dir (V ⟨ $ᵍ ι !⟩) ($ c)
    with ($ᵍ ι) ≡ᵍ ($ᵍ ι′)
... | yes refl = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ ($ₜ ι , $ₜ ι , Refl⊑) ⟧ dir V ($ c))
... | no new = ⊥ ˢ
pre-𝒱 (.★ , A′ ⇒ B′ , unk⊑) dir (V ⟨ ★⇒★ !⟩) V′ =
    (Value V)ˢ ×ˢ (Value V′)ˢ
    ×ˢ ▷ˢ (𝒱ˢ⟦ (★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑) ⟧ dir V V′)
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) dir ($ c) ($ c′) = (c ≡ c′) ˢ
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) dir (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (𝒱ˢ⟦ (A , A′ , A⊑A′) ⟧ dir W W′)
                  →ˢ ▷ˢ (ℰˢ⟦ (B , B′ , B⊑B′) ⟧ dir (N [ W ]) (N′ [ W′ ])) 
pre-𝒱 (A , A′ , A⊑A′) dir V V′ = ⊥ ˢ

{-

   Gradual Guarantee (GG):
   
                         M′ (more precise)
   M           value   blame   diverge
   value        ✓        ✓  
   ---------|--------|-------|--------
   blame                 ✓   
   ---------|--------|-------|--------
   diverge               ✓      ✓

   We express the GG in terms of two directional
   predicates, ℰ≺ and ℰ≻, whose intersection
   is equivalent to the GG.
   
   ℰ≺ accepts the following:

                         M′ (more precise)
   M           value   blame   diverge
   value         ✓      ✓   
   ---------|--------|-------|---------
   blame                ✓    
   ---------|--------|-------|---------
   diverge      ✓       ✓       ✓ 

-}

pre-ℰ : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ c ≺ M M′ =
   (∃ˢ[ N ] (M —→ N)ˢ ×ˢ ▷ˢ (ℰˢ⟦ c ⟧ ≻ N M′))
   ⊎ˢ ((Blame M)ˢ ×ˢ (Blame M′)ˢ)
   ⊎ˢ ((Value M)ˢ ×ˢ ((Blame M′)ˢ ⊎ˢ
                    (∃ˢ[ V′ ] (M′ —↠ V′)ˢ ×ˢ (Value V′)ˢ ×ˢ (pre-𝒱 c ≻ V′ M))))

{-

   ℰ≻ accepts the following:

                         M′ (more precise)
   M           value   blame   diverge
   value         ✓       ✓       ✓
   ---------|--------|-------|---------
   blame                 ✓       ✓
   ---------|--------|-------|---------
   diverge               ✓       ✓

-}
pre-ℰ c ≻ M M′ =
   (∃ˢ[ N′ ] (M′ —→ N′)ˢ ×ˢ ▷ˢ (ℰˢ⟦ c ⟧ ≻ M M′))
   ⊎ˢ (Blame M′)ˢ
   ⊎ˢ ((Value M′)ˢ ×ˢ (∃ˢ[ V ] (M —↠ V)ˢ ×ˢ (Value V)ˢ ×ˢ (pre-𝒱 c ≻ V M′)))

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (c , dir , V , V′)) = pre-𝒱 c dir V V′
pre-ℰ⊎𝒱 (inj₂ (c , dir , M , M′)) = pre-ℰ c dir M M′

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X

𝒱⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
𝒱⟦ c ⟧ dir V V′ = ℰ⊎𝒱 (inj₁ (c , dir , V , V′))

ℰ⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
ℰ⟦ c ⟧ dir M M′ = ℰ⊎𝒱 (inj₂ (c , dir , M , M′))

ℰ≺-steps : ∀{c}{M}{M′}{k}
  → #(ℰ⟦ c ⟧ ≺ M M′) (suc k)
  → (ToVal M × (ToVal M′ ⊎ Blame M′))
    ⊎ (Blame M × Blame M′)
    ⊎ (∃[ N ] Σ[ r ∈ M —↠ N ] len r ≡ k)
ℰ≺-steps {c}{M}{M′}{k} ℰ≺MM′sk = {!!}

ℰ≻-steps : ∀{c}{M}{M′}{k}
  → #(ℰ⟦ c ⟧ ≻ M M′) (suc k)
  → (ToVal M × ToVal M′)
    ⊎ (Blame M′)
    ⊎ (∃[ N′ ] Σ[ r ∈ M′ —↠ N′ ] len r ≡ k)
ℰ≻-steps {c}{M}{M′}{k} ℰ≻MM′sk = {!!}

{-
determinism : ∀{M N}
  → (r1 : M —→ N)
  → (r2 : M —→ N)
  → r1 ≡ r2
determinism {M} {N} (ξξ (□· M₁) eq1 eq2 r1) (ξξ (□· M₂) eq3 eq4 r2)
    with eq1 | eq2 | eq3 | eq4 
... | refl | refl | refl | refl
    with deterministic r1 r2
... | refl rewrite determinism r1 r2 = refl    
determinism {M} {N} (ξξ (□· M₁) eq1 eq2 r1) (ξξ (v ·□) eq3 eq4 r2)
    with eq1 | eq2 | eq3 | eq4 
... | refl | refl | refl | refl = ⊥-elim (value-irreducible v r1)
determinism {M} {N} (ξξ (□· M₁) eq1 eq2 r1) (ξξ □⟨ G !⟩ eq3 eq4 r2)
    with eq1 | eq2 | eq3
... | refl | refl | ()
determinism {M} {N} (ξξ (□· M₁) eq1 eq2 r1) (ξξ □⟨ H ?⟩ eq3 eq4 r2)
    with eq1 | eq2 | eq3
... | refl | refl | ()
determinism {.(ƛ _ · _)} {_} (ξξ (□· M₁) eq1 eq2 r1) (β x₂)
    with eq1
... | refl = ⊥-elim (value-irreducible (ƛ̬ _) r1)
determinism {M} {N} (ξξ (v ·□) eq1 eq2 r1) r2 = {!!}
determinism {M} {N} (ξξ □⟨ G !⟩ x x₁ r1) r2 = {!!}
determinism {M} {N} (ξξ □⟨ H ?⟩ x x₁ r1) r2 = {!!}
determinism {M} {.blame} (ξξ-blame F x) r2 = {!!}
determinism {.(ƛ _ · _)} {_} (β x) r2 = {!!}
determinism {.(_ ⟨ _ ?⟩)} {N} (collapse x x₁) r2 = {!!}
determinism {.(_ ⟨ _ ?⟩)} {.blame} (collide x x₁ x₂) r2 = {!!}

triangle—↠ : ∀{L M N : Term}
   → (L→M : L —↠ M)
   → (L→N : L —↠ N)
   → (len L→M ≤ len L→N)
   → (Σ[ M→N ∈ (M —↠ N) ] (L→N ≡ (L→M ++ M→N)))
triangle—↠ (_ END) L→N m≤n  = L→N , refl 
triangle—↠ (_ —→⟨ L→M₁ ⟩ M₁→M)
            (_ —→⟨ L→M₂ ⟩ M₂→N) (s≤s m≤n)
    with deterministic L→M₁ L→M₂
... | refl
    with triangle—↠ M₁→M M₂→N m≤n
... | M→N , refl
    with determinism L→M₁ L→M₂
... | refl = M→N , refl    
-}

step-value-plus-one : ∀{M N V}
   → (M→N : M —↠ N)
   → (M→V : M —↠ V)
   → Value V
   → len M→N ≡ suc (len M→V)
   → ⊥
step-value-plus-one (_ —→⟨ r ⟩ _ END) (_ END) v eq = value-irreducible v r
step-value-plus-one (_ —→⟨ r1 ⟩ M→N) (_ —→⟨ r2 ⟩ M→V) v eq
    with deterministic r1 r2
... | refl = step-value-plus-one M→N M→V v (suc-injective eq)

step-blame-plus-one : ∀{M N}
   → (M→N : M —↠ N)
   → (M→b : M —↠ blame)
   → len M→N ≡ suc (len M→b)
   → ⊥
step-blame-plus-one (_ —→⟨ r ⟩ _ END) (_ END) eq = blame-irreducible r
step-blame-plus-one (_ —→⟨ r1 ⟩ M→N) (_ —→⟨ r2 ⟩ M→b) eq
    with deterministic r1 r2
... | refl = step-blame-plus-one M→N M→b (suc-injective eq)

diverge-not-halt : ∀{M}
  → diverge M
  → ¬ halt M
diverge-not-halt divM (inj₁ M→blame)
    with divM (suc (len M→blame))
... | N , M→N , eq = step-blame-plus-one M→N M→blame (sym eq)    
diverge-not-halt divM (inj₂ (V , M→V , v))
    with divM (suc (len M→V))
... | N , M→N , eq = step-value-plus-one M→N M→V v (sym eq)    
  

ℰ≺≻⇒GG : ∀{c}{M}{M′}
   → [] ⊢ᵒ ℰ⟦ c ⟧ ≺ M M′
   → [] ⊢ᵒ ℰ⟦ c ⟧ ≻ M M′
   → ⊨ M ⊑ M′
ℰ≺≻⇒GG{c}{M}{M′} ℰ≺MM′ ℰ≻MM′ = GG1 , GG2 , GG3 , GG4
  where
  GG1 : ToVal M′ → ToVal M
  GG1 (V′ , M′→V′ , v′)
      with ℰ≻-steps {k = suc (len M′→V′)}
                    (⊢ᵒ-elim ℰ≻MM′ (suc (suc (len M′→V′))) tt)
  ... | inj₁ ((V , M→V , v) , _) = V , M→V , v
  ... | inj₂ (inj₁ isBlame) rewrite blame—↠ M′→V′ =
        ⊥-elim (blame-not-value v′ refl)
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) =
        ⊥-elim (step-value-plus-one M′→N′ M′→V′ v′ eq)

  GG2 : diverge M′ → diverge M
  GG2 divM′ k
      with ℰ≺-steps {k = k} (⊢ᵒ-elim ℰ≺MM′ (suc k) tt)
  ... | inj₁ ((V , M→V , v) , inj₁ (V′ , M′→V′ , v′)) =
        ⊥-elim (diverge-not-halt divM′ (inj₂ (V′ , M′→V′ , v′)))
  ... | inj₁ ((V , M→V , v) , inj₂ isBlame) = {!!} {- contradiction -}
  ... | inj₂ (inj₁ (isBlame , isBlame)) = {!!}  {- contradiction -}
  ... | inj₂ (inj₂ (N , M→N , eq)) = N , M→N , sym eq

  GG3 : ToVal M → ToVal M′ ⊎ M′ —↠ blame
  GG3 (V , M→V , v)
      with ℰ≺-steps {k = suc (len M→V)} (⊢ᵒ-elim ℰ≺MM′ (suc (suc (len M→V)))tt)
  ... | inj₁ ((V , M→V , v) , inj₁ (V′ , M′→V′ , v′)) = inj₁ (V′ , M′→V′ , v′)
  ... | inj₁ ((V , M→V , v) , inj₂ isBlame) = inj₂ (blame END)
  ... | inj₂ (inj₁ (isBlame , isBlame)) = inj₂ (blame END) 
  ... | inj₂ (inj₂ (N , M→N , eq)) = {!!} {- contradiction -}

  GG4 : diverge M → diverge⊎blame M′
  GG4 divM k 
      with ℰ≻-steps {k = k} (⊢ᵒ-elim ℰ≻MM′ (suc k) tt)
  ... | inj₁ ((V , M→V , v) , _) = {!!} {- contradiction -}
  ... | inj₂ (inj₁ isBlame) = blame , (blame END) , inj₂ refl
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) = N′ , (M′→N′ , (inj₁ (sym eq))) 
