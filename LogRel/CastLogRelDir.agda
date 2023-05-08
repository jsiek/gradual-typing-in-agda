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

ℰ⇒GG : ∀{c}{M}{M′}
   → [] ⊢ᵒ ℰ⟦ c ⟧ ≺ M M′
   → [] ⊢ᵒ ℰ⟦ c ⟧ ≻ M M′
   → ⊨ M ⊑ M′
ℰ⇒GG{c}{M}{M′} ℰ≺MM′ ℰ≻MM′ = GG1 , {!!} , {!!} , {!!}
  where
  GG1 : ToVal M′ → ToVal M
  GG1 (V′ , M′→V′ , v′)
      with ℰ≻-steps {k = suc (len M′→V′)}
                    (⊢ᵒ-elim ℰ≻MM′ (suc (suc (len M′→V′))) tt)
  ... | inj₁ ((V , M→V , v) , _) = V , M→V , v
  ... | inj₂ (inj₁ isBlame) = {!!} {- contradiction -}
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) = {!!} {- contradiction -}

  
