{-# OPTIONS --rewriting #-}
module RawLogRel.LogRel where

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
open import StepIndexedLogic
open import InjProj.CastCalculus
open import InjProj.Precision
open import InjProj.CastDeterministic
open import InjProj.Reduction
open import EquivalenceRelation

data Dir : Set where
  ≺ : Dir
  ≻ : Dir

𝒱⟦_⟧ : ∀{A}{A′}(A⊑A′ : A ⊑ A′) → Dir → Term → Term → ℕ → Set
ℰ⟦_⟧ : ∀{A}{A′}(A⊑A′ : A ⊑ A′) → Dir → Term → Term → ℕ → Set

𝒱⟦ A⊑A′ ⟧ dir V V′ zero = ⊤
𝒱⟦ unk⊑unk ⟧ dir (V ⟨ G !⟩) (V′ ⟨ H !⟩) (suc k)
    with G ≡ᵍ H
... | yes refl = (Value V) × (Value V′) × (𝒱⟦ Refl⊑{gnd⇒ty G} ⟧ dir V V′ k)
... | no neq = ⊥ 
𝒱⟦ unk⊑unk ⟧ dir V V′ (suc k) = ⊥
𝒱⟦ unk⊑{H} H⊑A′ ⟧ dir (V ⟨ G !⟩) V′ (suc k)
    with G ≡ᵍ H
... | yes refl = (Value V) × (Value V′) × (𝒱⟦ H⊑A′ ⟧ ≺ V V′ k)
... | no neq = ⊥ 
𝒱⟦ unk⊑ A⊑A′ ⟧ dir V V′ (suc k) = ⊥
𝒱⟦ base⊑ ⟧ dir ($ c) ($ c′) (suc k) =  c ≡ c′
𝒱⟦ base⊑ ⟧ dir V V′ (suc k) = ⊥
𝒱⟦ fun⊑ A⊑A′ B⊑B′ ⟧ dir (ƛ N) (ƛ N′) (suc k) =
    ∀ W W′ j → j ≤ k → (𝒱⟦ A⊑A′ ⟧ dir W W′ j)
           → (ℰ⟦ B⊑B′ ⟧ dir (N [ W ]) (N′ [ W′ ]) j) 
𝒱⟦ fun⊑ A⊑A′ A⊑A′₁ ⟧ dir V V′ (suc k) = ⊥

ℰ⟦ A⊑A′ ⟧ dir M M′ zero = ⊤
ℰ⟦ A⊑A′ ⟧ ≺ M M′ (suc k) =
   (∃[ N ] (M —→ N) × (ℰ⟦ A⊑A′ ⟧ ≺ N M′ k))
   ⊎ (M′ —↠ blame)
   ⊎ (Value M × (M′ —↠ blame
          ⊎ (∃[ V′ ] (M′ —↠ V′) × (Value V′) × (𝒱⟦ A⊑A′ ⟧ ≺ M V′ (suc k)))))
ℰ⟦ A⊑A′ ⟧ ≻ M M′ (suc k) =
   (∃[ N′ ] (M′ —→ N′) × (ℰ⟦ A⊑A′ ⟧ ≻ M N′ k))
   ⊎ (Blame M′)
   ⊎ (Value M′ × (∃[ V ] (M —↠ V) × Value V × (𝒱⟦ A⊑A′ ⟧ ≻ V M′ (suc k))))

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

   ℰ≻ accepts the following:

                         M′ (more precise)
   M           value   blame   diverge
   value         ✓       ✓       ✓
   ---------|--------|-------|---------
   blame                 ✓       ✓
   ---------|--------|-------|---------
   diverge               ✓       ✓

-}

{------------- Related values are syntactic values ----------------------------}

𝒱⇒Value : ∀ {k}{dir}{A}{A′} (A⊑A′ : A ⊑ A′) M M′
   → 𝒱⟦ A⊑A′ ⟧ dir M M′ (suc k)
     ----------------------------
   → Value M × Value M′
𝒱⇒Value {k} unk⊑unk (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
𝒱⇒Value {k}{≺} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    with G ≡ᵍ H
... | yes refl
    with 𝒱VGV′
... | v , v′ , _ = (v 〈 _ 〉) , v′
𝒱⇒Value {k}{≻} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    with G ≡ᵍ H
... | yes refl
    with 𝒱VGV′
... | v , v′ , _ = (v 〈 _ 〉) , v′
𝒱⇒Value {k} (unk⊑{H}{A′} d) (V ⟨ G !⟩) V′ 𝒱VGV′
    | no neq = ⊥-elim 𝒱VGV′
𝒱⇒Value {k} base⊑ ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
𝒱⇒Value {k} (fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱VV′ =
    (ƛ̬ N) , (ƛ̬ N′)

{----------- 𝒱 and ℰ are downwards closed ------------------------------------}

down-𝒱 : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{V}{V′}{dir}
  → downClosed (𝒱⟦ A⊑A′ ⟧ dir V V′)
down-ℰ : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}{dir}
  → downClosed (ℰ⟦ A⊑A′ ⟧ dir M M′)

down-𝒱 {A} {A′} {A⊑A′} {V} {V′} zero 𝒱VV′ .zero z≤n = tt
down-𝒱 {A} {A′} {A⊑A′} {V} {V′} (suc k) 𝒱VV′ .zero z≤n = tt
down-𝒱 {.★}{.★}{unk⊑unk}{V₁ ⟨ G !⟩}{V₁′ ⟨ H !⟩}(suc k) 𝒱VV′k (suc j)(s≤s j≤k)
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱VV′k
... | yes refl
    with 𝒱VV′k
... | v₁ , v₁′ , 𝒱V₁V₁′k =
      v₁ , v₁′ , down-𝒱 k 𝒱V₁V₁′k j j≤k 
down-𝒱 {.★}{A′}{unk⊑{H} A⊑A′}{V₁ ⟨ G !⟩}{V′} (suc k) 𝒱VV′k (suc j) (s≤s j≤k)
    with G ≡ᵍ H
... | yes refl
    with 𝒱VV′k
... | v₁ , v′ , 𝒱V₁V′ = v₁ , v′ , down-𝒱 k 𝒱V₁V′ j j≤k
down-𝒱 {_}{_}{base⊑}{$ c}{$ c′} (suc k) refl (suc j) (s≤s j≤k) = refl
down-𝒱 {_}{_} {fun⊑ A⊑A′ B⊑B′}{ƛ N} {ƛ N′} (suc k) 𝒱VV′k (suc j) (s≤s j≤k) =
    λ W W′ 𝒱WW′j →

      down-ℰ k {!!} j j≤k

down-ℰ{A}{A′}{A⊑A′}{M}{M′} = {!!}

{----------- Relate Open Terms ------------------------------------------------}

-- 𝓖⟦_⟧ : (Γ : List Prec) → Dir → Subst → Subst → List Setᵒ
-- 𝓖⟦ [] ⟧ dir σ σ′ = []
-- 𝓖⟦ c ∷ Γ ⟧ dir σ σ′ = (𝒱⟦ c ⟧ dir (σ 0) (σ′ 0))
--                      ∷ 𝓖⟦ Γ ⟧ dir (λ x → σ (suc x)) (λ x → σ′ (suc x))

-- _∣_⊨_⊑_⦂_ : List Prec → Dir → Term → Term → Prec → Set
-- Γ ∣ dir ⊨ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst)
--    → 𝓖⟦ Γ ⟧ dir γ γ′ ⊢ᵒ ℰ⟦ c ⟧ dir (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

-- _⊨_⊑_⦂_ : List Prec → Term → Term → Prec → Set
-- Γ ⊨ M ⊑ M′ ⦂ c = (Γ ∣ ≺ ⊨ M ⊑ M′ ⦂ c) × (Γ ∣ ≻ ⊨ M ⊑ M′ ⦂ c)

-- {----------- sanity checking ------------------------------------------------}

-- ℰ≺-steps : ∀{c}{M}{M′}{k}
--   → #(ℰ⟦ c ⟧ ≺ M M′) (suc k)
--   → (ToVal M × (ToVal M′ ⊎ (M′ —↠ blame)))
--     ⊎ (M′ —↠ blame)
--     ⊎ (∃[ N ] Σ[ r ∈ M —↠ N ] len r ≡ k)
-- ℰ≺-steps {c} {M} {M′} {zero} ℰ≺MM′sk = inj₂ (inj₂ (M , (M END) , refl))
-- ℰ≺-steps {c} {M} {M′} {suc k} ℰ≺MM′sk
--     with ⇔-to (ℰ-suc{c}{≺}) ℰ≺MM′sk
-- ... | inj₂ (inj₁ M′→blame) =
--       inj₂ (inj₁ M′→blame)
-- ... | inj₂ (inj₂ (m , inj₁ M′→blame)) =
--       inj₁ ((M , ((M END) , m)) , (inj₂ M′→blame))
-- ... | inj₂ (inj₂ (m , inj₂ (V′ , M′→V′ , v′ , 𝒱≺V′M))) =
--       inj₁ ((M , (M END) , m) , (inj₁ (V′ , M′→V′ , v′)))
-- ... | inj₁ (N , M→N , ▷ℰ≺NM′)
--     with ℰ≺-steps ▷ℰ≺NM′
-- ... | inj₁ ((V , M→V , v) , inj₁ (V′ , M′→V′ , v′)) =
--       inj₁ ((V , (M —→⟨ M→N ⟩ M→V) , v) , (inj₁ (V′ , M′→V′ , v′)))
-- ... | inj₁ ((V , M→V , v) , inj₂ M′→blame) =
--       inj₁ ((V , (M —→⟨ M→N ⟩ M→V) , v) , (inj₂ M′→blame))
-- ... | inj₂ (inj₁ M′→blame) =
--       inj₂ (inj₁ M′→blame)
-- ... | inj₂ (inj₂ (L , N→L , eq)) =
--       inj₂ (inj₂ (L , (M —→⟨ M→N ⟩ N→L) , cong suc eq))

-- ℰ≻-steps : ∀{c}{M}{M′}{k}
--   → #(ℰ⟦ c ⟧ ≻ M M′) (suc k)
--   → (ToVal M × ToVal M′)
--     ⊎ (M′ —↠ blame)
--     ⊎ (∃[ N′ ] Σ[ r ∈ M′ —↠ N′ ] len r ≡ k)
-- ℰ≻-steps {c} {M} {M′} {zero} ℰ≻MM′sk = inj₂ (inj₂ (M′ , (M′ END) , refl))
-- ℰ≻-steps {c} {M} {M′} {suc k} ℰ≻MM′sk
--     with ⇔-to (ℰ-suc{c}{≻}) ℰ≻MM′sk
-- ... | inj₂ (inj₁ isBlame) =
--       inj₂ (inj₁ (blame END))
-- ... | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱≻VM′)) =
--       inj₁ ((V , M→V , v) , M′ , (M′ END) , m′)
-- ... | inj₁ (N′ , M′→N′ , ▷ℰ≻MN′)
--     with ℰ≻-steps ▷ℰ≻MN′
-- ... | inj₁ ((V , M→V , v) , (V′ , N′→V′ , v′)) =
--       inj₁ ((V , M→V , v) , V′ , (M′ —→⟨ M′→N′ ⟩ N′→V′) , v′)
-- ... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′ —→⟨ M′→N′ ⟩ N′→blame))
-- ... | inj₂ (inj₂ (L′ , N′→L′ , eq)) =
--       inj₂ (inj₂ (L′ , (M′ —→⟨ M′→N′ ⟩ N′→L′) , cong suc eq))

-- {----------- ℰ implies the gradual guarantee ---------------------------------}

-- cant-reduce-value-and-blame : ∀{M}{V}
--    → Value V
--    → M —↠ V
--    → M —↠ blame
--    → ⊥
-- cant-reduce-value-and-blame v (M END) (M —→⟨ M→N ⟩ N→b) =
--   ⊥-elim (value-irreducible v M→N)
-- cant-reduce-value-and-blame v (.blame —→⟨ M→N ⟩ N→V) (.blame END) =
--   ⊥-elim (blame-irreducible M→N)
-- cant-reduce-value-and-blame v (M —→⟨ M→N ⟩ N→V) (.M —→⟨ M→N′ ⟩ N′→b)
--   rewrite deterministic M→N M→N′ = cant-reduce-value-and-blame v N→V N′→b

-- ℰ≺≻⇒GG : ∀{c}{M}{M′}
--    → [] ⊢ᵒ ℰ⟦ c ⟧ ≺ M M′
--    → [] ⊢ᵒ ℰ⟦ c ⟧ ≻ M M′
--    → ⊨ M ⊑ M′
-- ℰ≺≻⇒GG{c}{M}{M′} ℰ≺MM′ ℰ≻MM′ = GG1 , GG2 , GG3 , GG4
--   where
--   GG1 : ToVal M′ → ToVal M
--   GG1 (V′ , M′→V′ , v′)
--       with ℰ≻-steps {k = suc (len M′→V′)}
--                     (⊢ᵒ-elim ℰ≻MM′ (suc (suc (len M′→V′))) tt)
--   ... | inj₁ ((V , M→V , v) , _) = V , M→V , v
--   ... | inj₂ (inj₁ M′→blame) =
--         ⊥-elim (cant-reduce-value-and-blame v′ M′→V′ M′→blame)
--   ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) =
--         ⊥-elim (step-value-plus-one M′→N′ M′→V′ v′ eq)

--   GG2 : diverge M′ → diverge M
--   GG2 divM′ k
--       with ℰ≺-steps {k = k} (⊢ᵒ-elim ℰ≺MM′ (suc k) tt)
--   ... | inj₁ ((V , M→V , v) , inj₁ (V′ , M′→V′ , v′)) =
--         ⊥-elim (diverge-not-halt divM′ (inj₂ (V′ , M′→V′ , v′)))
--   ... | inj₁ ((V , M→V , v) , inj₂ M′→blame) =
--         ⊥-elim (diverge-not-halt divM′ (inj₁ M′→blame))
--   ... | inj₂ (inj₁ M′→blame) =
--         ⊥-elim (diverge-not-halt divM′ (inj₁ M′→blame))
--   ... | inj₂ (inj₂ (N , M→N , eq)) = N , M→N , sym eq

--   GG3 : ToVal M → ToVal M′ ⊎ M′ —↠ blame
--   GG3 (V , M→V , v)
--       with ℰ≺-steps {k = suc (len M→V)} (⊢ᵒ-elim ℰ≺MM′ (suc (suc (len M→V)))tt)
--   ... | inj₁ ((V , M→V , v) , inj₁ (V′ , M′→V′ , v′)) = inj₁ (V′ , M′→V′ , v′)
--   ... | inj₁ ((V , M→V , v) , inj₂ M′→blame) = inj₂ M′→blame
--   ... | inj₂ (inj₁ M′→blame) = inj₂ M′→blame
--   ... | inj₂ (inj₂ (N , M→N , eq)) =
--         ⊥-elim (step-value-plus-one M→N M→V v eq)

--   GG4 : diverge M → diverge⊎blame M′
--   GG4 divM k 
--       with ℰ≻-steps {k = k} (⊢ᵒ-elim ℰ≻MM′ (suc k) tt)
--   ... | inj₁ ((V , M→V , v) , _) =
--         ⊥-elim (diverge-not-halt divM (inj₂ (V , M→V , v)))
--   ... | inj₂ (inj₁ M′→blame) = blame , (M′→blame , (inj₂ refl))
--   ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) = N′ , (M′→N′ , (inj₁ (sym eq))) 

-- {----------- ℰ preserved by reduction and anti-reduction (i.e. expansion) ----}

-- {- formulation with explicit step-indexing a la Max New -}

-- anti-reduction-≺ : ∀{c}{M}{N}{M′}{i}
--   → #(ℰ⟦ c ⟧ ≺ N M′) i
--   → (M→N : M —↠ N)
--   → #(ℰ⟦ c ⟧ ≺ M M′) (len M→N + i)
-- anti-reduction-≺ {c} {M} {.M} {M′} {i} ℰ≺NM′si (.M END) = ℰ≺NM′si
-- anti-reduction-≺ {c} {M} {N} {M′} {i} ℰ≺NM′si (_—→⟨_⟩_ M {L}{N} M→L L→*N) =
--   let IH : # (ℰ⟦ c ⟧ ≺ L M′) (len L→*N + i)
--       IH = anti-reduction-≺ ℰ≺NM′si (L→*N) in
--   inj₁ (L , M→L , IH)

-- anti-reduction-≻ : ∀{c}{M}{M′}{N′}{i}
--   → #(ℰ⟦ c ⟧ ≻ M N′) i
--   → (M′→N′ : M′ —↠ N′)
--   → #(ℰ⟦ c ⟧ ≻ M M′) (len M′→N′ + i)
-- anti-reduction-≻ {c} {M} {M′} {.M′} {i} ℰ≻MN′ (.M′ END) = ℰ≻MN′
-- anti-reduction-≻ {c} {M} {M′}{N′} {i} ℰ≻MN′ (_—→⟨_⟩_ M′ {L′}{N′} M′→L′ L′→*N′)=
--   let IH : # (ℰ⟦ c ⟧ ≻ M L′) (len L′→*N′ + i)
--       IH = anti-reduction-≻ ℰ≻MN′ (L′→*N′) in
--   inj₁ (L′ , M′→L′ , IH)

-- anti-reduction-≺-R : ∀{c}{M}{M′}{N′}{i}
--   → #(ℰ⟦ c ⟧ ≺ M N′) i
--   → (M′→N′ : M′ —↠ N′)
--   → #(ℰ⟦ c ⟧ ≺ M M′) i
-- anti-reduction-≺-R {c}{M}{M′}{N′}{zero} ℰMN′ M′→N′ = tz (ℰ⟦ c ⟧ ≺ M M′)
-- anti-reduction-≺-R {c}{M}{M′}{N′}{suc i} ℰMN′ M′→N′
--     with ℰMN′
-- ... | inj₁ (N , M→N , ▷ℰNN′) =
--          let ℰNM′si = anti-reduction-≺-R ▷ℰNN′ M′→N′ in
--          inj₁ (N , M→N , ℰNM′si)
-- ... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′→N′ ++ N′→blame))
-- ... | inj₂ (inj₂ (m , inj₁ N′→blame)) = inj₂ (inj₁ (M′→N′ ++ N′→blame))
-- ... | inj₂ (inj₂ (m , inj₂ (V′ , N′→V′ , v′ , 𝒱MV′))) =
--       inj₂ (inj₂ (m , inj₂ (V′ , (M′→N′ ++ N′→V′) , v′ , 𝒱MV′)))

-- anti-reduction-≻-L : ∀{c}{M}{N}{M′}{i}
--   → #(ℰ⟦ c ⟧ ≻ N M′) i
--   → (M→N : M —↠ N)
--   → #(ℰ⟦ c ⟧ ≻ M M′) i
-- anti-reduction-≻-L {c} {M} {M′} {N′} {zero} ℰNM′ M→N = tz (ℰ⟦ c ⟧ ≻ M N′)
-- anti-reduction-≻-L {c} {M} {N}{M′}  {suc i} ℰNM′ M→N
--     with ℰNM′
-- ... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
--       inj₁ (N′ , (M′→N′ , (anti-reduction-≻-L ▷ℰMN′ M→N)))
-- ... | inj₂ (inj₁ isBlame) = inj₂ (inj₁ isBlame)
-- ... | inj₂ (inj₂ (m′ , V , N→V , v , 𝒱VM′)) =
--       inj₂ (inj₂ (m′ , V , (M→N ++ N→V) , v , 𝒱VM′))

-- anti-reduction : ∀{c}{M}{N}{M′}{N′}{i}{dir}
--   → #(ℰ⟦ c ⟧ dir N N′) i
--   → (M→N : M —→ N)
--   → (M′→N′ : M′ —→ N′)
--   → #(ℰ⟦ c ⟧ dir M M′) (suc i)
-- anti-reduction {c} {M} {N} {M′} {N′} {i} {≺} ℰNN′i M→N M′→N′ =
--   let ℰMN′si = anti-reduction-≺ ℰNN′i (unit M→N) in
--   let ℰM′N′si = anti-reduction-≺-R ℰMN′si (unit M′→N′) in
--   ℰM′N′si
-- anti-reduction {c} {M} {N} {M′} {N′} {i} {≻} ℰNN′i M→N M′→N′ =
--   let ℰM′Nsi = anti-reduction-≻ ℰNN′i (unit M′→N′) in
--   let ℰM′N′si = anti-reduction-≻-L ℰM′Nsi (unit M→N) in
--   ℰM′N′si

-- reduction-≺ : ∀{c}{M}{N}{M′}{i}
--   → #(ℰ⟦ c ⟧ ≺ M M′) (suc i)
--   → (M→N : M —→ N)
--   → #(ℰ⟦ c ⟧ ≺ N M′) i
-- reduction-≺ {c} {M} {N} {M′} {zero} ℰMM′si M→N = tz (ℰ⟦ c ⟧ ≺ N M′)
-- reduction-≺ {c} {M} {N} {M′} {suc i} ℰMM′ssi M→N
--     with ℰMM′ssi
-- ... | inj₁ (N₂ , M→N₂ , ▷ℰN₂M′) rewrite deterministic M→N M→N₂ = ▷ℰN₂M′
-- ... | inj₂ (inj₁ M′→blame) =
--       inj₂ (inj₁ M′→blame)
-- ... | inj₂ (inj₂ (m , _)) =
--       ⊥-elim (value-irreducible m M→N)

-- reduction*-≺ : ∀{c}{M}{N}{M′}{i}
--   → (M→N : M —↠ N)
--   → #(ℰ⟦ c ⟧ ≺ M M′) (len M→N + i)
--   → #(ℰ⟦ c ⟧ ≺ N M′) i
-- reduction*-≺ {c} {M} {.M} {M′} {i} (.M END) ℰMM′ = ℰMM′
-- reduction*-≺ {c} {M} {N} {M′} {i} (.M —→⟨ M→L ⟩ L→N) ℰMM′ =
--   let ℰLM′ = reduction-≺ ℰMM′ M→L in
--   reduction*-≺ L→N ℰLM′ 

-- reduction-≻ : ∀{c}{M}{N}{M′}{i}
--   → #(ℰ⟦ c ⟧ ≻ M M′) (suc i)
--   → (M→N : M —→ N)
--   → #(ℰ⟦ c ⟧ ≻ N M′) i
-- reduction-≻ {c} {M} {N} {M′} {zero} ℰMM′si M→N = tz (ℰ⟦ c ⟧ ≻ N M′)
-- reduction-≻ {c} {M} {N} {M′} {suc i} ℰMM′si M→N
--     with ℰMM′si
-- ... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
--       inj₁ (N′ , M′→N′ , reduction-≻ ▷ℰMN′ M→N)
-- ... | inj₂ (inj₁ M′→blame) = inj₂ (inj₁ M′→blame)
-- ... | inj₂ (inj₂ (m′ , V , (.V END) , v , 𝒱VM′)) =
--       ⊥-elim (value-irreducible v M→N)
-- ... | inj₂ (inj₂ (m′ , V , (.M —→⟨ M→M₁ ⟩ M₁→V) , v , 𝒱VM′))
--     with deterministic M→N M→M₁
-- ... | refl =
--     let 𝒱VM′si = down (𝒱⟦ c ⟧ ≻ V M′) (suc (suc i)) 𝒱VM′ (suc i) (n≤1+n _) in
--     inj₂ (inj₂ (m′ , V , M₁→V , v , 𝒱VM′si)) 

-- ℰ-reduction : ∀{c}{M}{N}{M′}{i}{dir}
--   → #(ℰ⟦ c ⟧ dir M M′) (suc i)
--   → (M→N : M —→ N)
--   → #(ℰ⟦ c ⟧ dir N M′) i
-- ℰ-reduction {c} {M} {N} {M′} {i} {≺} ℰMM′ M→N = reduction-≺ ℰMM′ M→N
-- ℰ-reduction {c} {M} {N} {M′} {i} {≻} ℰMM′ M→N = reduction-≻ ℰMM′ M→N

-- {- logical formulation -}

-- expansion-▷-≺ : ∀{𝒫}{c}{M}{N}{M′}
--   → 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ ≺ N M′)
--   → M —→ N
--   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ ≺ M M′
-- expansion-▷-≺ {𝒫}{c}{M}{N}{M′} ⊢▷ℰNM′ M→N =
--   substᵒ (≡ᵒ-sym (ℰ-stmt{c}{≺}{M}{M′}))
--   (inj₁ᵒ (⊢ᵒ-∃-intro N (constᵒI M→N ,ᵒ ⊢▷ℰNM′)))

-- expansion-▷-≻ : ∀{𝒫}{c}{M}{M′}{N′}
--   → 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ ≻ M N′)
--   → M′ —→ N′
--   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ ≻ M M′
-- expansion-▷-≻ {𝒫}{c}{M}{M′}{N′} ⊢▷ℰMN′ M′→N′ =
--   substᵒ (≡ᵒ-sym (ℰ-stmt{c}{≻}{M}{M′}))
--   (inj₁ᵒ (⊢ᵒ-∃-intro N′ (constᵒI M′→N′ ,ᵒ ⊢▷ℰMN′)))

-- ℰ-blame-step : ∀{c}{dir}{M}{k}
--    → #(ℰ⟦ c ⟧ dir M blame) k
-- ℰ-blame-step {c} {dir} {M} {zero} = tz (ℰ⟦ c ⟧ dir M blame)
-- ℰ-blame-step {c} {≺} {M} {suc k} = inj₂ (inj₁ (blame END))
-- ℰ-blame-step {c} {≻} {M} {suc k} = inj₂ (inj₁ isBlame)


-- {--------- Equations, intro, and elim rules for 𝒱 ----------------------------}

-- 𝒱-base : ∀{ι}{c}{c′}{dir}
--    → 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ dir ($ c) ($ c′) ≡ᵒ (c ≡ c′) ᵒ
-- 𝒱-base{ι}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

-- 𝒱-base-intro : ∀{𝒫}{ι}{c}{dir}
--    → 𝒫 ⊢ᵒ 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ dir ($ c) ($ c)
-- 𝒱-base-intro{ι}{c} = substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl)

-- 𝒱-base-elim-step : ∀{ι}{ι′}{c}{V}{V′}{dir}{k}
--   → #(𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ dir V V′) (suc k)
--   → ∃[ c ] ι ≡ ι′ × V ≡ $ c × V′ ≡ $ c
-- 𝒱-base-elim-step {ι} {.ι} {base⊑} {$ c} {$ c′} {dir} {k} refl =
--   c , refl , refl , refl

-- 𝒱-base-elim : ∀{𝒫}{ι}{ι′}{c}{V}{V′}{R}{dir}
--   → 𝒫 ⊢ᵒ 𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ dir V V′
--   → (∀ k → ι ≡ ι′ → V ≡ $ k → V′ ≡ $ k → 𝒫 ⊢ᵒ R)
--     -------------------------------------------
--   → 𝒫 ⊢ᵒ R
-- 𝒱-base-elim{𝒫}{ι}{ι′}{c}{V}{V′}{R} ⊢𝒱VV′ cont =
--   ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ → G 𝒱VV′ ⊢𝒱VV′ cont
--   where
--   G : ∀{ι}{ι′}{c}{V}{V′}{n}{dir} →  #(𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ dir V V′) (suc n)
--     → 𝒫 ⊢ᵒ 𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ dir V V′
--     → (∀ k → ι ≡ ι′ → V ≡ $ k → V′ ≡ $ k → 𝒫 ⊢ᵒ R)
--     → 𝒫 ⊢ᵒ R
--   G {ι} {.ι} {base⊑} {$ k} {$ k′} {n}{dir} refl ⊢𝒱kk cont =
--      cont k refl refl refl

-- 𝒱-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}{dir}
--    → (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ dir (ƛ N) (ƛ N′))
--       ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (𝒱⟦ A , A′ , A⊑A′ ⟧ dir W W′))
--                        →ᵒ (▷ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ dir (N [ W ]) (N′ [ W′ ])))))
-- 𝒱-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′}{dir} =
--    let X = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , dir , ƛ N , ƛ N′) in
--    (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ dir (ƛ N) (ƛ N′))  ⩦⟨ ≡ᵒ-refl refl ⟩
--    ℰ⊎𝒱 X                                              ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
--    # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                                 ⩦⟨ ≡ᵒ-refl refl ⟩
--    (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (𝒱⟦ A , A′ , A⊑A′ ⟧ dir W W′))
--                  →ᵒ (▷ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ dir (N [ W ]) (N′ [ W′ ]))))) ∎

-- 𝒱-fun-elim-step : ∀{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{dir}{k}{j}
--   → #(𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′) (suc k)
--   → j ≤ k
--   → ∃[ N ] ∃[ N′ ] V ≡ ƛ N × V′ ≡ ƛ N′ 
--       × (∀{W W′} → # (𝒱⟦ A , A′ , c ⟧ dir W W′) j
--                  → # (ℰ⟦ B , B′ , d ⟧ dir (N [ W ]) (N′ [ W′ ])) j)
-- 𝒱-fun-elim-step {A}{B}{A′}{B′}{c}{d}{ƛ N}{ƛ N′}{dir}{k}{j} 𝒱VV′ j≤k =
--   N , N′ , refl , refl , λ {W}{W′} 𝒱WW′ →
--     let 𝒱λNλN′sj = down (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir (ƛ N) (ƛ N′))
--                         (suc k) 𝒱VV′ (suc j) (s≤s j≤k) in
--     let ℰNWN′W′j = 𝒱λNλN′sj W W′ (suc j) ≤-refl 𝒱WW′ in
--     ℰNWN′W′j

-- 𝒱-fun-elim : ∀{𝒫}{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{R}{dir}
--    → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′
--    → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
--              → (∀{W W′} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A , A′ , c ⟧ dir W W′))
--                           →ᵒ (▷ᵒ (ℰ⟦ B , B′ , d ⟧ dir (N [ W ]) (N′ [ W′ ]))))
--              → 𝒫 ⊢ᵒ R)
--      --------------------------------------------------------------------
--    → 𝒫 ⊢ᵒ R
-- 𝒱-fun-elim {𝒫}{A}{B}{A′}{B′}{c}{d}{V}{V′}{R}{dir} ⊢𝒱VV′ cont =
--   ⊢ᵒ-sucP ⊢𝒱VV′ λ { 𝒱VV′sn → G {V}{V′} 𝒱VV′sn ⊢𝒱VV′ cont }
--   where
--   G : ∀{V}{V′}{n}
--      → # (𝒱⟦  A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′) (suc n)
--      → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′
--      → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
--              → (∀{W W′} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A , A′ , c ⟧ dir W W′))
--                            →ᵒ (▷ᵒ (ℰ⟦ B , B′ , d ⟧ dir (N [ W ]) (N′ [ W′ ]))))
--              → 𝒫 ⊢ᵒ R)
--      → 𝒫 ⊢ᵒ R
--   G {ƛ N}{ƛ N′}{n} 𝒱VV′ ⊢𝒱VV′ cont = cont N N′ refl refl λ {W}{W′} →
--      instᵒ (instᵒ (substᵒ 𝒱-fun ⊢𝒱VV′) W) W′ 

-- 𝒱-dyn-any-≻ : ∀{V}{V′}{G}{A′}{d : gnd⇒ty G ⊑ A′}
--    → 𝒱⟦ ★ , A′ , unk⊑{G}{A′} d ⟧ ≻ (V ⟨ G !⟩) V′ 
--      ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≻ V V′)
-- 𝒱-dyn-any-≻ {V}{V′}{G}{A′}{d} = 
--   𝒱⟦ ★ , A′ , unk⊑ d ⟧ ≻ (V ⟨ G !⟩) V′
--      ⩦⟨ ≡ᵒ-refl refl ⟩
--   ℰ⊎𝒱 X
--     ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X  ⟩
--   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
--     ⩦⟨ Goal ⟩
--   (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≻ V V′)
--   ∎
--   where
--   X = inj₁ ((★ , A′ , unk⊑ d) , ≻ , (V ⟨ G !⟩) , V′)
--   Goal : # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
--          ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≻ V V′)
--   Goal
--       with G ≡ᵍ G
--   ... | yes refl = cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
--             (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱
--                         (inj₁ ((gnd⇒ty G , A′ , d) , ≻ , V , V′)))))
--   ... | no neq = ⊥-elim (neq refl)

-- 𝒱-dyn-any-≺ : ∀{V}{V′}{G}{A′}{d : gnd⇒ty G ⊑ A′}
--    → 𝒱⟦ ★ , A′ , unk⊑{G}{A′} d ⟧ ≺ (V ⟨ G !⟩) V′ 
--      ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≺ V V′)
-- 𝒱-dyn-any-≺ {V}{V′}{G}{A′}{d} = 
--   𝒱⟦ ★ , A′ , unk⊑ d ⟧ ≺ (V ⟨ G !⟩) V′
--      ⩦⟨ ≡ᵒ-refl refl ⟩
--   ℰ⊎𝒱 X
--     ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X  ⟩
--   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
--     ⩦⟨ Goal ⟩
--   (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≺ V V′)
--   ∎
--   where
--   X = inj₁ ((★ , A′ , unk⊑ d) , ≺ , (V ⟨ G !⟩) , V′)
--   Goal : # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
--          ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ (gnd⇒ty G , A′ , d) ⟧ ≺ V V′)
--   Goal
--       with G ≡ᵍ G
--   ... | yes refl = (≡ᵒ-refl refl)
--   ... | no neq = ⊥-elim (neq refl)

-- 𝒱-dyn-any-elim-step-≻ : ∀{V}{V′}{k}{H}{A′}{c : gnd⇒ty H ⊑ A′}
--    → #(𝒱⟦ ★ , A′ , unk⊑ c ⟧ ≻ V V′) (suc k)
--    → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
--              × #(𝒱⟦ gnd⇒ty H , A′ , c ⟧ ≻ V₁ V′) (suc k)
-- 𝒱-dyn-any-elim-step-≻ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
--     with G ≡ᵍ H
-- ... | no neq = ⊥-elim 𝒱VGV′
-- ... | yes refl
--     with 𝒱VGV′
-- ... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′

-- 𝒱-dyn-any-elim-step-≺ : ∀{V}{V′}{k}{H}{A′}{c : gnd⇒ty H ⊑ A′}
--    → #(𝒱⟦ ★ , A′ , unk⊑ c ⟧ ≺ V V′) (suc k)
--    → ∃[ V₁ ] V ≡ V₁ ⟨ H !⟩ × Value V₁ × Value V′
--              × #(𝒱⟦ gnd⇒ty H , A′ , c ⟧ ≺ V₁ V′) k
-- 𝒱-dyn-any-elim-step-≺ {V ⟨ G !⟩}{V′}{k}{H}{A′}{c} 𝒱VGV′
--     with G ≡ᵍ H
-- ... | no neq = ⊥-elim 𝒱VGV′
-- ... | yes refl
--     with 𝒱VGV′
-- ... | v , v′ , 𝒱VV′ = V , refl , v , v′ , 𝒱VV′

-- 𝒱-dyn-dyn : ∀{V}{V′}{G}{dir}
--    → 𝒱⟦ ★ , ★ , unk⊑unk ⟧ dir (V ⟨ G !⟩) (V′ ⟨ G !⟩)
--      ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
--          ×ᵒ (▷ᵒ (𝒱⟦ (gnd⇒ty G , gnd⇒ty G , Refl⊑) ⟧ dir V V′))
-- 𝒱-dyn-dyn {V}{V′}{G}{dir} =
--   let X = inj₁ ((★ , ★ , unk⊑unk) , dir , (V ⟨ G !⟩) , (V′ ⟨ G !⟩)) in 
--   𝒱⟦ ★ , ★ , unk⊑unk ⟧ dir (V ⟨ G !⟩) (V′ ⟨ G !⟩)
--     ⩦⟨ ≡ᵒ-refl refl ⟩
--   ℰ⊎𝒱 X
--     ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X  ⟩
--   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
--     ⩦⟨ EQ ⟩
--    (Value V)ᵒ ×ᵒ (Value V′)ᵒ
--          ×ᵒ (▷ᵒ (𝒱⟦ (gnd⇒ty G , gnd⇒ty G , Refl⊑) ⟧ dir V V′)) ∎
--   where
--   X = inj₁ ((★ , ★ , unk⊑unk) , dir , (V ⟨ G !⟩) , (V′ ⟨ G !⟩))
--   EQ : # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
--     ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
--          ×ᵒ (▷ᵒ (𝒱⟦ (gnd⇒ty G , gnd⇒ty G , Refl⊑) ⟧ dir V V′))
--   EQ
--       with G ≡ᵍ G
--   ... | yes refl = ≡ᵒ-refl refl
--   ... | no neq = ⊥-elim (neq refl)

-- 𝒱-dyn-R-step-≻ : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}
--    → #(𝒱⟦ ★ , gnd⇒ty G , c ⟧ ≻ V V′) k
--    → #(𝒱⟦ ★ , ★ , unk⊑unk ⟧ ≻ V (V′ ⟨ G !⟩)) k
-- 𝒱-dyn-R-step-≻ {G} {c} {V} {V′} {zero} 𝒱VV′ =
--      tz (𝒱⟦ ★ , ★ , unk⊑unk ⟧ ≻ V (V′ ⟨ G !⟩))
-- 𝒱-dyn-R-step-≻ {G} {c} {V} {V′} {suc k} 𝒱VV′
--     with unk⊑gnd-inv c
-- ... | d , refl
--     with 𝒱-dyn-any-elim-step-≻ {V}{V′}{k}{G}{_}{d} 𝒱VV′
-- ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′
--     with G ≡ᵍ G
-- ... | no neq = ⊥-elim 𝒱VV′
-- ... | yes refl
--     with gnd-prec-unique d Refl⊑
-- ... | refl =
--     let 𝒱V₁V′k = down (𝒱⟦ gnd⇒ty G , gnd⇒ty G , d ⟧ ≻ V₁ V′)
--                        (suc k) 𝒱V₁V′ k (n≤1+n k) in
--     v₁ , v′ , 𝒱V₁V′k

-- 𝒱-dyn-R-step-≺ : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}
--    → #(𝒱⟦ ★ , gnd⇒ty G , c ⟧ ≺ V V′) k
--    → #(𝒱⟦ ★ , ★ , unk⊑unk ⟧ ≺ V (V′ ⟨ G !⟩)) k
-- 𝒱-dyn-R-step-≺ {G} {c} {V} {V′} {zero} 𝒱VV′ =
--      tz (𝒱⟦ ★ , ★ , unk⊑unk ⟧ ≺ V (V′ ⟨ G !⟩))
-- 𝒱-dyn-R-step-≺ {G} {c} {V} {V′} {suc k} 𝒱VV′
--     with unk⊑gnd-inv c
-- ... | d , refl
--     with 𝒱-dyn-any-elim-step-≺ {V}{V′}{k}{G}{_}{d} 𝒱VV′
-- ... | V₁ , refl , v₁ , v′ , 𝒱V₁V′
--     with G ≡ᵍ G
-- ... | no neq = ⊥-elim 𝒱VV′
-- ... | yes refl
--     with gnd-prec-unique d Refl⊑
-- ... | refl = v₁ , v′ , 𝒱V₁V′           {- No use of down! -}

-- 𝒱-dyn-R-step : ∀{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}{k}{dir}
--    → #(𝒱⟦ ★ , gnd⇒ty G , c ⟧ dir V V′) k
--    → #(𝒱⟦ ★ , ★ , unk⊑unk ⟧ dir V (V′ ⟨ G !⟩)) k
-- 𝒱-dyn-R-step {G} {c} {V} {V′} {k} {≺} 𝒱VV′ =
--     𝒱-dyn-R-step-≺{G} {c} {V} {V′} {k} 𝒱VV′ 
-- 𝒱-dyn-R-step {G} {c} {V} {V′} {k} {≻} 𝒱VV′ =
--    𝒱-dyn-R-step-≻{G} {c} {V} {V′} {k} 𝒱VV′

-- 𝒱-dyn-L-step : ∀{G}{A′}{c : gnd⇒ty G ⊑ A′}{V}{V′}{dir}{k}
--    → #(𝒱⟦ gnd⇒ty G , A′ , c ⟧ dir V V′) k
--    → #(𝒱⟦ ★ , A′ , unk⊑ c ⟧ dir (V ⟨ G !⟩) V′) k
-- 𝒱-dyn-L-step {G}{A′}{c}{V}{V′}{dir}{zero} 𝒱VV′k =
--     tz (𝒱⟦ ★ , A′ , unk⊑ c ⟧ dir (V ⟨ G !⟩) V′)
-- 𝒱-dyn-L-step {G} {A′} {c} {V} {V′} {≺} {suc k} 𝒱VV′sk
--     with G ≡ᵍ G
-- ... | no neq = ⊥-elim (neq refl)
-- ... | yes refl =
--     let (v , v′) = 𝒱⇒Value (gnd⇒ty G , A′ , c) V V′ 𝒱VV′sk in
--     let 𝒱VV′k = down (𝒱⟦ gnd⇒ty G , A′ , c ⟧ ≺ V V′) (suc k) 𝒱VV′sk
--                       k (n≤1+n k) in
--     v , v′ , 𝒱VV′k
-- 𝒱-dyn-L-step {G} {A′} {c} {V} {V′} {≻} {suc k} 𝒱VV′k
--     with G ≡ᵍ G
-- ... | no neq = ⊥-elim (neq refl)
-- ... | yes refl =
--       let (v , v′) = 𝒱⇒Value (gnd⇒ty G , A′ , c) V V′ 𝒱VV′k in
--       v , v′ , 𝒱VV′k

-- {--------------- Related values are related expressions -----------------------}

-- 𝒱⇒ℰ-step : ∀{c : Prec}{V V′}{dir}{k}
--    → #(𝒱⟦ c ⟧ dir V V′) k
--      ---------------------
--    → #(ℰ⟦ c ⟧ dir V V′) k
-- 𝒱⇒ℰ-step {c} {V} {V′} {dir} {zero} 𝒱VV′k = tz (ℰ⟦ c ⟧ dir V V′)
-- 𝒱⇒ℰ-step {c} {V} {V′} {≺} {suc k} 𝒱VV′sk =
--   ⇔-fro (ℰ-suc{c}{≺})
--   (let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′sk in
--   (inj₂ (inj₂ (v , inj₂ (V′ , (V′ END) , v′ , 𝒱VV′sk)))))
-- 𝒱⇒ℰ-step {c} {V} {V′} {≻} {suc k} 𝒱VV′sk =
--   ⇔-fro (ℰ-suc{c}{≻})
--   (let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′sk in
--   inj₂ (inj₂ (v′ , V , (V END) , v , 𝒱VV′sk)))

-- 𝒱⇒ℰ : ∀{c : Prec}{𝒫}{V V′}{dir}
--    → 𝒫 ⊢ᵒ 𝒱⟦ c ⟧ dir V V′
--      ---------------------
--    → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ dir V V′
-- 𝒱⇒ℰ {c}{𝒫}{V}{V′}{≺} ⊢𝒱VV′ = substᵒ (≡ᵒ-sym ℰ-stmt)
--   (⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ →
--   let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
--   (inj₂ᵒ (inj₂ᵒ (constᵒI v ,ᵒ
--    inj₂ᵒ (⊢ᵒ-∃-intro-new (λ X → (V′ —↠ X)ᵒ ×ᵒ (Value X)ᵒ ×ᵒ (𝒱⟦ c ⟧ ≺ V X))
--             V′ (constᵒI (V′ END) ,ᵒ
--             (constᵒI v′ ,ᵒ ⊢𝒱VV′)))))))
-- 𝒱⇒ℰ {c}{𝒫}{V}{V′}{≻} ⊢𝒱VV′ = substᵒ (≡ᵒ-sym ℰ-stmt)
--   (⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ →
--   let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
--   (inj₂ᵒ (inj₂ᵒ (constᵒI v′ ,ᵒ
--    (⊢ᵒ-∃-intro-new (λ X → (V —↠ X)ᵒ ×ᵒ (Value X)ᵒ ×ᵒ (𝒱⟦ c ⟧ ≻ X V′))
--             V (constᵒI (V END) ,ᵒ
--             (constᵒI v ,ᵒ ⊢𝒱VV′)))))))

-- {--------------- Blame on the right -------------------------------------------}

-- ℰ-blame : ∀{𝒫}{c}{M}{dir} → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ dir M blame
-- ℰ-blame {𝒫}{c}{M}{dir} = ⊢ᵒ-intro λ n x → ℰ-blame-step{c}{dir}
