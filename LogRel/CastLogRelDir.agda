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
   (∃ˢ[ N ] (M —→ N)ˢ ×ˢ ▷ˢ (ℰˢ⟦ c ⟧ ≺ N M′))
   ⊎ˢ (M′ —↠ blame)ˢ   -- was ((Blame M)ˢ ×ˢ (M′ —↠ blame)ˢ)
   ⊎ˢ ((Value M)ˢ ×ˢ ((M′ —↠ blame)ˢ ⊎ˢ
                    (∃ˢ[ V′ ] (M′ —↠ V′)ˢ ×ˢ (Value V′)ˢ ×ˢ (pre-𝒱 c ≺ M V′))))

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
   (∃ˢ[ N′ ] (M′ —→ N′)ˢ ×ˢ ▷ˢ (ℰˢ⟦ c ⟧ ≻ M N′))
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

ℰ-def : Prec → Dir → Term → Term → Setᵒ
ℰ-def c ≺ M M′ =
   (∃ᵒ[ N ] (M —→ N)ᵒ ×ᵒ ▷ᵒ (ℰ⟦ c ⟧ ≺ N M′))
   ⊎ᵒ (M′ —↠ blame)ᵒ  -- was ((Blame M)ᵒ ×ᵒ (M′ —↠ blame)ᵒ)
   ⊎ᵒ ((Value M)ᵒ ×ᵒ ((M′ —↠ blame)ᵒ ⊎ᵒ
                    (∃ᵒ[ V′ ] (M′ —↠ V′)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⟦ c ⟧ ≺ M V′))))
ℰ-def c ≻ M M′ =
   (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (ℰ⟦ c ⟧ ≻ M N′))
   ⊎ᵒ (Blame M′)ᵒ
   ⊎ᵒ ((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ (𝒱⟦ c ⟧ ≻ V M′)))

ℰ-stmt : ∀{c}{dir}{M}{M′} → ℰ⟦ c ⟧ dir M M′ ≡ᵒ ℰ-def c dir M M′
ℰ-stmt {c}{dir}{M}{M′} =
  ℰ⟦ c ⟧ dir M M′
                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 (X₂ dir)
                 ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 (X₂ dir) ⟩
  # (pre-ℰ⊎𝒱 (X₂ dir)) (ℰ⊎𝒱 , ttᵖ)
                 ⩦⟨ EQ{dir} ⟩
  ℰ-def c dir M M′
  ∎
  where
  X₁ : Dir → ℰ⊎𝒱-type
  X₁ = λ dir → inj₁ (c , dir , M , M′)
  X₂ = λ dir → inj₂ (c , dir , M , M′)
  EQ : ∀{dir} → # (pre-ℰ⊎𝒱 (X₂ dir)) (ℰ⊎𝒱 , ttᵖ) ≡ᵒ ℰ-def c dir M M′
  EQ {≺} = cong-⊎ᵒ (≡ᵒ-refl refl)
           (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
             (cong-∃ λ V′ → cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
              ((≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (c , ≺ , M , V′))))))))))
  EQ {≻} = cong-⊎ᵒ (≡ᵒ-refl refl) (cong-⊎ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ λ V → cong-×ᵒ (≡ᵒ-refl refl)
              (cong-×ᵒ (≡ᵒ-refl refl)
               (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (c , ≻ , V , M′))))))))

ℰ-suc : ∀{c}{dir}{M}{M′}{k}
  → #(ℰ⟦ c ⟧ dir M M′) (suc k) ⇔ #(ℰ-def c dir M M′) (suc k)
ℰ-suc {c}{dir}{M}{M′}{k} = ≡ᵒ⇒⇔{k = suc k} (ℰ-stmt{c}{dir}{M}{M′})

ℰ≺-steps : ∀{c}{M}{M′}{k}
  → #(ℰ⟦ c ⟧ ≺ M M′) (suc k)
  → (ToVal M × (ToVal M′ ⊎ (M′ —↠ blame)))
    ⊎ (M′ —↠ blame)
    ⊎ (∃[ N ] Σ[ r ∈ M —↠ N ] len r ≡ k)
ℰ≺-steps {c} {M} {M′} {zero} ℰ≺MM′sk = inj₂ (inj₂ (M , (M END) , refl))
ℰ≺-steps {c} {M} {M′} {suc k} ℰ≺MM′sk
    with ⇔-to (ℰ-suc{c}{≺}) ℰ≺MM′sk
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (m , inj₁ M′→blame)) =
      inj₁ ((M , ((M END) , m)) , (inj₂ M′→blame))
... | inj₂ (inj₂ (m , inj₂ (V′ , M′→V′ , v′ , 𝒱≺V′M))) =
      inj₁ ((M , (M END) , m) , (inj₁ (V′ , M′→V′ , v′)))
... | inj₁ (N , M→N , ▷ℰ≺NM′)
    with ℰ≺-steps ▷ℰ≺NM′
... | inj₁ ((V , M→V , v) , inj₁ (V′ , M′→V′ , v′)) =
      inj₁ ((V , (M —→⟨ M→N ⟩ M→V) , v) , (inj₁ (V′ , M′→V′ , v′)))
... | inj₁ ((V , M→V , v) , inj₂ M′→blame) =
      inj₁ ((V , (M —→⟨ M→N ⟩ M→V) , v) , (inj₂ M′→blame))
... | inj₂ (inj₁ M′→blame) =
      inj₂ (inj₁ M′→blame)
... | inj₂ (inj₂ (L , N→L , eq)) =
      inj₂ (inj₂ (L , (M —→⟨ M→N ⟩ N→L) , cong suc eq))

ℰ≻-steps : ∀{c}{M}{M′}{k}
  → #(ℰ⟦ c ⟧ ≻ M M′) (suc k)
  → (ToVal M × ToVal M′)
    ⊎ (M′ —↠ blame)
    ⊎ (∃[ N′ ] Σ[ r ∈ M′ —↠ N′ ] len r ≡ k)
ℰ≻-steps {c} {M} {M′} {zero} ℰ≻MM′sk = inj₂ (inj₂ (M′ , (M′ END) , refl))
ℰ≻-steps {c} {M} {M′} {suc k} ℰ≻MM′sk
    with ⇔-to (ℰ-suc{c}{≻}) ℰ≻MM′sk
... | inj₂ (inj₁ isBlame) =
      inj₂ (inj₁ (blame END))
... | inj₂ (inj₂ (m′ , V , M→V , v , 𝒱≻VM′)) =
      inj₁ ((V , M→V , v) , M′ , (M′ END) , m′)
... | inj₁ (N′ , M′→N′ , ▷ℰ≻MN′)
    with ℰ≻-steps ▷ℰ≻MN′
... | inj₁ ((V , M→V , v) , (V′ , N′→V′ , v′)) =
      inj₁ ((V , M→V , v) , V′ , (M′ —→⟨ M′→N′ ⟩ N′→V′) , v′)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′ —→⟨ M′→N′ ⟩ N′→blame))
... | inj₂ (inj₂ (L′ , N′→L′ , eq)) =
      inj₂ (inj₂ (L′ , (M′ —→⟨ M′→N′ ⟩ N′→L′) , cong suc eq))

cant-reduce-value-and-blame : ∀{M}{V}
   → Value V
   → M —↠ V
   → M —↠ blame
   → ⊥
cant-reduce-value-and-blame v (M END) (M —→⟨ M→N ⟩ N→b) =
  ⊥-elim (value-irreducible v M→N)
cant-reduce-value-and-blame v (.blame —→⟨ M→N ⟩ N→V) (.blame END) =
  ⊥-elim (blame-irreducible M→N)
cant-reduce-value-and-blame v (M —→⟨ M→N ⟩ N→V) (.M —→⟨ M→N′ ⟩ N′→b)
  rewrite deterministic M→N M→N′ = cant-reduce-value-and-blame v N→V N′→b

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
  ... | inj₂ (inj₁ M′→blame) =
        ⊥-elim (cant-reduce-value-and-blame v′ M′→V′ M′→blame)
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) =
        ⊥-elim (step-value-plus-one M′→N′ M′→V′ v′ eq)

  GG2 : diverge M′ → diverge M
  GG2 divM′ k
      with ℰ≺-steps {k = k} (⊢ᵒ-elim ℰ≺MM′ (suc k) tt)
  ... | inj₁ ((V , M→V , v) , inj₁ (V′ , M′→V′ , v′)) =
        ⊥-elim (diverge-not-halt divM′ (inj₂ (V′ , M′→V′ , v′)))
  ... | inj₁ ((V , M→V , v) , inj₂ M′→blame) =
        ⊥-elim (diverge-not-halt divM′ (inj₁ M′→blame))
  ... | inj₂ (inj₁ M′→blame) =
        ⊥-elim (diverge-not-halt divM′ (inj₁ M′→blame))
  ... | inj₂ (inj₂ (N , M→N , eq)) = N , M→N , sym eq

  GG3 : ToVal M → ToVal M′ ⊎ M′ —↠ blame
  GG3 (V , M→V , v)
      with ℰ≺-steps {k = suc (len M→V)} (⊢ᵒ-elim ℰ≺MM′ (suc (suc (len M→V)))tt)
  ... | inj₁ ((V , M→V , v) , inj₁ (V′ , M′→V′ , v′)) = inj₁ (V′ , M′→V′ , v′)
  ... | inj₁ ((V , M→V , v) , inj₂ M′→blame) = inj₂ M′→blame
  ... | inj₂ (inj₁ M′→blame) = inj₂ M′→blame
  ... | inj₂ (inj₂ (N , M→N , eq)) =
        ⊥-elim (step-value-plus-one M→N M→V v eq)

  GG4 : diverge M → diverge⊎blame M′
  GG4 divM k 
      with ℰ≻-steps {k = k} (⊢ᵒ-elim ℰ≻MM′ (suc k) tt)
  ... | inj₁ ((V , M→V , v) , _) =
        ⊥-elim (diverge-not-halt divM (inj₂ (V , M→V , v)))
  ... | inj₂ (inj₁ M′→blame) = blame , (M′→blame , (inj₂ refl))
  ... | inj₂ (inj₂ (N′ , M′→N′ , eq)) = N′ , (M′→N′ , (inj₁ (sym eq))) 

{- formulation with explicit step-indexing a la Max New -}

anti-reduction-≺ : ∀{c}{M}{N}{M′}{i}
  → #(ℰ⟦ c ⟧ ≺ N M′) (suc i)
  → (M→N : M —↠ N)
  → #(ℰ⟦ c ⟧ ≺ M M′) (suc (len M→N + i))
anti-reduction-≺ {c} {M} {.M} {M′} {i} ℰ≺NM′si (.M END) = ℰ≺NM′si
anti-reduction-≺ {c} {M} {N} {M′} {i} ℰ≺NM′si (_—→⟨_⟩_ M {L}{N} M→L L→*N) =
  let IH : # (ℰ⟦ c ⟧ ≺ L M′) (suc (len L→*N + i))
      IH = anti-reduction-≺ ℰ≺NM′si (L→*N) in
  inj₁ (L , M→L , IH)

anti-reduction-≻ : ∀{c}{M}{M′}{N′}{i}
  → #(ℰ⟦ c ⟧ ≻ M N′) (suc i)
  → (M′→N′ : M′ —↠ N′)
  → #(ℰ⟦ c ⟧ ≻ M M′) (suc (len M′→N′ + i))
anti-reduction-≻ {c} {M} {M′} {.M′} {i} ℰ≻MN′ (.M′ END) = ℰ≻MN′
anti-reduction-≻ {c} {M} {M′}{N′} {i} ℰ≻MN′ (_—→⟨_⟩_ M′ {L′}{N′} M′→L′ L′→*N′)=
  let IH : # (ℰ⟦ c ⟧ ≻ M L′) (suc (len L′→*N′ + i))
      IH = anti-reduction-≻ ℰ≻MN′ (L′→*N′) in
  inj₁ (L′ , M′→L′ , IH)

anti-reduction-≺-R : ∀{c}{M}{M′}{N′}{i}
  → #(ℰ⟦ c ⟧ ≺ M N′) i
  → (M′→N′ : M′ —↠ N′)
  → #(ℰ⟦ c ⟧ ≺ M M′) i
anti-reduction-≺-R {c}{M}{M′}{N′}{zero} ℰMN′ M′→N′ = tz (ℰ⟦ c ⟧ ≺ M M′)
anti-reduction-≺-R {c}{M}{M′}{N′}{suc i} ℰMN′ M′→N′
    with ℰMN′
... | inj₁ (N , M→N , ▷ℰNN′) =
         let ℰNM′si = anti-reduction-≺-R ▷ℰNN′ M′→N′ in
         inj₁ (N , M→N , ℰNM′si)
... | inj₂ (inj₁ N′→blame) = inj₂ (inj₁ (M′→N′ ++ N′→blame))
... | inj₂ (inj₂ (m , inj₁ N′→blame)) = inj₂ (inj₁ (M′→N′ ++ N′→blame))
... | inj₂ (inj₂ (m , inj₂ (V′ , N′→V′ , v′ , 𝒱MV′))) =
      inj₂ (inj₂ (m , inj₂ (V′ , (M′→N′ ++ N′→V′) , v′ , 𝒱MV′)))

anti-reduction-≻-L : ∀{c}{M}{N}{M′}{i}
  → #(ℰ⟦ c ⟧ ≻ N M′) i
  → (M→N : M —↠ N)
  → #(ℰ⟦ c ⟧ ≻ M M′) i
anti-reduction-≻-L {c} {M} {M′} {N′} {zero} ℰNM′ M→N = tz (ℰ⟦ c ⟧ ≻ M N′)
anti-reduction-≻-L {c} {M} {N}{M′}  {suc i} ℰNM′ M→N
    with ℰNM′
... | inj₁ (N′ , M′→N′ , ▷ℰMN′) =
      inj₁ (N′ , (M′→N′ , (anti-reduction-≻-L ▷ℰMN′ M→N)))
... | inj₂ (inj₁ isBlame) = inj₂ (inj₁ isBlame)
... | inj₂ (inj₂ (m′ , V , N→V , v , 𝒱VM′)) =
      inj₂ (inj₂ (m′ , V , (M→N ++ N→V) , v , 𝒱VM′))

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

{- logical formulation -}

expansion-▷-≺ : ∀{𝒫}{c}{M}{N}{M′}
  → 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ ≺ N M′)
  → M —→ N
  → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ ≺ M M′
expansion-▷-≺ {𝒫}{c}{M}{N}{M′} ⊢▷ℰNM′ M→N =
  substᵒ (≡ᵒ-sym (ℰ-stmt{c}{≺}{M}{M′}))
  (inj₁ᵒ (⊢ᵒ-∃-intro N (constᵒI M→N ,ᵒ ⊢▷ℰNM′)))

expansion-▷-≻ : ∀{𝒫}{c}{M}{M′}{N′}
  → 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ ≻ M N′)
  → M′ —→ N′
  → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ ≻ M M′
expansion-▷-≻ {𝒫}{c}{M}{M′}{N′} ⊢▷ℰMN′ M′→N′ =
  substᵒ (≡ᵒ-sym (ℰ-stmt{c}{≻}{M}{M′}))
  (inj₁ᵒ (⊢ᵒ-∃-intro N′ (constᵒI M′→N′ ,ᵒ ⊢▷ℰMN′)))

ℰ-blame : ∀{c}{dir}{M}{k}
   → #(ℰ⟦ c ⟧ dir M blame) k
ℰ-blame {c} {dir} {M} {zero} = tz (ℰ⟦ c ⟧ dir M blame)
ℰ-blame {c} {≺} {M} {suc k} = inj₂ (inj₁ (blame END))
ℰ-blame {c} {≻} {M} {suc k} = inj₂ (inj₁ isBlame)
