open import Types hiding (_⊔_)
open import Labels
open import Variables
open import CastStructure
import EfficientParamCasts
open import Data.Bool using (Bool; true; false)
open import Data.Nat {-using (ℕ; _≤_; _⊔_; z≤n; s≤s)-}
open import Data.Nat.Properties
open import Data.Nat.Solver
open Data.Nat.Properties.≤-Reasoning
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
     renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)

{-

  A proof that the Efficient Parameterized Cast Calculus
  is indeed space efficient.

  Proof idea:

  In contexts that are not eligible for reduction such as underneath a
  lambda or in the branch of an if or case expression, we only allow
  up to 2 casts in a sequence. We count a variable as a cast because
  when we substitute a value for a variable, the value may have one cast.

  In contexts that are eligible for reduction, we allow up to 3 casts
  in sequence. The worst-case scenario is when there is a β reduction
  underneath a single cast, where the argument is a value with one
  cast at the top and the body of the lambda is the lambda's parameter
  with one cast around it. In this scenario, the contractum has 3
  casts in a row.

-}

module SpaceEfficient (ecs : EfficientCastStruct) where

  open EfficientCastStruct ecs
  open EfficientParamCasts ecs

  import ParamCastCalculus
  open ParamCastCalculus Cast
  open import EfficientParamCastAux precast

  data _∣_⊢_ok : ∀{Γ A} → ℕ → Bool → Γ ⊢ A  → Set where
    castulOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}
             → n ∣ true ⊢ M ok  →  n ≤ 1
             → suc n ∣ true ⊢ M ⟨ c ⟩ ok
    castOK : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}
             → n ∣ false ⊢ M ok  →  n ≤ 2
             → suc n ∣ false ⊢ M ⟨ c ⟩ ok
    varOK : ∀{Γ A}{∋x : Γ ∋ A}{ul}
           {- We pre-count a 1 here because a value may have 1 cast
              and get substituted for this variable. -}
          → 1 ∣ ul ⊢ (` ∋x) ok
    lamOK : ∀{Γ B A}{N : Γ , A ⊢ B}{n}{ul}
          → n ∣ true ⊢ N ok
          → 0 ∣ ul ⊢ (ƛ N) ok
    appOK : ∀{Γ A B}{L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}{ul}{n}{m}
          → n ∣ ul ⊢ L ok → m ∣ ul ⊢ M ok
          → 0 ∣ ul ⊢ (L · M) ok
    litOK : ∀{Γ : Context}{A}{r : rep A}{p : Prim A}{ul}
          → 0 ∣ ul ⊢ ($_ {Γ} r {p}) ok
    ifOK : ∀{Γ A}{L : Γ ⊢ ` 𝔹}{M N : Γ ⊢ A}{n m k}{ul}
          → n ∣ ul ⊢ L ok → m ∣ true ⊢ M ok → k ∣ true ⊢ N ok
          → 0 ∣ ul ⊢ (if L M N) ok
    consOK : ∀{Γ A B}{M : Γ ⊢ A}{N : Γ ⊢ B}{n m}{ul}
          → n ∣ ul ⊢ M ok → m ∣ ul ⊢ N ok
          → 0 ∣ ul ⊢ (cons M N) ok
    fstOK : ∀{Γ A B}{M : Γ ⊢ A `× B}{n}{ul}
          → n ∣ ul ⊢ M ok
          → 0 ∣ ul ⊢ fst M ok
    sndOK : ∀{Γ A B}{M : Γ ⊢ A `× B}{n}{ul}
          → n ∣ ul ⊢ M ok
          → 0 ∣ ul ⊢ snd M ok
    inlOK : ∀{Γ A B}{M : Γ ⊢ A}{n}{ul}
          → n ∣ ul ⊢ M ok
          → 0 ∣ ul ⊢ (inl {B = B} M) ok
    inrOK : ∀{Γ A B}{M : Γ ⊢ B}{n}{ul}
          → n ∣ ul ⊢ M ok
          → 0 ∣ ul ⊢ (inr {A = A} M) ok
    caseOK : ∀{Γ A B C}{L : Γ ⊢ A `⊎ B}{M : Γ ⊢ A ⇒ C}{N : Γ ⊢ B ⇒ C}{n m k}{ul}
           → n ∣ ul ⊢ L ok → m ∣ true ⊢ M ok → k ∣ true ⊢ N ok
           → 0 ∣ ul ⊢ (case L M N) ok
    blameOK : ∀{Γ A ℓ}{ul}
           → 0 ∣ ul ⊢ (blame {Γ}{A} ℓ) ok

  simple→ok0 : ∀{Γ A}{M : Γ ⊢ A}{n}
    → SimpleValue M → n ∣ false ⊢ M ok → n ≡ 0
  simple→ok0 V-ƛ (lamOK Mok) = refl
  simple→ok0 V-const litOK = refl
  simple→ok0 (V-pair x x₁) (consOK y z) = refl
  simple→ok0 (V-inl x) (inlOK y) = refl
  simple→ok0 (V-inr x) (inrOK y) = refl

  value→ok1 : ∀{Γ A}{M : Γ ⊢ A}{n}
    → Value M → n ∣ false ⊢ M ok → n ≤ 1
  value→ok1 (S-val x) Mok
      with simple→ok0 x Mok
  ... | refl = z≤n
  value→ok1 (V-cast vV) (castOK Vok z) 
      with simple→ok0 vV Vok
  ... | refl = s≤s z≤n

  value-strengthen-ok : ∀{Γ A}{M : Γ ⊢ A}{n}
    → Value M → n ∣ false ⊢ M ok → n ∣ true ⊢ M ok

  simple-strengthen-ok : ∀{Γ A}{M : Γ ⊢ A}{n}
    → SimpleValue M → n ∣ false ⊢ M ok → n ∣ true ⊢ M ok
  simple-strengthen-ok V-ƛ (lamOK Nok) = lamOK Nok
  simple-strengthen-ok V-const litOK = litOK
  simple-strengthen-ok (V-pair x x₁) (consOK a b) =
     consOK (value-strengthen-ok x a) (value-strengthen-ok x₁ b)
  simple-strengthen-ok (V-inl x) (inlOK a) = inlOK (value-strengthen-ok x a)
  simple-strengthen-ok (V-inr x) (inrOK a) = inrOK (value-strengthen-ok x a)

  value-strengthen-ok (S-val x) Mok = simple-strengthen-ok x Mok
  value-strengthen-ok (V-cast x) (castOK Mok lt) =
    let Mok2 = (simple-strengthen-ok x Mok) in
    castulOK Mok2 (value→ok1 (S-val x) Mok)

  weaken-OK-ul : ∀{Γ A}{M : Γ ⊢ A}{n}
       → n ∣ true ⊢ M ok  →  n ∣ false ⊢ M ok
  weaken-OK-ul (castulOK Mok lt) =
     castOK (weaken-OK-ul Mok) (≤-trans lt (s≤s z≤n))
  weaken-OK-ul varOK = varOK
  weaken-OK-ul (lamOK Mok) = lamOK Mok
  weaken-OK-ul (appOK Mok Mok₁) = appOK (weaken-OK-ul Mok) (weaken-OK-ul Mok₁)
  weaken-OK-ul litOK = litOK
  weaken-OK-ul (ifOK Mok Mok₁ Mok₂) = ifOK (weaken-OK-ul Mok) Mok₁ Mok₂
  weaken-OK-ul (consOK Mok Mok₁) = consOK (weaken-OK-ul Mok) (weaken-OK-ul Mok₁)
  weaken-OK-ul (fstOK Mok) = fstOK (weaken-OK-ul Mok)
  weaken-OK-ul (sndOK Mok) = sndOK (weaken-OK-ul Mok)
  weaken-OK-ul (inlOK Mok) = inlOK (weaken-OK-ul Mok)
  weaken-OK-ul (inrOK Mok) = inrOK (weaken-OK-ul Mok)
  weaken-OK-ul (caseOK Mok Mok₁ Mok₂) = caseOK (weaken-OK-ul Mok) Mok₁ Mok₂
  weaken-OK-ul blameOK = blameOK
       
  OK-ul→2 : ∀{Γ A}{M : Γ ⊢ A}{n}
       → n ∣ true ⊢ M ok → n ≤ 2
  OK-ul→2 (castulOK Mok lt) = s≤s lt
  OK-ul→2 varOK = s≤s z≤n
  OK-ul→2 (lamOK Mok) = z≤n
  OK-ul→2 (appOK Mok Mok₁) = z≤n
  OK-ul→2 litOK = z≤n
  OK-ul→2 (ifOK Mok Mok₁ Mok₂) = z≤n
  OK-ul→2 (consOK Mok Mok₁) = z≤n
  OK-ul→2 (fstOK Mok) = z≤n
  OK-ul→2 (sndOK Mok) = z≤n
  OK-ul→2 (inlOK Mok) = z≤n
  OK-ul→2 (inrOK Mok) = z≤n
  OK-ul→2 (caseOK Mok Mok₁ Mok₂) = z≤n
  OK-ul→2 blameOK = z≤n
  
  OK→3 : ∀{Γ A}{M : Γ ⊢ A}{n}{ul}
       → n ∣ ul ⊢ M ok → n ≤ 3
  OK→3 (castulOK Mok lt) = s≤s (≤-step lt)
  OK→3 (castOK Mok x) = s≤s x
  OK→3 varOK = s≤s z≤n
  OK→3 (lamOK Mok) = z≤n
  OK→3 (appOK Mok Mok₁) = z≤n
  OK→3 litOK = z≤n
  OK→3 (ifOK Mok Mok₁ Mok₂) = z≤n
  OK→3 (consOK Mok Mok₁) = z≤n
  OK→3 (fstOK Mok) = z≤n
  OK→3 (sndOK Mok) = z≤n
  OK→3 (inlOK Mok) = z≤n
  OK→3 (inrOK Mok) = z≤n
  OK→3 (caseOK Mok Mok₁ Mok₂) = z≤n
  OK→3 blameOK = z≤n

  rename-ok : ∀{Γ Δ A}{M : Γ ⊢ A}{n}{ul}{ρ : ∀{B} → Γ ∋ B → Δ ∋ B}
          → n ∣ ul ⊢ M ok
          → n ∣ ul ⊢ rename ρ M ok
  rename-ok (castulOK Mok x) = castulOK (rename-ok Mok) x
  rename-ok (castOK Mok x) = castOK (rename-ok Mok) x
  rename-ok varOK = varOK
  rename-ok (lamOK Mok) = lamOK (rename-ok Mok)
  rename-ok (appOK Mok Mok₁) = appOK (rename-ok Mok) (rename-ok Mok₁)
  rename-ok litOK = litOK
  rename-ok (ifOK Mok Mok₁ Mok₂) =
     ifOK (rename-ok Mok) (rename-ok Mok₁) (rename-ok Mok₂)
  rename-ok (consOK Mok Mok₁) = consOK (rename-ok Mok) (rename-ok Mok₁)
  rename-ok (fstOK Mok) = fstOK (rename-ok Mok)
  rename-ok (sndOK Mok) = sndOK (rename-ok Mok)
  rename-ok (inlOK Mok) = inlOK (rename-ok Mok)
  rename-ok (inrOK Mok) = inrOK (rename-ok Mok)
  rename-ok (caseOK Mok Mok₁ Mok₂) =
     caseOK (rename-ok Mok) (rename-ok Mok₁) (rename-ok Mok₂)
  rename-ok blameOK = blameOK

  SubstOK : ∀ {Γ Δ}(σ : ∀{B} → Γ ∋ B → Δ ⊢ B) → Set
  SubstOK {Γ}{Δ} σ = (∀{A}(x : Γ ∋ A) → (Σ[ m ∈ ℕ ] m ∣ true ⊢ σ x ok × m ≤ 1))

  exts-ok : ∀ {Γ Δ A} {σ : ∀{B} → Γ ∋ B → Δ ⊢ B}
      → SubstOK σ
      → SubstOK (exts σ {B = A})
  exts-ok σok Z = ⟨ 1 , ⟨ varOK , (s≤s z≤n) ⟩ ⟩
  exts-ok σok (S ∋x)
      with σok ∋x
  ... | ⟨ k , ⟨ ok , lt ⟩ ⟩ =
        ⟨ k , ⟨ rename-ok ok , lt ⟩ ⟩

  sub-ok : ∀ {Γ Δ A} (N : Γ ⊢ A) {n : ℕ} {σ : ∀{B} → Γ ∋ B → Δ ⊢ B} {ul}
      → n ∣ ul ⊢ N ok
      → SubstOK σ
      → Σ[ k ∈ ℕ ] k ∣ ul ⊢ subst σ N ok  ×  k ≤ n
  sub-ok (M ⟨ c ⟩) (castulOK Mok lt) σok
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩ =
        ⟨ suc m1 , ⟨ castulOK σMok (≤-trans m1≤ lt) , s≤s m1≤ ⟩ ⟩
  sub-ok (M ⟨ c ⟩) (castOK Mok lt) σok
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩ =
        ⟨ suc m1 , ⟨ (castOK σMok (≤-trans m1≤ lt)) , s≤s m1≤ ⟩ ⟩
  sub-ok (` x) (varOK{ul = true}) σok = σok x
  sub-ok (` x) (varOK{ul = false}) σok
      with σok x
  ... | ⟨ k , ⟨ σxok , lt ⟩ ⟩ = ⟨ k , ⟨ weaken-OK-ul σxok , lt ⟩ ⟩
  sub-ok (ƛ N) (lamOK Nok) σok
      with sub-ok N Nok (exts-ok σok)
  ... | ⟨ k , ⟨ σNok , lt ⟩ ⟩ =      
       ⟨ zero , ⟨ (lamOK σNok) , z≤n ⟩ ⟩
  sub-ok (L · M) (appOK Lok Mok) σok
      with sub-ok L Lok σok
  ... | ⟨ l1 , ⟨ σLok , l1≤ ⟩ ⟩
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩ =
      ⟨ zero , ⟨ (appOK σLok σMok) , z≤n ⟩ ⟩
  sub-ok ($_ r {p}) litOK σok = ⟨ zero , ⟨ litOK , z≤n ⟩ ⟩
  sub-ok (if L M N) (ifOK Lok Mok Nok) σok
      with sub-ok L Lok σok
  ... | ⟨ l1 , ⟨ σLok , l1≤ ⟩ ⟩
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩
      with sub-ok N Nok σok
  ... | ⟨ n1 , ⟨ σNok , n1≤ ⟩ ⟩ =
      ⟨ zero , ⟨ (ifOK σLok σMok σNok) , z≤n ⟩ ⟩
  sub-ok (cons M N) (consOK Mok Nok) σok
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩
      with sub-ok N Nok σok
  ... | ⟨ n1 , ⟨ σNok , n1≤ ⟩ ⟩ =
      ⟨ zero , ⟨ (consOK σMok σNok) , z≤n ⟩ ⟩
  sub-ok (fst M) (fstOK Mok) σok
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩ = ⟨ zero , ⟨ (fstOK σMok) , z≤n ⟩ ⟩
  sub-ok (snd M) (sndOK Mok) σok
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩ = ⟨ zero , ⟨ (sndOK σMok) , z≤n ⟩ ⟩
  sub-ok (inl M) (inlOK Mok) σok
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩ = ⟨ zero , ⟨ (inlOK σMok) , z≤n ⟩ ⟩
  sub-ok (inr M) (inrOK Mok) σok
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩ = ⟨ zero , ⟨ (inrOK σMok) , z≤n ⟩ ⟩
  sub-ok (case L M N) (caseOK Lok Mok Nok) σok
      with sub-ok L Lok σok
  ... | ⟨ l1 , ⟨ σLok , l1≤ ⟩ ⟩
      with sub-ok M Mok σok
  ... | ⟨ m1 , ⟨ σMok , m1≤ ⟩ ⟩
      with sub-ok N Nok σok
  ... | ⟨ n1 , ⟨ σNok , n1≤ ⟩ ⟩ =
      ⟨ zero , ⟨ (caseOK σLok σMok σNok) , z≤n ⟩ ⟩
  sub-ok (blame ℓ) blameOK σok = ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩


  SubstZeroOK : ∀ {Γ A} (M : Γ ⊢ A) {m : ℕ}
         → m ∣ false ⊢ M ok → m ≤ 1 → Value M
         → SubstOK (subst-zero M)
  SubstZeroOK M {m = m} Mok m≤1 vM Z =
      ⟨ m , ⟨ value-strengthen-ok vM Mok , m≤1 ⟩ ⟩
  SubstZeroOK M Mok m≤1 vM (S ∋x) = ⟨ 1 , ⟨ varOK , (s≤s z≤n) ⟩ ⟩

  subst-ok : ∀ {Γ A B} (N : Γ , A ⊢ B) (M : Γ ⊢ A) {n m : ℕ}{ul}
      → n ∣ ul ⊢ N ok
      → m ∣ false ⊢ M ok →  m ≤ 1 → Value M
      → Σ[ k ∈ ℕ ] k ∣ ul ⊢ N [ M ] ok × k ≤ n
  subst-ok N M Nok Mok m≤1 vM
      with sub-ok N {σ = subst-zero M} Nok (SubstZeroOK M Mok m≤1 vM)
  ... | ⟨ k , ⟨ NMok , lt ⟩ ⟩ = ⟨ k , ⟨ NMok , lt ⟩ ⟩
  
  invert-plug : ∀{Γ A B} (M : Γ ⊢ A) (F : Frame A B) {n : ℕ}
           → n ∣ false ⊢ plug M F ok
           → Σ[ m ∈ ℕ ] m ∣ false ⊢ M ok
  invert-plug M (F-·₁ x) (appOK {n = n} MFok MFok₁) = ⟨ n , MFok ⟩
  invert-plug M (F-·₂ M₁) (appOK {m = m} MFok MFok₁) = ⟨ m , MFok₁ ⟩
  invert-plug M (F-if x x₁) (ifOK {n = n} MFok MFok₁ MFok₂) =
     ⟨ n , MFok ⟩
  invert-plug M (F-×₁ x) (consOK {m = m} MFok MFok₁) = ⟨ m , MFok₁ ⟩
  invert-plug M (F-×₂ x) (consOK {n = n} MFok MFok₁) = ⟨ n , MFok ⟩
  invert-plug M F-fst (fstOK {n = n} MFok) = ⟨ n , MFok ⟩
  invert-plug M F-snd (sndOK {n = n} MFok) = ⟨ n , MFok ⟩
  invert-plug M F-inl (inlOK {n = n} MFok) = ⟨ n , MFok ⟩
  invert-plug M F-inr (inrOK {n = n} MFok) = ⟨ n , MFok ⟩
  invert-plug M (F-case x x₁) (caseOK {n = n} MFok y z) =
     ⟨ n , MFok ⟩

  plug-ok : ∀{Γ A B} (M M′ : Γ ⊢ A) (F : Frame A B) {n m : ℕ}
      → m ∣ false ⊢ plug M F ok
      → n ∣ false ⊢ M′ ok
      → 0 ∣ false ⊢ plug M′ F ok
  plug-ok M M′ (F-·₁ x) (appOK y z) Mok = appOK Mok z
  plug-ok M M′ (F-·₂ M₁) (appOK y z) Mok = appOK y Mok
  plug-ok M M′ (F-if x x₁) (ifOK a b c) Mok = ifOK Mok b c
  plug-ok M M′ (F-×₁ x) (consOK a b) Mok = consOK a Mok
  plug-ok M M′ (F-×₂ x) (consOK a b) Mok = consOK Mok b
  plug-ok M M′ F-fst (fstOK a) Mok = fstOK Mok
  plug-ok M M′ F-snd (sndOK a) Mok = sndOK Mok
  plug-ok M M′ F-inl (inlOK a) Mok = inlOK Mok
  plug-ok M M′ F-inr (inrOK a) Mok = inrOK Mok
  plug-ok M M′ (F-case x x₁) (caseOK a b c) Mok = caseOK Mok b c

  plug-ok0 : ∀{Γ A B} (M : Γ ⊢ A) (F : Frame A B) {n : ℕ}{ul}
      → n ∣ ul ⊢ plug M F ok
      → n ≡ 0
  plug-ok0 M (F-·₁ x) (appOK a b) = refl
  plug-ok0 M (F-·₂ M₁) (appOK a b) = refl
  plug-ok0 M (F-if x x₁) (ifOK a b c) = refl
  plug-ok0 M (F-×₁ x) (consOK a b) = refl
  plug-ok0 M (F-×₂ x) (consOK a b) = refl
  plug-ok0 M F-fst (fstOK a) = refl
  plug-ok0 M F-snd (sndOK a) = refl
  plug-ok0 M F-inl (inlOK a) = refl
  plug-ok0 M F-inr (inrOK a) = refl
  plug-ok0 M (F-case x x₁) (caseOK a b c) = refl

  red-any→ok0 : ∀{Γ A}{M M′ : Γ ⊢ A}{n}
          → n ∣ false ⊢ M ok
          → any_ctx / M —→ M′
          → n ≡ 0
  red-any→ok0 Mok (ξ {M = M}{F = F} M—→M′) = plug-ok0 M F Mok 
  red-any→ok0 Mok (ξ-blame{F = F}) = plug-ok0 _ F Mok
  red-any→ok0 (appOK a b) (β x) = refl
  red-any→ok0 (appOK a b) δ = refl
  red-any→ok0 (ifOK a b c) β-if-true = refl
  red-any→ok0 (ifOK a b c) β-if-false = refl
  red-any→ok0 (fstOK a) (β-fst x x₁) = refl
  red-any→ok0 (sndOK a) (β-snd x x₁) = refl
  red-any→ok0 (caseOK a b c) (β-caseL x) = refl
  red-any→ok0 (caseOK a b c) (β-caseR x) = refl
  red-any→ok0 (appOK a b) (fun-cast v x) = refl
  red-any→ok0 (fstOK a) (fst-cast v) = refl
  red-any→ok0 (sndOK a) (snd-cast v) = refl
  red-any→ok0 (caseOK a b c) (case-cast v) = refl

  module PreserveOK
    (preserveApplyCast : ∀{Γ A B}{M : Γ ⊢ A}{c : Cast (A ⇒ B)}{n}{a}
          → n ∣ false ⊢ M ok → (v : Value M)
          → Σ[ m ∈ ℕ ] m ∣ false ⊢ applyCast M v c {a} ok × m ≤ 2 + n)
    where

    preserve-ok : ∀{Γ A}{M M′ : Γ ⊢ A}{ctx : ReductionCtx}{n}
            → n ∣ false ⊢ M ok  →  ctx / M —→ M′
            → Σ[ m ∈ ℕ ] m ∣ false ⊢ M′ ok × m ≤ 2 + n
    preserve-ok {ctx = any_ctx} MFok (ξ {M = M}{M′}{F = F} M—→M′)
        with invert-plug M F MFok
    ... | ⟨ m , Mok ⟩
        with preserve-ok Mok M—→M′
    ... | ⟨ m2 , ⟨ Mpok , m≤n+2 ⟩ ⟩ =      
        ⟨ zero , ⟨ plug-ok M M′ F MFok Mpok , z≤n ⟩ ⟩
    preserve-ok {ctx = any_ctx} Mok ξ-blame = ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩
    preserve-ok {ctx = any_ctx} (appOK {M = M} (lamOK {N = N} Nok) Mok) (β vM) 
       with subst-ok N M Nok Mok (value→ok1 vM Mok) vM
    ... | ⟨ k , ⟨ NMok , k≤ ⟩ ⟩ =
        let n≤2 = OK-ul→2 Nok in
        let m≤1 = value→ok1 vM Mok in
        ⟨ k , ⟨ weaken-OK-ul NMok , ≤-trans k≤ n≤2 ⟩ ⟩
    preserve-ok {ctx = any_ctx} (appOK litOK Mok) δ = ⟨ 0 , ⟨ litOK , z≤n ⟩ ⟩
    preserve-ok {ctx = any_ctx} (ifOK {m = m} litOK Mok Nok) β-if-true =
       ⟨ m , ⟨ weaken-OK-ul Mok , ≤-trans (OK-ul→2 Mok) ≤-refl ⟩ ⟩
    preserve-ok {ctx = any_ctx} (ifOK {k = k} litOK Mok Nok) β-if-false =
       ⟨ k , ⟨ weaken-OK-ul Nok , ≤-trans (OK-ul→2 Nok) ≤-refl ⟩ ⟩
    preserve-ok {ctx = any_ctx} (fstOK (consOK {n = n} Mpok Wok)) (β-fst vMp vW) =
      ⟨ n , ⟨ Mpok , (≤-trans (value→ok1 vMp Mpok) (s≤s z≤n)) ⟩ ⟩
    preserve-ok {ctx = any_ctx} (sndOK (consOK {m = m} Mpok Wok)) (β-snd vM VMp) =
      ⟨ m , ⟨ Wok , (≤-trans (value→ok1 VMp Wok) (s≤s z≤n)) ⟩ ⟩
    preserve-ok {ctx = any_ctx} (caseOK (inlOK a) b c) (β-caseL vV) =
        ⟨ zero , ⟨ appOK (weaken-OK-ul b) a , z≤n ⟩ ⟩
    preserve-ok {ctx = any_ctx} (caseOK (inrOK a) b c) (β-caseR vV) =
        ⟨ zero , ⟨ (appOK (weaken-OK-ul c) a) , z≤n ⟩ ⟩
    preserve-ok {ctx = any_ctx} (appOK (castOK a c) b) (fun-cast v x) =
        let xx = value→ok1 x b in
        ⟨ 1 , ⟨ (castOK (appOK a (castOK b (≤-trans xx (s≤s z≤n)))) z≤n) ,
                (s≤s z≤n) ⟩ ⟩
    preserve-ok {ctx = any_ctx} (fstOK (castOK a b)) (fst-cast v) =
       ⟨ 1 , ⟨ castOK (fstOK a) z≤n , s≤s z≤n ⟩ ⟩
    preserve-ok {ctx = any_ctx} (sndOK (castOK a b)) (snd-cast v) =
       ⟨ 1 , ⟨ castOK (sndOK a) z≤n , s≤s z≤n ⟩ ⟩
    preserve-ok {ctx = any_ctx} (caseOK (castOK {n = n} a b) d e)
        (case-cast {Γ}{A}{B}{A'}{B'}{C}{V}{W₁}{W₂}{c} v {x}) =
       ⟨ zero , ⟨ (caseOK a
               (lamOK (appOK (rename-ok d) (castulOK (varOK{∋x = Z})(s≤s z≤n))))
               (lamOK (appOK (rename-ok e) (castulOK(varOK{∋x = Z})(s≤s z≤n)))))
             , z≤n ⟩ ⟩
    preserve-ok {ctx = non_cast_ctx} (castOK Mok lt) (ξ-cast M—→M′)
        with preserve-ok Mok M—→M′
    ... | ⟨ m , ⟨ Mpok , m≤2 ⟩ ⟩
        with red-any→ok0 Mok M—→M′
    ... | refl =     
          ⟨ suc m , ⟨ castOK Mpok m≤2 , s≤s m≤2 ⟩ ⟩
    preserve-ok {ctx = non_cast_ctx} (castOK blameOK lt) ξ-cast-blame =
       ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩
    preserve-ok {ctx = non_cast_ctx} (castOK Mok lt) (cast v)
        with preserveApplyCast Mok v
    ... | ⟨ m , ⟨ acOK , lt2 ⟩ ⟩ =    
          ⟨ m , ⟨ acOK , ≤-step lt2 ⟩ ⟩
    preserve-ok {ctx = non_cast_ctx} (castOK (castOK {n = n} Mok lt1) lt2)
       compose-casts =
       ⟨ suc n , ⟨ (castOK Mok lt1) , (s≤s (≤-step (≤-step (≤-step ≤-refl)))) ⟩ ⟩

    compress-casts : ∀{A}{M : ∅ ⊢ A}{n}
            → n ∣ false ⊢ M ok
            → Σ[ N ∈ (∅ ⊢ A) ] Σ[ k ∈ ℕ ]
                (non_cast_ctx / M —↠ N)  ×  k ∣ false ⊢ N ok × k ≤ 1
    compress-casts {M = M} {zero} Mok =
       ⟨ M , ⟨ 0 , ⟨ (M ■) , ⟨ Mok , z≤n ⟩ ⟩ ⟩ ⟩
    compress-casts {M = M} {suc zero} Mok =
       ⟨ M , ⟨ 1 , ⟨ (M ■) , ⟨ Mok , s≤s z≤n ⟩ ⟩ ⟩ ⟩
    compress-casts {M = ((N ⟨ c ⟩) ⟨ d ⟩)} {suc (suc zero)} (castOK (castOK Nok x₁) x) = ⟨ N ⟨ compose c d ⟩ , ⟨ 1 , ⟨ non_cast_ctx / (N ⟨ c ⟩) ⟨ d ⟩ —→⟨ compose-casts ⟩ (_ ■) , ⟨ (castOK Nok x₁) , s≤s z≤n ⟩ ⟩ ⟩ ⟩
    compress-casts {M = ((N ⟨ c ⟩) ⟨ d ⟩) ⟨ e ⟩} {suc (suc (suc 0))}
        (castOK (castOK (castOK Nok lt1) lt2) (s≤s (s≤s z≤n))) =
        ⟨ (N ⟨ compose c (compose d e) ⟩) , ⟨ 1 , ⟨ (non_cast_ctx / ((N ⟨ c ⟩) ⟨ d ⟩) ⟨ e ⟩ —→⟨ compose-casts ⟩ (non_cast_ctx / (N ⟨ c ⟩) ⟨ compose d e ⟩ —→⟨ compose-casts ⟩ (_ ■))) , ⟨ (castOK Nok lt1) , (s≤s z≤n) ⟩ ⟩ ⟩ ⟩

  module EfficientCompile
    (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
    where

    open import GTLC
    open import GTLC2CC Cast cast

    compile-efficient : ∀{Γ A} (M : Term) (d : Γ ⊢G M ⦂ A) (ul : Bool)
        → Σ[ k ∈ ℕ ] k ∣ ul ⊢ (compile M d) ok × k ≤ 1
    compile-efficient (` x) (⊢var ∋x) ul = ⟨ 1 , ⟨ varOK , s≤s z≤n ⟩ ⟩
    compile-efficient (ƛ A ˙ N) (⊢lam d) ul
        with compile-efficient N d true
    ... | ⟨ k , ⟨ Nok , lt ⟩ ⟩ =  ⟨ zero , ⟨ lamOK Nok , {!!} ⟩ ⟩
    compile-efficient (L · M at ℓ) (⊢app d₁ d₂ mA A1~B) true
        with compile-efficient L d₁ true
    ... | ⟨ l , ⟨ Lok , lt1 ⟩ ⟩
        with compile-efficient M d₂ true
    ... | ⟨ m , ⟨ Mok , lt2 ⟩ ⟩ =
        ⟨ zero , ⟨ appOK (castulOK Lok lt1) (castulOK Mok lt2) , z≤n ⟩ ⟩
    compile-efficient (L · M at ℓ) (⊢app d₁ d₂ mA A1~B) false
        with compile-efficient L d₁ false
    ... | ⟨ l , ⟨ Lok , lt1 ⟩ ⟩
        with compile-efficient M d₂ false
    ... | ⟨ m , ⟨ Mok , lt2 ⟩ ⟩ =
        ⟨ zero , ⟨ appOK (castOK Lok (≤-trans lt1 (s≤s z≤n)))
                         (castOK Mok (≤-trans lt2 (s≤s z≤n))) , z≤n ⟩ ⟩
    compile-efficient ($ k # p) ⊢lit ul = ⟨ zero , ⟨ litOK , z≤n ⟩ ⟩
    compile-efficient (if L then M else N at ℓ) (⊢if d₁ d₂ d₃ mA aa) true 
        with compile-efficient L d₁ true
    ... | ⟨ l , ⟨ Lok , lt1 ⟩ ⟩
        with compile-efficient M d₂ true
    ... | ⟨ m , ⟨ Mok , lt2 ⟩ ⟩
        with compile-efficient N d₃ true
    ... | ⟨ n , ⟨ Nok , lt3 ⟩ ⟩ =
       ⟨ zero , ⟨ (ifOK (castulOK Lok lt1) (castulOK Mok lt2)(castulOK Nok lt3))
                , z≤n ⟩ ⟩
    compile-efficient (if L then M else N at ℓ) (⊢if d₁ d₂ d₃ mA aa) false
        with compile-efficient L d₁ false
    ... | ⟨ l , ⟨ Lok , lt1 ⟩ ⟩
        with compile-efficient M d₂ true
    ... | ⟨ m , ⟨ Mok , lt2 ⟩ ⟩
        with compile-efficient N d₃ true
    ... | ⟨ n , ⟨ Nok , lt3 ⟩ ⟩ =
       ⟨ zero ,
       ⟨ (ifOK (castOK Lok (≤-step lt1)) (castulOK Mok lt2)(castulOK Nok lt3))
       , z≤n ⟩ ⟩
    compile-efficient (⟦ M , N ⟧) (⊢cons d d₁) ul
        with compile-efficient M d ul
    ... | ⟨ m , ⟨ Mok , lt1 ⟩ ⟩
        with compile-efficient N d₁ ul
    ... | ⟨ n , ⟨ Nok , lt2 ⟩ ⟩ = ⟨ zero , ⟨ (consOK Mok Nok) , z≤n ⟩ ⟩
    compile-efficient (fst M at ℓ) (⊢fst d x) true 
        with compile-efficient M d true
    ... | ⟨ m , ⟨ Mok , lt1 ⟩ ⟩ = ⟨ zero , ⟨ (fstOK(castulOK Mok lt1)) , z≤n ⟩ ⟩
    compile-efficient (fst M at ℓ) (⊢fst d x) false
        with compile-efficient M d false
    ... | ⟨ m , ⟨ Mok , lt1 ⟩ ⟩ =
          ⟨ zero , ⟨ (fstOK(castOK Mok (≤-trans lt1 (s≤s z≤n)))) , z≤n ⟩ ⟩
    compile-efficient (snd M at ℓ) (⊢snd d x) true
        with compile-efficient M d true
    ... | ⟨ m , ⟨ Mok , lt1 ⟩ ⟩ = ⟨ zero , ⟨ (sndOK(castulOK Mok lt1)) , z≤n ⟩ ⟩
    compile-efficient (snd M at ℓ) (⊢snd d x) false
        with compile-efficient M d false
    ... | ⟨ m , ⟨ Mok , lt1 ⟩ ⟩ =
          ⟨ zero , ⟨ (sndOK(castOK Mok (≤-trans lt1 (s≤s z≤n)))) , z≤n ⟩ ⟩
    compile-efficient (inl M other B) (⊢inl d) ul
        with compile-efficient M d ul
    ... | ⟨ m , ⟨ Mok , lt1 ⟩ ⟩ = ⟨ zero , ⟨ (inlOK Mok) , z≤n ⟩ ⟩
    compile-efficient (inr M other A) (⊢inr d) ul
        with compile-efficient M d ul
    ... | ⟨ m , ⟨ Mok , lt1 ⟩ ⟩ = ⟨ zero , ⟨ (inrOK Mok) , z≤n ⟩ ⟩
    compile-efficient (case L of B₁ ⇒ M ∣ C₁ ⇒ N at ℓ) (⊢case d₁ d₂ d₃ abc bc) true
        with compile-efficient L d₁ true
    ... | ⟨ l , ⟨ Lok , lt1 ⟩ ⟩
        with compile-efficient M d₂ true
    ... | ⟨ m , ⟨ Mok , lt2 ⟩ ⟩
        with compile-efficient N d₃ true
    ... | ⟨ n , ⟨ Nok , lt3 ⟩ ⟩ =
          ⟨ zero ,
          ⟨ (caseOK (castulOK Lok lt1) (lamOK (castulOK Mok lt2))
                    (lamOK (castulOK Nok lt3)))
          , z≤n ⟩ ⟩
    compile-efficient (case L of B₁ ⇒ M ∣ C₁ ⇒ N at ℓ) (⊢case d₁ d₂ d₃ abc bc) false
        with compile-efficient L d₁ false
    ... | ⟨ l , ⟨ Lok , lt1 ⟩ ⟩
        with compile-efficient M d₂ true
    ... | ⟨ m , ⟨ Mok , lt2 ⟩ ⟩
        with compile-efficient N d₃ true
    ... | ⟨ n , ⟨ Nok , lt3 ⟩ ⟩ =
          ⟨ zero ,
          ⟨ (caseOK (castOK Lok (≤-trans lt1 (s≤s z≤n)))
                    (lamOK (castulOK Mok lt2)) 
                    (lamOK (castulOK Nok lt3)))
          , z≤n ⟩ ⟩

{-
  simple-size : ∀{Γ A} (M : Γ ⊢ A) → MaybeCast M → SimpleValue M
            → size M ≤ 8 * ideal-size M
            
  value-size : ∀{Γ A} (M : Γ ⊢ A) → MaybeCast M → Value M
            → size M ≤ 1 + 8 * ideal-size M
  maybecast-size : ∀{Γ A} (M : Γ ⊢ A) → MaybeCast M
            → size M ≤ 2 + 8 * ideal-size M

  simple-size (ƛ N) (notCast (nclam mcN)) V-ƛ =
      let IH = maybecast-size N mcN in
      begin
        1 + size N
        ≤⟨ s≤s IH ⟩
        3 + (8 * ideal-size N)
        ≤⟨ +-mono-≤ X ≤-refl ⟩
        8 + (8 * ideal-size N)
        ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
        8 * (1 + ideal-size N)
      ∎
      where
      X : 3 ≤ 8
      X = s≤s (s≤s (s≤s z≤n))
  simple-size ($_ r {p}) mcM V-const = s≤s z≤n
  simple-size (cons M N) (notCast (nccons mcM mcN)) (V-pair vM vN) =
      let IH1 = maybecast-size M mcM in
      let IH2 = maybecast-size N mcN in
      begin
        1 + (size M + size N)
        ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
        1 + ((2 + 8 * ideal-size M) + (2 + 8 * ideal-size N))
        ≤⟨ ≤-reflexive (solve 2 (λ x y → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y)) := con 5 :+ (con 8 :* x :+ con 8 :* y)) refl (ideal-size M) (ideal-size N)) ⟩
        5 + (8 * ideal-size M + 8 * ideal-size N)
        ≤⟨ +-monoʳ-≤ 5 ((≤-reflexive ((sym (*-distribˡ-+ 8 (ideal-size M) (ideal-size N) ))))) ⟩
        5 + 8 * (ideal-size M + ideal-size N)
        ≤⟨ +-mono-≤ X ≤-refl ⟩
        8 + 8 * (ideal-size M + ideal-size N)
        ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
        8 * (1 + (ideal-size M + ideal-size N))
      ∎
    where
    X : 5 ≤ 8
    X = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
    open +-*-Solver
  simple-size (inl M) (notCast (ncinl mcM)) (V-inl vM) =
    let IH = value-size M mcM vM in
    begin
      1 + (size M)
      ≤⟨ s≤s IH ⟩
      2 + 8 * ideal-size M
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + (8 * ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * (1 + ideal-size M)
    ∎
    where
    X : 2 ≤ 8
    X = s≤s (s≤s z≤n)
  simple-size (inr M) (notCast (ncinr mcM)) (V-inr vM) =
    let IH = value-size M mcM vM in
    begin
      1 + (size M)
      ≤⟨ s≤s IH ⟩
      2 + 8 * ideal-size M
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + (8 * ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * (1 + ideal-size M)
    ∎
    where
    X : 2 ≤ 8
    X = s≤s (s≤s z≤n)
  nocast-size : ∀{Γ A} (M : Γ ⊢ A) → NotCast M → size M ≤ 8 * ideal-size M
  
  value-size M mcM (Value.S-val sM) = ≤-step (simple-size M mcM sM)
  value-size (M ⟨ c ⟩) (isCast ncM) (V-cast sM) =
    let IH = nocast-size M ncM in s≤s IH
  value-size (M ⟨ c ⟩) (castVal mcM vM) (V-cast sM) =
    let IH = simple-size M mcM sM in s≤s IH

  nocast-size (` ∋x) ncvar = s≤s z≤n
  nocast-size (ƛ N) (nclam mcN) =
    let IH = maybecast-size N mcN in
    begin
      suc (size N)
      ≤⟨ s≤s IH ⟩
      3 + 8 * (ideal-size N)
      ≤⟨ +-mono-≤ (s≤s (s≤s (s≤s (z≤n{n = 5})))) ≤-refl ⟩
      8 + 8 * (ideal-size N)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size N)
    ∎
  nocast-size (L · M) (ncapp mcL mcM) =
    let IH1 = maybecast-size L mcL in
    let IH2 = maybecast-size M mcM in
    begin
      1 + (size L + size M)
      ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
      1 + ((2 + 8 * ideal-size L) + (2 + 8 * ideal-size M))
      ≤⟨ ≤-reflexive (solve 2 (λ x y → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y))
                         := con 5 :+ ((con 8 :* x) :+ (con 8 :* y))) refl (ideal-size L) (ideal-size M)) ⟩
      5 + ((8 * ideal-size L) + (8 * ideal-size M))
      ≤⟨ +-mono-≤ (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n {n = 3})))))) ≤-refl ⟩
      8 + ((8 * ideal-size L) + (8 * ideal-size M))
      ≤⟨ +-monoʳ-≤ 8 (≤-reflexive ((sym (*-distribˡ-+ 8 (ideal-size L) (ideal-size M) )))) ⟩
      8 + 8 * (ideal-size L + ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size L + ideal-size M)
    ∎
    where open +-*-Solver
  nocast-size ($_ r {p}) nclit = s≤s z≤n
  nocast-size (if L M N) (ncif mcL mcM mcN) =
    let IH1 = maybecast-size L mcL in
    let IH2 = maybecast-size M mcM in
    let IH3 = maybecast-size N mcN in
    begin
      1 + (size L + size M + size N)
      ≤⟨ s≤s (+-mono-≤ (+-mono-≤ IH1 IH2) IH3) ⟩
      1 + ((2 + 8 * ideal-size L) + (2 + 8 * ideal-size M) + (2 + 8 * ideal-size N))
      ≤⟨ ≤-reflexive (solve 3 (λ x y z → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y) :+ (con 2 :+ con 8 :* z)) := con 7 :+ con 8 :* (x :+ y :+ z)) refl (ideal-size L) (ideal-size M) (ideal-size N)) ⟩
      7 + 8 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + 8 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size L + ideal-size M + ideal-size N)
    ∎
    where
    X : 7 ≤ 8
    X = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
    open +-*-Solver
  nocast-size (cons M N) (nccons mcM mcN) =
    let IH1 = maybecast-size M mcM in
    let IH2 = maybecast-size N mcN in
    begin
     1 + (size M + size N)
     ≤⟨ s≤s (+-mono-≤ IH1 IH2) ⟩
     1 + ((2 + 8 * ideal-size M) + (2 + 8 * ideal-size N))
     ≤⟨ ≤-reflexive (solve 2 (λ x y → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y)) := con 5 :+ ((con 8 :* x) :+ (con 8 :* y))) refl (ideal-size M) (ideal-size N)) ⟩
     5 + ((8 * ideal-size M) + (8 * ideal-size N))
     ≤⟨ +-mono-≤ X ≤-refl ⟩
     8 + (8 * ideal-size M + 8 * ideal-size N)
     ≤⟨ +-monoʳ-≤ 8 ((≤-reflexive ((sym (*-distribˡ-+ 8 (ideal-size M) (ideal-size N) ))))) ⟩
     8 + 8 * (ideal-size M + ideal-size N)
     ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
     8 * suc (ideal-size M + ideal-size N)
    ∎
    where
    X : 5 ≤ 8
    X = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
    open +-*-Solver
  nocast-size (fst M) (ncfst mcM) =
    let IH = maybecast-size M mcM in
    begin
     1 + size M
     ≤⟨ s≤s IH ⟩
     3 + 8 * (ideal-size M)
     ≤⟨ +-mono-≤ X ≤-refl ⟩
     8 + 8 * (ideal-size M)
     ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
     8 * suc (ideal-size M)
    ∎
    where
    X : 3 ≤ 8
    X = s≤s (s≤s (s≤s z≤n))
  nocast-size (snd M) (ncsnd mcM) =
    let IH = maybecast-size M mcM in
    begin
     1 + size M
     ≤⟨ s≤s IH ⟩
     3 + 8 * (ideal-size M)
     ≤⟨ +-mono-≤ X ≤-refl ⟩
     8 + 8 * (ideal-size M)
     ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
     8 * suc (ideal-size M)
    ∎
    where
    X : 3 ≤ 8
    X = s≤s (s≤s (s≤s z≤n))
  nocast-size (inl M) (ncinl mcM) =
    let IH = maybecast-size M mcM in
    begin
      1 + size M
      ≤⟨ s≤s IH ⟩
      3 + 8 * (ideal-size M)
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + 8 * (ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size M)
    ∎
    where
    X : 3 ≤ 8
    X = s≤s (s≤s (s≤s z≤n))
  nocast-size (inr M) (ncinr mcM) =
    let IH = maybecast-size M mcM in
    begin
      1 + size M
      ≤⟨ s≤s IH ⟩
      3 + 8 * (ideal-size M)
      ≤⟨ +-mono-≤ X ≤-refl ⟩
      8 + 8 * (ideal-size M)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size M)
    ∎
    where
    X : 3 ≤ 8
    X = s≤s (s≤s (s≤s z≤n))
  nocast-size (case L M N) (nccase mcL mcM mcN) =
    let IH1 = maybecast-size L mcL in
    let IH2 = maybecast-size M mcM in
    let IH3 = maybecast-size N mcN in
    begin
      1 + (size L + size M + size N)
      ≤⟨ s≤s (+-mono-≤ (+-mono-≤ IH1 IH2) IH3) ⟩
      1 + ((2 + 8 * ideal-size L) + (2 + 8 * ideal-size M) + (2 + 8 * ideal-size N))
      ≤⟨ ≤-reflexive (solve 3 (λ x y z → con 1 :+ ((con 2 :+ con 8 :* x) :+ (con 2 :+ con 8 :* y) :+ (con 2 :+ con 8 :* z)) := con 7 :+ con 8 :* (x :+ y :+ z)) refl (ideal-size L) (ideal-size M) (ideal-size N)) ⟩
      7 + 8 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ ≤-step ≤-refl ⟩
      8 + 8 * (ideal-size L + ideal-size M + ideal-size N)
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 8 1 _ )) ⟩
      8 * suc (ideal-size L + ideal-size M + ideal-size N)
    ∎
    where open +-*-Solver
  nocast-size (blame ℓ) ncblame = s≤s z≤n
  maybecast-size M (notCast ncM) =
    let IH = nocast-size M ncM in ≤-step (≤-step IH)
  maybecast-size (M ⟨ c ⟩) (isCast ncM) =
    let IH = nocast-size M ncM in s≤s (≤-step IH)
  maybecast-size (M ⟨ c ⟩) (castVal mcM vM) =
    let IH = value-size M mcM vM in s≤s IH

-}
