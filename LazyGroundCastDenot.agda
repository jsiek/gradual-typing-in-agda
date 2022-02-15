module LazyGroundCastDenot where

open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Int using (pos)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import LazyGroundCast
open import Variables
open import PrimitiveTypes using (Base)
open import Types hiding (_⊑_; _⊔_)
open import Val Base rep-base
open import Labels

blame! : Label → Val
blame! ℓ = const {Blame} ℓ

𝒫 : Set → Set₁
𝒫 V = V → Set

_∈_ : ∀{V} → V → 𝒫 V → Set
x ∈ D = D x

_⊆_ : 𝒫 Val → 𝒫 Val → Set
D₁ ⊆ D₂ = ∀ x → x ∈ D₁ → x ∈ D₂

↓ : Val → 𝒫 Val
↓ v w = w ⊑ v

_∷_ : ∀{Γ B} → 𝒫 Val → (∀{A} → Γ ∋ A → 𝒫 Val) → (∀{A} → Γ , B ∋ A → 𝒫 Val)
(D ∷ ρ) Z = D
(D ∷ ρ) (S x) = ρ x

{- Function Application -}

infix 6 _•_
_•_ : 𝒫 Val → 𝒫 Val → 𝒫 Val
(D₁ • D₂) w = Σ[ v ∈ Val ] (v ↦ w) ∈ D₁ × v ∈ D₂

{- Function Abstraction -}

Λ : (𝒫 Val → 𝒫 Val) → 𝒫 Val
Λ f ⊥ = ⊤
Λ f (const k) = Bot
Λ f (v ↦ w) = f (↓ v) w
Λ f (u ⊔ v) = Λ f u × Λ f v

{- Primitives -}

℘ : ∀{A}{P : Prim A} → rep A → Val → Set
℘ {A}{P} k ⊥ = ⊤
℘ {A}{P-Base {B}} k (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = Bot
℘ {A}{P-Fun {B} P} f (const {B′} k′) = Bot
℘ {A}{P} f (v ↦ w)
    with P
... | P-Base {B} = Bot
... | P-Fun {B} P′ = Σ[ k ∈ base-rep B ] (const {B} k ⊑ v × ℘ {P = P′} (f k) w)
℘ {A}{P} k (u ⊔ v) = ℘ {A}{P} k u × ℘ {A}{P} k v

pair : 𝒫 Val → 𝒫 Val → 𝒫 Val
pair D₁ D₂ w = (Σ[ u ∈ Val ] const 0 ↦ u ⊑ w  ×  u ∈ D₁)
                 × (Σ[ v ∈ Val ] const 1 ↦ v ⊑ w  ×  v ∈ D₂)
car : 𝒫 Val → 𝒫 Val
car D u = (const 0 ↦ u) ∈ D

cdr : 𝒫 Val → 𝒫 Val
cdr D u = (const 1 ↦ u) ∈ D

cond : 𝒫 Val → (𝒫 Val → 𝒫 Val) → (𝒫 Val → 𝒫 Val) → 𝒫 Val
cond D₀ F₁ F₂ w = (const true ∈ (car D₀) × w ∈ F₁ (cdr D₀))
   ⊎ (const false ∈ (car D₀) × w ∈ F₂ (cdr D₀))

data IsBlame : Val → Set where
  is-blame : ∀ {ℓ} → IsBlame (blame! ℓ)

blame-dec : (v : Val) → Dec (IsBlame v)
blame-dec ⊥ = no (λ ())
blame-dec (const {Nat} k) = no λ ()
blame-dec (const {Int} k) = no λ ()
blame-dec (const {𝔹} k) = no λ ()
blame-dec (const {Unit} k) = no λ ()
blame-dec (const {Blame} k) = yes is-blame
blame-dec (v ↦ w) = no (λ ())
blame-dec (v ⊔ w) = no λ ()

ℬ⟦_⟧ : Base → 𝒫 Val 
ℬ⟦ ι ⟧ ⊥ = Bot
ℬ⟦ ι ⟧ (const {ι′} k)
    with base-eq? ι ι′
... | no neq = ι′ ≡ Blame
... | yes refl  = ⊤
ℬ⟦ ι ⟧ (v ↦ w) = Bot
ℬ⟦ ι ⟧ (v ⊔ w) = ℬ⟦ ι ⟧ v × ℬ⟦ ι ⟧ w

data 𝐵? : Base → Val → Set where
  ι?-const : ∀{ι k}
    → 𝐵? ι (const {ι} k)
  ι?-⊔ : ∀{ι v w}
    → 𝐵? ι v
    → 𝐵? ι w
    → 𝐵? ι (v ⊔ w)
  ι?-blame : ∀{ι ℓ}
    → 𝐵? ι (blame! ℓ)

𝐵-dec : (ι : Base) → (v : Val) → Dec (𝐵? ι v)
𝐵-dec ι ⊥ = no (λ ())
𝐵-dec ι (const {ι′} k)
    with base-eq? ι ι′
... | yes refl = yes ι?-const
... | no a
    with blame-dec (const {ι′} k)
... | yes is-blame = yes ι?-blame
... | no b = no λ { ι?-const → a refl ; ι?-blame → b is-blame }
𝐵-dec ι (v ↦ w) = no (λ ())
𝐵-dec ι (v ⊔ w)
    with 𝐵-dec ι v | 𝐵-dec ι w
... | yes a | yes b = yes (ι?-⊔ a b)    
... | _ | no b = no λ { (ι?-⊔ x x₁) → b x₁ }
... | no a | _ = no λ { (ι?-⊔ x x₁) → a x }

𝐵! : Base → Label → Val → Val
𝐵! b ℓ ⊥ = blame! ℓ
𝐵! b ℓ (const {b'} k)
    with base-eq? b b'
... | yes eq = const k
... | no neq = blame! ℓ
𝐵! b ℓ (v ↦ w) = blame! ℓ
𝐵! b ℓ (u ⊔ v) = (𝐵! b ℓ u) ⊔ (𝐵! b ℓ v)

𝐵!? : ∀ A ℓ v → 𝐵? A (𝐵! A ℓ v)
𝐵!? A ℓ ⊥ = ι?-blame
𝐵!? A ℓ (const{B} k)
    with base-eq? A B
... | yes refl = ι?-const
... | no a = ι?-blame
𝐵!? A ℓ (v ↦ w) = ι?-blame
𝐵!? A ℓ (v ⊔ w) = ι?-⊔ (𝐵!? A ℓ v) (𝐵!? A ℓ w)

𝒯⟦_⟧ : Type → 𝒫 Val
𝒯⟦ ⋆ ⟧ w = ⊤
𝒯⟦ ` ι ⟧ w = ℬ⟦ ι ⟧ w
𝒯⟦ A ⇒ B ⟧ ⊥ = ⊤
𝒯⟦ A ⇒ B ⟧ (const {ι} k)
   with base-eq? ι Blame
... | yes refl = ⊤
... | no neq = Bot
𝒯⟦ A ⇒ B ⟧ (v ↦ w) = (𝒯⟦ A ⟧ v → 𝒯⟦ B ⟧ w)
𝒯⟦ A ⇒ B ⟧ (v ⊔ w) = 𝒯⟦ A ⇒ B ⟧ v × 𝒯⟦ A ⇒ B ⟧ w
𝒯⟦ A `× B ⟧ w = {!!}
𝒯⟦ A `⊎ B ⟧ w = {!!}

blame∈𝒯 : ∀{A ℓ}
  → blame! ℓ ∈ 𝒯⟦ A ⟧
blame∈𝒯 {⋆} {ℓ} = tt
blame∈𝒯 {` ι} {ℓ}
    with base-eq? ι Blame
... | yes refl = tt
... | no neq = refl
blame∈𝒯 {A ⇒ B} {ℓ} = tt
blame∈𝒯 {A `× B} {ℓ} = {!!}
blame∈𝒯 {A `⊎ B} {ℓ} = {!!}

{-
data 𝑇? : Type → Val → Set where
  𝑇?-blame : ∀{A ℓ} → 𝑇? A (blame! ℓ)
  ⋆? : ∀{v} → 𝑇? ⋆ v
  ι? : ∀{ι v} → 𝐵? ι v → 𝑇? (` ι) v
  ⇒?-⊥ : ∀{A B} → 𝑇? (A ⇒ B) ⊥
  ⇒?-↦ : ∀{A B v w}
       → (𝑇? A v → 𝑇? B w)
       → 𝑇? (A ⇒ B) (v ↦ w)
  𝑇?-⊔ : ∀{A v w}
       → 𝑇? A v
       → 𝑇? A w
       → 𝑇? A (v ⊔ w)
       
¬𝐵?→¬𝑇? : ∀{ι}{v} → ¬ 𝐵? ι v → ¬ 𝑇? (` ι) v
¬𝐵?→¬𝑇? {ι} {⊥} nb (ι? x) = nb x
¬𝐵?→¬𝑇? {ι} {const k} nb 𝑇?-blame = nb ι?-blame
¬𝐵?→¬𝑇? {ι} {const k} nb (ι? x) = nb x
¬𝐵?→¬𝑇? {ι} {v ↦ w} nb (ι? ())
¬𝐵?→¬𝑇? {ι} {v ⊔ w} nb (ι? x) = nb x
¬𝐵?→¬𝑇? {ι} {v ⊔ w} nb (𝑇?-⊔ t t₁) =
    ¬𝐵?→¬𝑇? (λ z → ¬𝐵?→¬𝑇? (λ z₁ → nb (ι?-⊔ z z₁)) t₁) t

𝑇-dec : (A : Type) → (v : Val) → Dec (𝑇? A v)
𝑇-dec ⋆ v = yes ⋆?
𝑇-dec (` ι) v
    with 𝐵-dec ι v
... | yes a = yes (ι? a)
... | no a = no (¬𝐵?→¬𝑇? a)
𝑇-dec (A ⇒ B) ⊥ = yes ⇒?-⊥
𝑇-dec (A ⇒ B) (const k)
   with blame-dec (const k)
... | yes is-blame = yes 𝑇?-blame
... | no a = no λ { 𝑇?-blame → a is-blame }
𝑇-dec (A ⇒ B) (v ↦ w)
    with 𝑇-dec A v | 𝑇-dec B w
... | yes a | yes b = yes (⇒?-↦ {!!})
... | no a | _ = {!!}
... | _ | no b = {!!}
𝑇-dec (A ⇒ B) (v ⊔ w)
    with 𝑇-dec (A ⇒ B) v | 𝑇-dec (A ⇒ B) w
... | yes a | yes b = yes (𝑇?-⊔ a b)
... | _ | no b = no λ { (𝑇?-⊔ x x₁) → b x₁ }
... | no a | _ = no λ { (𝑇?-⊔ x x₁) → a x }
𝑇-dec (A `× B) ⊥ = no (λ ())
𝑇-dec (A `× B) (const k)
    with blame-dec (const k)
... | yes is-blame = yes 𝑇?-blame
... | no a = no λ { 𝑇?-blame → a is-blame }
𝑇-dec (A `× B) (v ↦ w) = no (λ ())
𝑇-dec (A `× B) (v ⊔ w)
    with 𝑇-dec (A `× B) v | 𝑇-dec (A `× B) w
... | yes a | yes b = yes (𝑇?-⊔ a b)
... | _ | no b = no λ { (𝑇?-⊔ x x₁) → b x₁ }
... | no a | _ = no λ { (𝑇?-⊔ x x₁) → a x }
𝑇-dec (A `⊎ B) ⊥ = no λ ()
𝑇-dec (A `⊎ B) (const k)
    with blame-dec (const k)
... | yes is-blame = yes 𝑇?-blame
... | no a = no λ { 𝑇?-blame → a is-blame }
𝑇-dec (A `⊎ B) (v ↦ w) = no λ ()
𝑇-dec (A `⊎ B) (v ⊔ w)
    with 𝑇-dec (A `⊎ B) v | 𝑇-dec (A `⊎ B) w
... | yes a | yes b = yes (𝑇?-⊔ a b)
... | _ | no b = no λ { (𝑇?-⊔ x x₁) → b x₁ }
... | no a | _ = no λ { (𝑇?-⊔ x x₁) → a x }

𝑇! : Type → Label → Val → Val
𝑇! ⋆ ℓ v = v
𝑇! (` ι) ℓ v = 𝐵! ι ℓ v
𝑇! (A ⇒ B) ℓ ⊥ = ⊥
𝑇! (A ⇒ B) ℓ (const k) = blame! ℓ
𝑇! (A ⇒ B) ℓ (v ↦ w)
    with 𝑇-dec A v
... | yes Av = v ↦ 𝑇! B ℓ w
... | no a = ⊥
𝑇! (A ⇒ B) ℓ (v ⊔ w) = 𝑇! (A ⇒ B) ℓ v ⊔ 𝑇! (A ⇒ B) ℓ w
𝑇! (A `× B) ℓ v = blame! ℓ
𝑇! (A `⊎ B) ℓ v = blame! ℓ

𝑇!? : ∀{A ℓ v} → 𝑇? A (𝑇! A ℓ v)
𝑇!? {⋆} {ℓ} {v} = ⋆?
𝑇!? {` ι} {ℓ} {v} = ι? (𝐵!? ι ℓ v)
𝑇!? {A ⇒ B} {ℓ} {⊥} = ⇒?-⊥
𝑇!? {A ⇒ B} {ℓ} {const k} = 𝑇?-blame
𝑇!? {A ⇒ B} {ℓ} {v ↦ w}
    with 𝑇-dec A v 
... | no a = ⇒?-⊥
... | yes a = {!!}
𝑇!? {A ⇒ B} {ℓ} {v ⊔ w} = 𝑇?-⊔ (𝑇!?{A ⇒ B}{ℓ}{v}) (𝑇!?{A ⇒ B}{ℓ}{w})
𝑇!? {A `× B} {ℓ} {v} = 𝑇?-blame
𝑇!? {A `⊎ B} {ℓ} {v} = 𝑇?-blame
-}

{-
  Val consistency for ⊎ should prevent mixtures of true and false.
-}

coerce : ∀ {A B : Type} → (c : A ~ B) → Label → 𝒫 Val → 𝒫 Val
coerce {.⋆} {⋆} unk~L ℓ D = D
coerce {.⋆} {` ι} unk~L ℓ D = {!!}
coerce {.⋆} {B ⇒ B'} unk~L ℓ D = {!!}
coerce {.⋆} {B `× B'} unk~L ℓ D = {!!}
coerce {.⋆} {B `⊎ B'} unk~L ℓ D = {!!}
coerce {⋆} {.⋆} unk~R ℓ D = D
coerce {` ι} {.⋆} unk~R ℓ D = {!!}
coerce {A ⇒ A'} {.⋆} unk~R ℓ D = {!!}
coerce {A `× A'} {.⋆} unk~R ℓ D = {!!}
coerce {A `⊎ A'} {.⋆} unk~R ℓ D = {!!}
coerce {` ι} {` ι} base~ ℓ D = D
coerce {.(_ ⇒ _)} {.(_ ⇒ _)} (fun~ c d) ℓ D =
    Λ λ X → coerce d ℓ (D • (coerce c ℓ X))
coerce {.(_ `× _)} {.(_ `× _)} (pair~ c d) ℓ D = {!!}
coerce {.(_ `⊎ _)} {.(_ `⊎ _)} (sum~ c d) ℓ D = {!!}



{-

   -}

Env : Context → Set₁
Env Γ = ∀{A} → Γ ∋ A → 𝒫 Val

⟦_⟧ : ∀{Γ A} → Γ ⊢ A → (Env Γ) → 𝒫 Val
⟦ ` x ⟧ ρ = ρ x
⟦ ƛ M ⟧ ρ = Λ λ D → ⟦ M ⟧ (D ∷ ρ)
⟦ L · M ⟧ ρ = ⟦ L ⟧ ρ  •  ⟦ M ⟧ ρ
⟦ $_ {Γ}{A} k {p} ⟧ ρ = ℘ {A}{p} k
⟦ if L M N ⟧ ρ w = (const true ∈ ⟦ L ⟧ ρ  ×  w ∈ ⟦ M ⟧ ρ)
                 ⊎ (const false ∈ ⟦ L ⟧ ρ  ×  w ∈ ⟦ N ⟧ ρ)
⟦ cons M N ⟧ ρ = pair (⟦ M ⟧ ρ) (⟦ N ⟧ ρ)
⟦ fst M ⟧ ρ = car (⟦ M ⟧ ρ)
⟦ snd M ⟧ ρ = cdr (⟦ M ⟧ ρ)
⟦ inl M ⟧ ρ = pair (℘ {P = P-Base} true) (⟦ M ⟧ ρ)
⟦ inr M ⟧ ρ = pair (℘ {P = P-Base} false) (⟦ M ⟧ ρ)
⟦ case L M N ⟧ ρ = cond (⟦ L ⟧ ρ) (λ D → ⟦ M ⟧ (D ∷ ρ)) λ D → ⟦ N ⟧ (D ∷ ρ)
⟦ M ⟨ cast A B ℓ c ⟩ ⟧ ρ = coerce {A}{B} c ℓ (⟦ M ⟧ ρ) 
⟦ M ⟪ inert {A} g c ⟫ ⟧ ρ = coerce {A}{⋆} unk~R (pos 0) (⟦ M ⟧ ρ)
⟦ blame ℓ ⟧ ρ w = w ≡ blame! ℓ

base-non-empty : ∀{ι : Base}{k : rep-base ι}
  → const k ∈ ℘ {` ι}{P-Base} k
base-non-empty {ι}{k}
    with base-eq? ι ι 
... | yes refl = refl
... | no neq = neq refl

rep-base-inhabit : ∀{ι : Base} → rep-base ι
rep-base-inhabit {Nat} = zero
rep-base-inhabit {Int} = pos zero
rep-base-inhabit {𝔹} = false
rep-base-inhabit {Unit} = tt
rep-base-inhabit {Blame} = pos zero

prim-non-empty : ∀{A}{P : Prim A}{k : rep A}
  → Σ[ v ∈ Val ] v ∈ ℘ {A}{P} k
prim-non-empty {` ι} {P-Base} {k} = ⟨ (const k) , base-non-empty ⟩
prim-non-empty {` ι ⇒ B} {P-Fun P} {f} =
  let IH = prim-non-empty {B} {P} {{!!}} in
  {!!}

values-non-empty : ∀{Γ A} (V : Γ ⊢ A) (v : Value V) (ρ : Env Γ)
  → Σ[ v ∈ Val ] v ∈ ⟦ V ⟧ ρ
values-non-empty {Γ} {.(_ ⇒ _)} (ƛ M) V-ƛ ρ = ⟨ ⊥ , tt ⟩
values-non-empty {Γ} {A} .($ _) (V-const{k = k}) ρ = ⟨ {!!} , {!!} ⟩
values-non-empty {Γ} {.(_ `× _)} .(cons _ _) (V-pair v v₁) ρ = {!!}
values-non-empty {Γ} {.(_ `⊎ _)} .(inl _) (V-inl v) ρ = {!!}
values-non-empty {Γ} {.(_ `⊎ _)} .(inr _) (V-inr v) ρ = {!!}
values-non-empty {Γ} {A} .(_ ⟪ i ⟫) (V-wrap v i) ρ = {!!}

_⊧_ : (Γ : Context) → Env Γ → Set
Γ ⊧ ρ = (∀ {A} (x : Γ ∋ A) → ρ x ⊆ 𝒯⟦ A ⟧)

down-pres : ∀ v A → v ∈ 𝒯⟦ A ⟧ → ↓ v ⊆ 𝒯⟦ A ⟧
down-pres v A v∈A = {!!}

ext-pres : ∀{Γ A}{ρ : Env Γ}{D}
  → Γ ⊧ ρ → D ⊆ 𝒯⟦ A ⟧
  → (Γ , A) ⊧ (D ∷ ρ)
ext-pres Γρ DA = {!!}

•-sound : ∀{A B}{D E : 𝒫 Val}
  → D ⊆ 𝒯⟦ A ⇒ B ⟧
  → E ⊆ 𝒯⟦ A ⟧
  → (D • E) ⊆ 𝒯⟦ B ⟧
•-sound D⊆A⇒B E⊆A w ⟨ v , ⟨ vw∈D , v∈E ⟩ ⟩ =
  let vw∈A⇒B = D⊆A⇒B (v ↦ w) vw∈D in
  let v∈A = E⊆A v v∈E in
  vw∈A⇒B v∈A

prim-sound : ∀ {A}{P : Prim A}{k : rep A}
  → ℘ {A}{P} k ⊆ 𝒯⟦ A ⟧
prim-sound = {!!}

coerce-sound : ∀{A B ℓ}{D} (c : A ~ B)
  → D ⊆ 𝒯⟦ A ⟧
  → coerce c ℓ D ⊆ 𝒯⟦ B ⟧
coerce-sound c D⊆A = {!!}

sem-sound : ∀{Γ A}{ρ : Env Γ} (M : Γ ⊢ A)
  → Γ ⊧ ρ
  → ⟦ M ⟧ ρ ⊆ 𝒯⟦ A ⟧
sem-sound (` x) Γ⊧ρ = Γ⊧ρ x
sem-sound (ƛ M) Γ⊧ρ ⊥ vw∈Λ = tt
sem-sound {Γ}{A ⇒ B}{ρ} (ƛ M) Γ⊧ρ (v ↦ w) vw∈Λ v∈A =
   let w∈M : w ∈ ⟦ M ⟧ (↓ v ∷ ρ)
       w∈M = vw∈Λ in
   let IH : ⟦ M ⟧ (↓ v ∷ ρ) ⊆ 𝒯⟦ B ⟧
       IH = sem-sound {Γ , A}{B}{↓ v ∷ ρ} M (ext-pres Γ⊧ρ (down-pres v A v∈A)) in
   IH w w∈M
sem-sound {A = A ⇒ B} (ƛ M) Γ⊧ρ (u ⊔ v) ⟨ u∈Λ , v∈Λ ⟩ =
  let IH1 : u ∈ 𝒯⟦ A ⇒ B ⟧
      IH1 = sem-sound (ƛ M) Γ⊧ρ u u∈Λ in
  let IH2 : v ∈ 𝒯⟦ A ⇒ B ⟧
      IH2 = sem-sound (ƛ M) Γ⊧ρ v v∈Λ in
  ⟨ IH1 , IH2 ⟩
sem-sound {Γ}{ρ = ρ} (_·_ {A = A}{B} L M) Γ⊧ρ =
  let IH1 : ⟦ L ⟧ ρ ⊆ 𝒯⟦ A ⇒ B ⟧
      IH1 = sem-sound L Γ⊧ρ in
  let IH2 : ⟦ M ⟧ ρ ⊆ 𝒯⟦ A ⟧
      IH2 = sem-sound M Γ⊧ρ in
  •-sound IH1 IH2
sem-sound ($ k) Γ⊧ρ = prim-sound
sem-sound (if L M N) Γ⊧ρ = {!!}
sem-sound (cons M N) Γ⊧ρ = {!!}
sem-sound (fst M) Γ⊧ρ = {!!}
sem-sound (snd M) Γ⊧ρ = {!!}
sem-sound (inl M) Γ⊧ρ = {!!}
sem-sound (inr M) Γ⊧ρ = {!!}
sem-sound (case L M N) Γ⊧ρ = {!!}
sem-sound {ρ = ρ}(M ⟨ cast A B ℓ c ⟩) Γ⊧ρ =
  let IH  : ⟦ M ⟧ ρ ⊆ 𝒯⟦ A ⟧
      IH = sem-sound M Γ⊧ρ in
  coerce-sound c IH
sem-sound {ρ = ρ} (M ⟪ inert {A} g c ⟫) Γ⊧ρ =
  let IH  : ⟦ M ⟧ ρ ⊆ 𝒯⟦ A ⟧
      IH = sem-sound M Γ⊧ρ in
  coerce-sound {A = A}{ℓ = pos 0} unk~R IH
sem-sound {A = A} (blame ℓ) Γ⊧ρ v refl = blame∈𝒯 {A}{ℓ}


abstract
  infix 2 _≅_
  _≅_ : 𝒫 Val → 𝒫 Val → Set
  D₁ ≅ D₂ = D₁ ⊆ D₂ × D₂ ⊆ D₁

  ≅-refl : ∀ {D} → D ≅ D
  ≅-refl {D} = ⟨ (λ x x₁ → x₁) , (λ x x₁ → x₁) ⟩

  ≅-sym : ∀ {D E} → D ≅ E → E ≅ D
  ≅-sym ⟨ fst₁ , snd₁ ⟩ = ⟨ snd₁ , fst₁ ⟩

  ≅-trans : ∀ {D E F : 𝒫 Val} → D ≅ E → E ≅ F → D ≅ F
  ≅-trans ⟨ de , ed ⟩ ⟨ ef , fe ⟩ =
      ⟨ (λ x z → ef x (de x z)) , (λ x z → ed x (fe x z)) ⟩

infix  3 _■
_■ : ∀ (D : 𝒫 Val) → D ≅ D
(D ■) =  ≅-refl{D}

infixr 2 _≅⟨_⟩_
_≅⟨_⟩_ : ∀ {E F : 𝒫 Val} (D : 𝒫 Val) → D ≅ E → E ≅ F → D ≅ F
D ≅⟨ D≅E ⟩ E≅F = ≅-trans D≅E E≅F

coerce-atomic-id : ∀{A ℓ} (D : 𝒫 Val) → (A~A : A ~ A) → (a : Atomic A)
  → coerce {A}{A} A~A ℓ D ≅ D
coerce-atomic-id D unk~L A-Unk = ≅-refl {D}
coerce-atomic-id D unk~R A-Unk = ≅-refl {D}
coerce-atomic-id D base~ A-Base = ≅-refl {D}

shift⟦⟧ : ∀{Γ A B} (V : Γ ⊢ A) (D : 𝒫 Val) (ρ : ∀{A} → Γ ∋ A → 𝒫 Val)
  → ⟦ rename (S_{B = B}) V ⟧ (D ∷ ρ) ≅ ⟦ V ⟧ ρ
shift⟦⟧ V D ρ = {!!}

Λ-cong : ∀{F G}
  → (∀{X} → F X ≅ G X)
  → Λ F ≅ Λ G
Λ-cong eq = {!!}

•-cong : ∀{D₁ D₂ E₁ E₂}
  → D₁ ≅ E₁
  → D₂ ≅ E₂
  → D₁ • D₂ ≅ E₁ • E₂
•-cong de1 de2 = {!!}

coerce-cong : ∀{D E ℓ A B} (c : A ~ B)
  → D ≅ E
  → coerce c ℓ D ≅ coerce c ℓ E
coerce-cong de = {!!}

coerce-retract : ∀{G B ℓ ℓ'}{D : 𝒫 Val}{g : Ground G}
  → (c : G ~ ⋆) → (d : ⋆ ~ B) → (e : G ~ B)
  → coerce d ℓ (coerce c ℓ' D) ≅ coerce e ℓ D
coerce-retract {G}{B}{ℓ}{ℓ'}{D}{g} c d e = {!!}

coerce-blame : ∀{G B H ℓ ℓ'}{D : 𝒫 Val}{g : Ground G}{h : Ground H}
  → D ⊆ 𝒯⟦ G ⟧
  → (c : G ~ ⋆) → (d : ⋆ ~ B) → (bh : B ~ H) → (G ≢ H)
  → coerce d ℓ (coerce c ℓ' D) ≅ (λ w → w ≡ blame! ℓ)
coerce-blame {G}{B}{ℓ}{ℓ'}{D}{g} D⊆G c d bh neq = {!!}

⟦⟧-cast : ∀{Γ A B} (V : Γ ⊢ A) (c : Cast (A ⇒ B)) (a : Active c)
   {v : Value V}{ρ : ∀{A} → Γ ∋ A → 𝒫 Val}
  → Γ ⊧ ρ
  → ⟦ V ⟨ c ⟩ ⟧ ρ ≅ ⟦ applyCast V v c {a} ⟧ ρ
⟦⟧-cast V (cast A .A ℓ A~B) (activeId {a = a} .(cast A A ℓ _)) {v}{ρ} Γ⊧ρ =
    coerce-atomic-id (⟦ V ⟧ ρ) A~B a 
⟦⟧-cast V (cast A .⋆ ℓ A~B) (activeInj .(cast A ⋆ ℓ _) ng nd) {v}{ρ} Γ⊧ρ = {!!}
⟦⟧-cast (V ⟪ inert {G} g c ⟫) (cast .⋆ B ℓ ⋆~B) (activeProj _ nd)
        {V-wrap v _} {ρ} Γ⊧ρ
    with ground B {nd}
... | ⟨ H , ⟨ h , B~H ⟩ ⟩
    with gnd-eq? G H {g}{h}
... | yes refl = coerce-retract {g = g} unk~R ⋆~B (Sym~ B~H)
... | no neq = {!!} {- coerce-blame{g = g}{h = h} (sem-sound V Γ⊧ρ) unk~R ⋆~B B~H neq  -}
⟦⟧-cast V (cast (A ⇒ B) (A' ⇒ B') ℓ (fun~ c d)) (activeFun .(cast (A ⇒ B) (A' ⇒ B') ℓ (fun~ c d))) {v}{ρ} Γ⊧ρ =
    Λ-cong G 
    where
    G : ∀ {X : 𝒫 Val} →
         coerce d ℓ (⟦ V ⟧ ρ • coerce c ℓ X)
       ≅ coerce d ℓ (⟦ rename S_ V ⟧ (X ∷ ρ) • coerce c ℓ X)
    G {X} =
            coerce d ℓ (⟦ V ⟧ ρ • coerce c ℓ X)
          ≅⟨ coerce-cong d (•-cong (≅-sym (shift⟦⟧{B = A'} V X ρ)) ≅-refl) ⟩
            coerce d ℓ (⟦ rename S_ V ⟧ (X ∷ ρ) • coerce c ℓ X)
          ■
⟦⟧-cast V (cast .(_ `× _) .(_ `× _) ℓ A~B) (activePair .(cast (_ `× _) (_ `× _) ℓ _)) Γ⊧ρ = {!!}
⟦⟧-cast V (cast .(_ `⊎ _) .(_ `⊎ _) ℓ A~B) (activeSum .(cast (_ `⊎ _) (_ `⊎ _) ℓ _)) Γ⊧ρ = {!!}
⟦⟧-cast V (cast A B ℓ A~B) (activeErr .(cast A B ℓ _) nsc) Γ⊧ρ = {!!}

⟦⟧—→ : ∀{Γ A}{M N : Γ ⊢ A}{ρ : ∀{A} → Γ ∋ A → 𝒫 Val}
  → M —→ N → Γ ⊧ ρ → ⟦ M ⟧ ρ ≅ ⟦ N ⟧ ρ
⟦⟧—→ {M} {N} (ξ red) Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} ξ-blame Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} (β x) Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} δ Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} β-if-true Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} β-if-false Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} (β-fst x x₁) Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} (β-snd x x₁) Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} (β-caseL x) Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} (β-caseR x) Γ⊧ρ = {!!}
⟦⟧—→ {M} {N} (cast{V = V}{c} v {a}) Γ⊧ρ = ⟦⟧-cast V c a Γ⊧ρ
⟦⟧—→ {M} {N} (wrap v) Γ⊧ρ = {!!}
