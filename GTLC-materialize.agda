
module GTLC-materialize where

open import GTLC
open import Types
open import Variables
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)

{-

This version uses the materialize rule.

-}

infix  4  _⊢m_⦂_
data _⊢m_⦂_ : Context → Term → Type → Set where
  ⊢mat : ∀ {Γ M A B }
    → Γ ⊢m M ⦂ A  →  A ⊑ B
      -------------------
    → Γ ⊢m M ⦂ B

  ⊢m` : ∀ {Γ A k x}
    → lookup Γ x ≡ just ⟨ A , k ⟩
      ---------------------------
    → Γ ⊢m ` x ⦂ A

  ⊢mƛ : ∀ {Γ N A B}
    → Γ , A ⊢m N ⦂ B
      -------------------
    → Γ ⊢m ƛ A , N ⦂ A ⇒ B

  ⊢mapp : ∀ {Γ L M A B ℓ}
    → Γ ⊢m L ⦂ A ⇒ B
    → Γ ⊢m M ⦂ A
      -------------
    → Γ ⊢m L · M at ℓ ⦂ B

  ⊢mconst : ∀ {Γ A} {k : rep A} {p : Prim A}
      -----------
    → Γ ⊢m $ k ⦂ A

  ⊢mif : ∀ {Γ L M N A ℓ}
    → Γ ⊢m L ⦂ 𝔹
    → Γ ⊢m M ⦂ A
    → Γ ⊢m N ⦂ A
      -------------------------------------
    → Γ ⊢m if L M N ℓ ⦂ A

  ⊢mcons : ∀ {Γ A B M N}
    → Γ ⊢m M ⦂ A  →  Γ ⊢m N ⦂ B
      -----------------------
    → Γ ⊢m cons M N ⦂ A `× B
    
  ⊢mfst : ∀ {Γ A B M ℓ}
    → Γ ⊢m M ⦂ A `× B
      -----------------------
    → Γ ⊢m fst M ℓ ⦂ A

  ⊢msnd : ∀ {Γ A B M ℓ}
    → Γ ⊢m M ⦂ A `× B
      -----------------------
    → Γ ⊢m snd M ℓ ⦂ B

  ⊢minl : ∀ {Γ A B M}
    → Γ ⊢m M ⦂ A
      -----------------------
    → Γ ⊢m inl B M ⦂ A `⊎ B

  ⊢minr : ∀ {Γ A B M}
    → Γ ⊢m M ⦂ B
      -----------------------
    → Γ ⊢m inr A M ⦂ A `⊎ B

  ⊢mcase : ∀{Γ A B C L M N ℓ}
    → Γ ⊢m L ⦂ A `⊎ B
    → Γ ⊢m M ⦂ A ⇒ C  →  Γ ⊢m N ⦂ B ⇒ C
      -------------------------------
    → Γ ⊢m case L M N ℓ ⦂ C

cons-ub : ∀{A B} → A ~ B → Σ[ C ∈ Type ] A ⊑ C × B ⊑ C
cons-ub {A}{B} c with (A `⊔ B) {c}
... | ⟨ C , ⟨ ⟨ ac , bc ⟩ , rest ⟩ ⟩ = 
  ⟨ C , ⟨ ac , bc ⟩ ⟩

⊑→▹⇒ : ∀{A B₁ B₂} → A ⊑ B₁ ⇒ B₂ → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ]
   (A ▹ A₁ ⇒ A₂) × (A₁ ⊑ B₁) × (A₂ ⊑ B₂)
⊑→▹⇒ unk⊑ = ⟨ ⋆ , ⟨ ⋆ , ⟨ match⇒⋆ , ⟨ unk⊑ , unk⊑ ⟩ ⟩ ⟩ ⟩
⊑→▹⇒ (fun⊑{A = A}{B = B} d₁ d₂) = ⟨ A , ⟨ B , ⟨ match⇒⇒ , ⟨ d₁ , d₂ ⟩ ⟩ ⟩ ⟩

⊑→▹× : ∀{A B₁ B₂} → A ⊑ B₁ `× B₂ → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ]
   (A ▹ A₁ × A₂) × A₁ ⊑ B₁ × A₂ ⊑ B₂
⊑→▹× unk⊑ = ⟨ ⋆ , ⟨ ⋆ , ⟨ match×⋆ , ⟨ unk⊑ , unk⊑ ⟩ ⟩ ⟩ ⟩
⊑→▹× (pair⊑{A = A}{B = B} d₁ d₂) = ⟨ A , ⟨ B , ⟨ match×× , ⟨ d₁ , d₂ ⟩ ⟩ ⟩ ⟩

⊑→▹⊎ : ∀{A B₁ B₂} → A ⊑ B₁ `⊎ B₂ → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ]
   (A ▹ A₁ ⊎ A₂) × A₁ ⊑ B₁ × A₂ ⊑ B₂
⊑→▹⊎ unk⊑ = ⟨ ⋆ , ⟨ ⋆ , ⟨ match⊎⋆ , ⟨ unk⊑ , unk⊑ ⟩ ⟩ ⟩ ⟩
⊑→▹⊎ (sum⊑{A = A}{B = B} d₁ d₂) = ⟨ A , ⟨ B , ⟨ match⊎⊎ , ⟨ d₁ , d₂ ⟩ ⟩ ⟩ ⟩

trad-impl-mat : ∀ {Γ M A} → Γ ⊢ M ⦂ A → Γ ⊢m M ⦂ A
trad-impl-mat (⊢` x₁) = ⊢m` x₁
trad-impl-mat (⊢ƛ d) = ⊢mƛ (trad-impl-mat d)
trad-impl-mat (⊢app{Γ}{L}{M}{A}{A₁}{A₂}{B} d₁ ma d₂ a1~b)
    with (A₁ `⊔ B) {a1~b}
... | ⟨ A₁⊔B , ⟨ ⟨ a1⊑a1b , b⊑a1b ⟩ , lb ⟩ ⟩ =
  let d₁' = ⊢mat (trad-impl-mat d₁) (Trans⊑ (▹⇒⊑ ma) (fun⊑ a1⊑a1b Refl⊑)) in
  let d₂' = ⊢mat (trad-impl-mat d₂) b⊑a1b in
   ⊢mapp d₁' d₂'
trad-impl-mat (⊢const {k = k}{p = p}) = ⊢mconst {k = k} {p = p}
trad-impl-mat (⊢if {A = A}{A' = A'} d d₁ d₂ bb aa)
    with cons-ub bb | (A `⊔ A') {aa}
... | ⟨ C₁ , ⟨ bc1 , boolc1 ⟩ ⟩ | ⟨ C₂ , lub ⟩  with ⊑R𝔹 boolc1
... | c1=𝔹 rewrite c1=𝔹 =
  let d' = ⊢mat (trad-impl-mat d) bc1 in
  let d₁' = ⊢mat (trad-impl-mat d₁) (proj₁ (proj₁ lub)) in
  let d₂' = ⊢mat (trad-impl-mat d₂) (proj₂ (proj₁ lub)) in
  ⊢mif d' d₁' d₂'
trad-impl-mat (⊢cons d d₁) = ⊢mcons (trad-impl-mat d) (trad-impl-mat d₁)
trad-impl-mat (⊢fst d ma) =
  ⊢mfst (⊢mat (trad-impl-mat d) (▹×⊑ ma))
trad-impl-mat (⊢snd d ma) =
  ⊢msnd (⊢mat (trad-impl-mat d) (▹×⊑ ma))
trad-impl-mat (⊢inl d) = ⊢minl (trad-impl-mat d)
trad-impl-mat (⊢inr d) = ⊢minr (trad-impl-mat d)
trad-impl-mat (⊢case{A₁ = A₁}{A₂ = A₂}{B₁ = B₁}{B₂ = B₂}{C₁ = C₁}{C₂ = C₂}
               d ma d₁ mb d₂ mc ab ac bc)
  with (A₁ `⊔ B₁) {ab} | (A₂ `⊔ C₁) {ac} | (B₂ `⊔ C₂) {bc} 
... | ⟨ A₁⊔B₁ , ⟨ ⟨ a1⊑a1b1 , b1⊑a1b1 ⟩ , lub-a1b1 ⟩ ⟩
    | ⟨ A₂⊔C₁ , ⟨ ⟨ a2⊑a2c1 , c1⊑a2c1 ⟩ , lub-a2c1 ⟩ ⟩
    | ⟨ B₂⊔C₂ , ⟨ ⟨ b2⊑b2c2 , c2⊑b2c2 ⟩ , lub-b2c2 ⟩ ⟩ =
  let d' = ⊢mat (trad-impl-mat d) (Trans⊑ (▹⊎⊑ ma) (sum⊑ a1⊑a1b1 a2⊑a2c1)) in
  let d₁' = ⊢mat (trad-impl-mat d₁) (Trans⊑ (▹⇒⊑ mb) (fun⊑ b1⊑a1b1 b2⊑b2c2)) in
  let d₂' = ⊢mat (trad-impl-mat d₂) (Trans⊑ (▹⇒⊑ mc) (fun⊑ c1⊑a2c1 c2⊑b2c2)) in
  ⊢mcase d' d₁' d₂'


mat-impl-trad : ∀ {Γ M A} → Γ ⊢m M ⦂ A → Σ[ A' ∈ Type ] Γ ⊢ M ⦂ A' × A' ⊑ A
mat-impl-trad (⊢mat{A = A}{B = B} d ab)
    with mat-impl-trad d
... | ⟨ A' , ⟨ d' , lt ⟩ ⟩ = 
      ⟨ A' , ⟨ d' , Trans⊑ lt ab ⟩ ⟩
mat-impl-trad (⊢m` {A = A} lk) = ⟨ A , ⟨ (⊢` lk) , Refl⊑ ⟩ ⟩
mat-impl-trad (⊢mƛ {A = A} d)
    with mat-impl-trad d
... | ⟨ B' , ⟨ d' , lt ⟩ ⟩ =
      ⟨ A ⇒ B' , ⟨ ⊢ƛ d' , fun⊑ Refl⊑ lt ⟩ ⟩
mat-impl-trad (⊢mapp{A = A₁}{B = A₂} d₁ d₂)
    with mat-impl-trad d₁ | mat-impl-trad d₂
... | ⟨ A' , ⟨ d₁' , lt1 ⟩ ⟩ | ⟨ B' , ⟨ d₂' , lt2 ⟩ ⟩
    with ⊑→▹⇒ lt1
... | ⟨ A₁' , ⟨ A₂' , ⟨ ma , ⟨ lt3 , lt4 ⟩ ⟩ ⟩ ⟩ =
   ⟨ A₂' , ⟨ (⊢app d₁' ma d₂' (consis lt3 lt2)) , lt4 ⟩ ⟩
mat-impl-trad (⊢mconst{Γ}{A}{k}{p}) =
   ⟨ A , ⟨ ⊢const{Γ}{A}{k}{p} , Refl⊑ ⟩ ⟩
mat-impl-trad (⊢mif{ℓ = ℓ} d d₁ d₂)
    with mat-impl-trad d | mat-impl-trad d₁ | mat-impl-trad d₂
... | ⟨ B' , ⟨ d' , lt1 ⟩ ⟩ | ⟨ C₁ , ⟨ d₁' , lt2 ⟩ ⟩ | ⟨ C₂ , ⟨ d₂' , lt3 ⟩ ⟩
    with ⊢if{ℓ = ℓ} d' d₁' d₂' (⊑𝔹→~𝔹 lt1) (consis lt2 lt3)
... | d-if     
    with (C₁ `⊔ C₂) {consis lt2 lt3} 
... | ⟨ C' , ⟨ ⟨ ub1 , ub2 ⟩ ,  lub ⟩ ⟩ =
      ⟨ C' , ⟨ d-if , lub ⟨ lt2 , lt3 ⟩ ⟩ ⟩
mat-impl-trad (⊢mcons d₁ d₂)
    with mat-impl-trad d₁ | mat-impl-trad d₂
... | ⟨ C₁ , ⟨ d₁' , lt2 ⟩ ⟩ | ⟨ C₂ , ⟨ d₂' , lt3 ⟩ ⟩ =
   ⟨ C₁ `× C₂ , ⟨ ⊢cons d₁' d₂' , pair⊑ lt2 lt3 ⟩ ⟩
mat-impl-trad (⊢mfst d)
    with mat-impl-trad d
... | ⟨ C , ⟨ d' , lt ⟩ ⟩
    with ⊑→▹× lt
... | ⟨ A₁ , ⟨ A₂ , ⟨ ma , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ =
      ⟨ A₁ , ⟨ (⊢fst d' ma) , lt1 ⟩ ⟩
mat-impl-trad (⊢msnd d)
    with mat-impl-trad d
... | ⟨ C , ⟨ d' , lt ⟩ ⟩
    with ⊑→▹× lt
... | ⟨ A₁ , ⟨ A₂ , ⟨ ma , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ =
      ⟨ A₂ , ⟨ (⊢snd d' ma) , lt2 ⟩ ⟩
mat-impl-trad (⊢minl{B = B} d)
    with mat-impl-trad d
... | ⟨ C , ⟨ d' , lt ⟩ ⟩ =
  ⟨ C `⊎ B , ⟨ ⊢inl d' , sum⊑ lt Refl⊑ ⟩ ⟩
mat-impl-trad (⊢minr{A = A} d)
    with mat-impl-trad d
... | ⟨ C , ⟨ d' , lt ⟩ ⟩ =
  ⟨ A `⊎ C , ⟨ ⊢inr d' , sum⊑ Refl⊑ lt ⟩ ⟩
mat-impl-trad (⊢mcase{A = A}{B = B}{C = C} d d₁ d₂)
    with mat-impl-trad d | mat-impl-trad d₁ | mat-impl-trad d₂
... | ⟨ A' , ⟨ a , lt1 ⟩ ⟩ | ⟨ B' , ⟨ b , lt2 ⟩ ⟩ | ⟨ C' , ⟨ c , lt3 ⟩ ⟩
    with ⊑→▹⊎ lt1 | ⊑→▹⇒ lt2 | ⊑→▹⇒ lt3
... | ⟨ A₁ , ⟨ A₂ , ⟨ ma , ⟨ a1 , a2 ⟩ ⟩ ⟩ ⟩
    | ⟨ B₁ , ⟨ B₂ , ⟨ mb , ⟨ b1 , b2 ⟩ ⟩ ⟩ ⟩
    | ⟨ C₁ , ⟨ C₂ , ⟨ mc , ⟨ c1 , c2 ⟩ ⟩ ⟩ ⟩
    with (⊢case a ma b mb c mc (consis a1 b1) (consis a2 c1) (consis b2 c2))
... | d'      
    with (B₂ `⊔ C₂) {consis b2 c2}
... | ⟨ B₂⊔C₂ , ⟨ ub , lub ⟩ ⟩ =
      ⟨ B₂⊔C₂ , ⟨ d' , lub ⟨ b2 , c2 ⟩ ⟩ ⟩
