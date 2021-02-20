open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import Types
open import Variables
open import Labels
open import GTLC
open import GTLCPrecision
open import PreCastStructure

module CompilePresPrec
  (pcsp : PreCastStructWithPrecision)
  where

open PreCastStructWithPrecision pcsp
open import ParamCastCalculus Cast Inert
open import ParamCCPrecision pcsp

module CompilePresPrecProof
  (cast : (A : Type) → (B : Type) → Label → {c : A ~ B } → Cast (A ⇒ B))
  where


  open import GTLC2CC Cast Inert cast

  {-
    Compilation from GTLC to CC preserves precision.
      - We assume Γ ⊢ e ↝ f ⦂ A and Γ′ ⊢ e′ ↝ f′ ⦂ A′ .
  -}
  compile-pres-prec : ∀ {Γ Γ′ A A′} {e : Γ ⊢G A} {e′ : Γ′ ⊢G A′}
    → Γ ⊑* Γ′
    → Γ , Γ′ ⊢ e ⊑ᴳ e′
      -------------------------------
    → (A ⊑ A′) × (Γ , Γ′ ⊢ compile {Γ} {A} e ⊑ᶜ compile {Γ′} {A′} e′)
  compile-pres-prec lpc (⊑ᴳ-prim {A = A}) = ⟨ Refl⊑ , ⊑ᶜ-prim ⟩
  compile-pres-prec lpc (⊑ᴳ-var {x = x} {x′} eq) = ⟨ ⊑*→⊑ x x′ lpc eq , ⊑ᶜ-var eq ⟩
  compile-pres-prec lpc (⊑ᴳ-ƛ lpA lpe) =
    let ⟨ lpB , lpeN ⟩ = compile-pres-prec (⊑*-, lpA lpc) lpe in
      ⟨ (fun⊑ lpA lpB) , ⊑ᶜ-ƛ lpA lpeN ⟩
  compile-pres-prec lpc (⊑ᴳ-· lpeL lpeM {m = m} {m′ = m′}) =
    let ⟨ lpA , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
    let ⟨ lpB , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
    let ⟨ lpA₁ , lpA₂ ⟩ = ▹⇒-pres-prec m m′ lpA in
      ⟨ lpA₂ , ⊑ᶜ-· (⊑ᶜ-cast lpA (fun⊑ lpA₁ lpA₂) lpeL′) (⊑ᶜ-cast lpB lpA₁ lpeM′) ⟩
  compile-pres-prec lpc (⊑ᴳ-if lpeL lpeM lpeN {aa = aa} {aa′}) =
    let ⟨ lpB , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
    let ⟨ lpA₁ , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
    let ⟨ lpA₂ , lpeN′ ⟩ = compile-pres-prec lpc lpeN in
    let lp⨆aa = ⨆-pres-prec aa aa′ lpA₁ lpA₂ in
      ⟨ lp⨆aa , ⊑ᶜ-if (⊑ᶜ-cast lpB base⊑ lpeL′) (⊑ᶜ-cast lpA₁ lp⨆aa lpeM′) (⊑ᶜ-cast lpA₂ lp⨆aa lpeN′) ⟩
  compile-pres-prec lpc (⊑ᴳ-cons lpeM lpeN) =
    let ⟨ lpA , lpeM′ ⟩ = compile-pres-prec lpc lpeM in
    let ⟨ lpB , lpeN′ ⟩ = compile-pres-prec lpc lpeN in
      ⟨ pair⊑ lpA lpB , ⊑ᶜ-cons lpeM′ lpeN′ ⟩
  compile-pres-prec lpc (⊑ᴳ-fst lpe {m} {m′}) =
    let ⟨ lp , lpe′ ⟩ = compile-pres-prec lpc lpe in
    let ⟨ lp₁ , lp₂ ⟩ = ▹×-pres-prec m m′ lp in
      ⟨ lp₁ , ⊑ᶜ-fst (⊑ᶜ-cast lp (pair⊑ lp₁ lp₂) lpe′) ⟩
  compile-pres-prec lpc (⊑ᴳ-snd lpe {m} {m′}) =
    let ⟨ lp , lpe′ ⟩ = compile-pres-prec lpc lpe in
    let ⟨ lp₁ , lp₂ ⟩ = ▹×-pres-prec m m′ lp in
      ⟨ lp₂ , ⊑ᶜ-snd (⊑ᶜ-cast lp (pair⊑ lp₁ lp₂) lpe′) ⟩
  compile-pres-prec lpc (⊑ᴳ-inl lpB lpe) =
    let ⟨ lpA , lpe′ ⟩ = compile-pres-prec lpc lpe in
      ⟨ sum⊑ lpA lpB , ⊑ᶜ-inl lpB lpe′ ⟩
  compile-pres-prec lpc (⊑ᴳ-inr lpA lpe) =
    let ⟨ lpB , lpe′ ⟩ = compile-pres-prec lpc lpe in
      ⟨ sum⊑ lpA lpB , ⊑ᶜ-inr lpA lpe′ ⟩
  compile-pres-prec lpc (⊑ᴳ-case lpeL lp1 lp2 lpeM lpeN {ma} {ma′} {bc = bc} {bc′}) =
    let ⟨ lpA , lpeL′ ⟩ = compile-pres-prec lpc lpeL in
    let ⟨ lpB , lpeM′ ⟩ = compile-pres-prec (⊑*-, lp1 lpc) lpeM in
    let ⟨ lpC , lpeN′ ⟩ = compile-pres-prec (⊑*-, lp2 lpc) lpeN in
    let ⟨ lpA₁ , lpA₂ ⟩ = ▹⊎-pres-prec ma ma′ lpA in
    let lp⨆bc = ⨆-pres-prec bc bc′ lpB lpC in
      ⟨ lp⨆bc , ⊑ᶜ-case (⊑ᶜ-cast (sum⊑ lpA₁ lpA₂) (sum⊑ lp1 lp2) (⊑ᶜ-cast lpA (sum⊑ lpA₁ lpA₂) lpeL′))
                        lp1 lp2
                        (⊑ᶜ-cast lpB lp⨆bc lpeM′)
                        (⊑ᶜ-cast lpC lp⨆bc lpeN′) ⟩
