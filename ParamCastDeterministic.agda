open import Labels
open import Types
open import PreCastStructure using ()
open import CastStructure

open import Data.Nat using ()
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Variables
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)

module ParamCastDeterministic (cs : CastStruct) where
  open CastStruct cs
  open import ParamCastCalculus Cast Inert
  open import ParamCastAux precast
  open import ParamCastReduction cs 

  value? : ∀{Γ : Context}{A : Type} → (M : Γ ⊢ A) → Dec (Value M)
  value? (` x) = no (λ ())
  value? (ƛ M) = yes V-ƛ
  value? (M · M₁) = no (λ ())
  value? ($ x) = yes V-const
  value? (if M M₁ M₂) = no (λ ())
  value? (cons M₁ M₂)
      with value? M₁ | value? M₂
  ... | yes m1v | yes m2v = yes (V-pair m1v m2v)
  ... | yes m1v | no m2v = no λ {(V-pair a b) → m2v b }
  ... | no m1nv | _ = no λ { (V-pair a b) → m1nv a }
  value? (fst M) = no (λ ())
  value? (snd M) = no (λ ())
  value? (inl M)
      with value? M
  ... | yes mv = yes (V-inl mv)
  ... | no mv = no λ { (V-inl a) → mv a }
  value? (inr M)
      with value? M
  ... | yes mv = yes (V-inr mv)
  ... | no mv = no λ { (V-inr a) → mv a }
  value? (case M M₁ M₂) = no (λ ())
  value? (M ⟨ x ⟩) = no (λ ())
  value? (M ⟪ x ⟫)
      with value? M
  ... | yes mv = yes (V-wrap mv x)
  ... | no mv = no λ { (V-wrap a b) → mv a }
  value? (blame x) = no (λ ())

  blame? : ∀{Γ : Context}{A : Type} → (M : Γ ⊢ A)
      → Dec (Σ[ ℓ ∈ Label ] M ≡ blame ℓ)
  blame? (` x) = no λ { ⟨ ℓ , ()⟩ }
  blame? (ƛ M) = no λ { ⟨ ℓ , ()⟩ }
  blame? (M · M₁) = no λ { ⟨ ℓ , ()⟩ }
  blame? ($ x) = no λ { ⟨ ℓ , ()⟩ }
  blame? (if M M₁ M₂) = no λ { ⟨ ℓ , ()⟩ }
  blame? (cons M M₁) = no λ { ⟨ ℓ , ()⟩ }
  blame? (fst M) = no λ { ⟨ ℓ , ()⟩ }
  blame? (snd M) = no λ { ⟨ ℓ , ()⟩ }
  blame? (inl M) = no λ { ⟨ ℓ , ()⟩ }
  blame? (inr M) = no λ { ⟨ ℓ , ()⟩ }
  blame? (case M M₁ M₂) = no λ { ⟨ ℓ , ()⟩ }
  blame? (M ⟨ x ⟩) = no λ { ⟨ ℓ , ()⟩ }
  blame? (M ⟪ x ⟫) = no λ { ⟨ ℓ , ()⟩ }
  blame? (blame ℓ) = yes (⟨ ℓ , refl ⟩)

  plug-not-value : ∀{Γ}{A B : Type}{M : Γ ⊢ A}{F : Frame A B} → ¬ Value M → ¬ Value (plug M F)
  plug-not-value {F = F-×₁ M v} nvm (V-pair vp vp₁) = nvm vp₁
  plug-not-value {F = F-×₂ x} nvm (V-pair vp vp₁) = nvm vp
  plug-not-value {F = F-inl} nvm (V-inl a) = nvm a
  plug-not-value {F = F-inr} nvm (V-inr a) = nvm a
  plug-not-value {F = F-wrap i} nvm (V-wrap a b) = nvm a

  plug-not-var : ∀ {Γ A B} {M : Γ ⊢ A} {F : Frame {Γ} A B} {x}
    → plug M F ≢ ` x
  plug-not-var {F = F-·₁ x} ()
  plug-not-var {F = F-·₂ M} ()
  plug-not-var {F = F-if x x₁} ()
  plug-not-var {F = F-×₁ M v} ()
  plug-not-var {F = F-×₂ x} ()
  plug-not-var {F = F-fst} ()
  plug-not-var {F = F-snd} ()
  plug-not-var {F = F-inl} ()
  plug-not-var {F = F-inr} ()
  plug-not-var {F = F-case x x₁} ()
  plug-not-var {F = F-cast x} ()
  plug-not-var {F = F-wrap i} ()

  canonical-base : ∀{Γ}{ι : Base}{M : Γ ⊢ ` ι} (v : Value M)
      → Σ[ k ∈ rep (` ι)] Σ[ p ∈ Prim (` ι)] M ≡ $_ k {p}
  canonical-base (V-const{k = k}{f = f}) = ⟨ k , ⟨ f , refl ⟩ ⟩
  canonical-base (V-wrap {c = c} vm i) = ⊥-elim (baseNotInert c i)

  canonical-bool : ∀{Γ}{M : Γ ⊢ ` 𝔹} (v : Value M)
      → (M ≡ $_ true {P-Base}) ⊎ (M ≡ $_ false {P-Base})
  canonical-bool (V-const {k = false}{f = P-Base}) = inj₂ refl
  canonical-bool (V-const {k = true}{f = P-Base}) = inj₁ refl
  canonical-bool (V-wrap {c = c} v i) = ⊥-elim (baseNotInert c i)

  canonical-pair : ∀{Γ}{A B}{M : Γ ⊢ A `× B} (v : Value M) →
      (Σ[ M₁ ∈ Γ ⊢ A ] Σ[ M₂ ∈ Γ ⊢ B ] M ≡ cons M₁ M₂ × Value M₁ × Value M₂)
      ⊎
      (Σ[ A' ∈ Type ] Σ[ M₁ ∈ Γ ⊢ A' ] Σ[ c ∈ Cast (A' ⇒ A `× B) ] Σ[ i ∈ Inert c ]
          M ≡ M₁ ⟪ i ⟫ × Value M₁)
  canonical-pair (V-pair {V = V}{W} vm vm₁) =
      inj₁ (⟨ V , (⟨ W , (⟨ refl , (⟨ vm , vm₁ ⟩) ⟩) ⟩) ⟩)
  canonical-pair (V-wrap {A = A'}{V = V}{c = c} vm i) =
      inj₂ (⟨ A' , (⟨ V , (⟨ c , (⟨ i , (⟨ refl , vm ⟩) ⟩) ⟩) ⟩) ⟩)

  canonical-sum : ∀{Γ}{A B}{M : Γ ⊢ A `⊎ B} (v : Value M) →
     (Σ[ M₁ ∈ Γ ⊢ A ] M ≡ inl M₁)
     ⊎ (Σ[ M₁ ∈ Γ ⊢ B ] M ≡ inr M₁)
     ⊎ (Σ[ A' ∈ Type ] Σ[ M₁ ∈ Γ ⊢ A' ] Σ[ c ∈ Cast (A' ⇒ A `⊎ B) ]
        Σ[ i ∈ Inert c ] M ≡ M₁ ⟪ i ⟫ × Value M₁)
  canonical-sum (V-inl {V = V} v) = inj₁ (⟨ V , refl ⟩)
  canonical-sum (V-inr {V = V} v) = inj₂ (inj₁ (⟨ V , refl ⟩))
  canonical-sum (V-wrap {A = A}{V = V}{c} v i) =
      inj₂ (inj₂ (⟨ A , (⟨ V , (⟨ c , (⟨ i , (⟨ refl , v ⟩) ⟩) ⟩) ⟩) ⟩))

  hop : ∀{A} → (M : ∅ ⊢ A) → .(nv : ¬ Value M)  → ∅ ⊢ A
  hop (ƛ M) nv = ⊥-elimi (nv V-ƛ)
  hop (L · M) nv
      with value? L
  ... | yes vl
      with value? M
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbm = L · (hop M nvm)
  hop (L · M) nv | yes vl | yes vm
      with vl
  ... | (V-ƛ {N = N}) = N [ M ]
  ... | (V-wrap {V = V}{c} vv i)
      with Inert-Cross⇒ c i
  ... | (⟨ x , (⟨ A1 , (⟨ A2 , refl ⟩) ⟩) ⟩) =
      (V · (M ⟨ dom c x ⟩)) ⟨ cod c x ⟩
  hop (L · M) nv | yes vl | yes vm | (V-const {k = f}{f = (P-Fun b)})
      with canonical-base vm
  ... | ⟨ k , ⟨ p , refl ⟩ ⟩ = $_ (f k) {b}
  hop (L · M) nv | no nvl
      with blame? L
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbl = (hop L nvl) · M
  hop ($ x) nv = ⊥-elimi (nv V-const)
  hop (if L M N) nv
      with value? L
  ... | no nvl
      with blame? L
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbl = if (hop L nvl) M N
  hop (if L M N) nv | yes vl
      with canonical-bool vl
  ... | inj₁ refl = M
  ... | inj₂ refl = N
  hop (cons M N) nv
      with value? M
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbm = cons (hop M nvm) N
  hop (cons M N) nv | yes vm
      with value? N
  ... | no nvn
      with blame? N
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbn = cons M (hop N nvn)
  hop (cons M N) nv | yes vm | yes vn = ⊥-elimi (nv (V-pair vm vn))
  hop (fst M) nv
      with value? M
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbm = fst (hop M nvm)
  hop (fst M) nv | yes vm
      with canonical-pair vm
  ... | inj₁ (⟨ M₁ , (⟨ M₂ , (⟨ refl , (⟨ vm1 , vm2 ⟩) ⟩) ⟩) ⟩) = M₁
  ... | inj₂ (⟨ A' , (⟨ M₁ , (⟨ c , (⟨ i , (⟨ refl , vm1 ⟩) ⟩) ⟩) ⟩) ⟩)
      with Inert-Cross× c i
  ... | (⟨ x , (⟨ A1 , (⟨ A2 , refl ⟩) ⟩) ⟩) = fst M₁ ⟨ fstC c x ⟩ 
  hop (snd M) nv
      with value? M
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbm = snd (hop M nvm)
  hop (snd M) nv | yes vm
      with canonical-pair vm
  ... | inj₁ (⟨ M₁ , (⟨ M₂ , (⟨ refl , (⟨ vm1 , vm2 ⟩) ⟩) ⟩) ⟩) = M₂
  ... | inj₂ (⟨ A' , (⟨ M₁ , (⟨ c , (⟨ i , (⟨ refl , vm1 ⟩) ⟩) ⟩) ⟩) ⟩)
      with Inert-Cross× c i
  ... | (⟨ x , (⟨ A1 , (⟨ A2 , refl ⟩) ⟩) ⟩) = snd M₁ ⟨ sndC c x ⟩ 
  hop (inl M) nv
      with value? M
  ... | yes vm = ⊥-elimi (nv (V-inl vm))
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbm = inl (hop M nvm)
  hop (inr M) nv 
      with value? M
  ... | yes vm = ⊥-elimi (nv (V-inr vm))
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbm = inr (hop M nvm)
  hop (case L M N) nv
      with value? L
  ... | no nvl
      with blame? L
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbl = case (hop L nvl) M N
  hop (case L M N) nv | yes vl
      with canonical-sum vl
  ... | inj₁ (⟨ V , refl ⟩) = M [ V ]
  ... | inj₂ (inj₁ (⟨ V , refl ⟩)) = N [ V ]
  ... | inj₂ (inj₂ (⟨ A' , (⟨ M₁ , (⟨ c , (⟨ i , (⟨ refl , vm1 ⟩) ⟩) ⟩) ⟩) ⟩))
      with Inert-Cross⊎ c i
  ... | (⟨ x , (⟨ A1 , (⟨ A2 , refl ⟩) ⟩) ⟩) = 
        case M₁ (rename (ext S_) M [ ` Z ⟨ inlC c x ⟩ ])
                (rename (ext S_) N [ ` Z ⟨ inrC c x ⟩ ]) 
  hop (M ⟨ c ⟩) nv
      with value? M
  ... | no nvm 
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbm = (hop M nvm) ⟨ c ⟩
  hop (M ⟨ c ⟩) nv | yes vm
      with ActiveOrInert c
  ... | inj₁ a = applyCast M vm c {a}
  ... | inj₂ i = M ⟪ i ⟫
  hop (M ⟪ i ⟫) nv
      with value? M
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = blame ℓ
  ... | no nbm = (hop M nvm) ⟪ i ⟫
  hop (M ⟪ i ⟫) nv | yes vm = M ⟪ i ⟫
  hop (blame ℓ) nv = blame ℓ

  reduce-not-value : ∀{Γ : Context}{A : Type}{M N : Γ ⊢ A} → M —→ N → ¬ Value M
  reduce-not-value {M = M} M→N 
      with value? M
  ... | yes mv = λ x → V⌿→ mv M→N
  ... | no nmv = nmv

  prim-irrelevant : ∀{A : Type} (p1 : Prim A) (p2 : Prim A) → p1 ≡ p2
  prim-irrelevant {.(` _)} P-Base P-Base = refl
  prim-irrelevant {.(` _ ⇒ _)} (P-Fun p1) (P-Fun p2)
      with prim-irrelevant p1 p2
  ... | refl = refl

  value-irrelevant : ∀{Γ}{A}{V : Γ ⊢ A} (v1 : Value V) (v2  : Value V) → v1 ≡ v2
  value-irrelevant V-ƛ V-ƛ = refl
  value-irrelevant V-const V-const = refl
  value-irrelevant (V-pair v1 v3) (V-pair v2 v4)
      with value-irrelevant v1 v2 | value-irrelevant v3 v4
  ... | refl | refl = refl
  value-irrelevant (V-inl v1) (V-inl v2)
      with value-irrelevant v1 v2
  ... | refl = refl
  value-irrelevant (V-inr v1) (V-inr v2)
      with value-irrelevant v1 v2
  ... | refl = refl
  value-irrelevant (V-wrap v1 i1) (V-wrap v2 i2)
      with value-irrelevant v1 v2
  ... | refl = refl

  reduce→hop : ∀{A} {M N : ∅ ⊢ A}  →  (r : M —→ N)  →  (nv : ¬ Value M)
      → hop M nv ≡ N
  reduce→hop (ξ {M = M₁}{F = F-·₁ M₂} M→N) nv
      with value? M₁
  ... | yes vm1 = ⊥-elim (reduce-not-value M→N vm1)
  ... | no nvm1
      with blame? M₁
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N )
  ... | no nbm1
      with reduce→hop M→N nvm1
  ... | refl = refl
  reduce→hop (ξ {M = M₂}{F = F-·₂ M₁ {vm1}} M→N) nv
      with value? M₁
  ... | no nvm1 = ⊥-elim (nvm1 vm1)
  ... | yes _
      with value? M₂
  ... | yes vm2 = ⊥-elim (reduce-not-value M→N vm2)
  ... | no nvm2
      with blame? M₂
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N )
  ... | no nbm2
      with reduce→hop M→N nvm2
  ... | refl = refl
  reduce→hop (ξ {M = L}{F = F-if M N} L→L') nv
      with value? L
  ... | yes vl = ⊥-elim (reduce-not-value L→L' vl)
  reduce→hop (ξ {M = L}{F = F-if M N} L→L') nv | no nvl
      with blame? L
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ L→L' )
  ... | no nbl
      with reduce→hop L→L' nvl
  ... | refl = refl
  reduce→hop (ξ {M = M₂}{F = F-×₁ M₁ vm1} M→N) nv
      with value? M₁
  ... | no nvm = ⊥-elimi (nvm vm1)
  ... | yes vm
      with value? M₂
  ... | yes vn = ⊥-elim (reduce-not-value M→N vn) 
  ... | no nvn
      with blame? M₂
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N )
  ... | no nbm2
      with reduce→hop M→N nvn
  ... | refl = refl
  reduce→hop (ξ {M = M₁}{F = F-×₂ M₂} M→N) nv
      with value? M₁
  ... | yes vm = ⊥-elim (reduce-not-value M→N vm)
  ... | no nvm
      with blame? M₁
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N)
  ... | no nbm1
      with reduce→hop M→N nvm
  ... | refl = refl
  reduce→hop (ξ {M = M}{F = F-fst} M→N) nv
      with value? M
  ... | yes vm = ⊥-elim (reduce-not-value M→N vm)
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N)
  ... | no nbm
      with reduce→hop M→N nvm
  ... | refl = refl
  reduce→hop (ξ {M = M}{F = F-snd} M→N) nv
      with value? M
  ... | yes vm = ⊥-elim (reduce-not-value M→N vm)
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N)
  ... | no nbm
      with reduce→hop M→N nvm
  ... | refl = refl
  reduce→hop (ξ {M = M}{F = F-inl} M→N) nv
      with value? M
  ... | yes vm = ⊥-elim (reduce-not-value M→N vm)
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N)
  ... | no nbm
      with reduce→hop M→N nvm
  ... | refl = refl
  reduce→hop (ξ {M = M}{F = F-inr} M→N) nv
      with value? M
  ... | yes vm = ⊥-elim (reduce-not-value M→N vm)
  ... | no nvm
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N)
  ... | no nbm
      with reduce→hop M→N nvm
  ... | refl = refl
  reduce→hop (ξ {M = L}{F = F-case M N } L→L') nv
      with value? L
  ... | yes vl = ⊥-elim (reduce-not-value L→L' vl)
  ... | no nvl
      with blame? L
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ L→L' )
  ... | no nbl
      with reduce→hop L→L' nvl
  ... | refl = refl
  reduce→hop (ξ {M = M}{F = F-cast c} M→N) nv
      with value? M
  ... | yes vm = ⊥-elim (reduce-not-value M→N vm)
  ... | no nvm  
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N)
  ... | no nbm
      with reduce→hop M→N nvm
  ... | refl = refl
  reduce→hop (ξ {M = M}{F = F-wrap i} M→N) nv
      with value? M
  ... | yes vm = ⊥-elim (reduce-not-value M→N vm)
  ... | no nvm  
      with blame? M
  ... | yes (⟨ ℓ , refl ⟩) = ⊥-elim (blame⌿→ M→N)
  ... | no nbm
      with reduce→hop M→N nvm
  ... | refl = refl
  reduce→hop (ξ-blame {F = F-·₁ x}) nv = refl
  reduce→hop (ξ-blame {F = F-·₂ M₁ {v}}) nv
      with value? M₁
  ... | no nvm1 = ⊥-elim (nvm1 v)
  ... | yes vm1 = refl
  reduce→hop (ξ-blame {F = F-if x x₁}) nv = refl
  reduce→hop (ξ-blame {F = F-×₁ M₁ vm1}) nv
      with value? M₁
  ... | no nvm1 = ⊥-elimi (nvm1 vm1)
  ... | yes _ = refl
  reduce→hop (ξ-blame {F = F-×₂ x}) nv = refl
  reduce→hop (ξ-blame {F = F-fst}) nv = refl
  reduce→hop (ξ-blame {F = F-snd}) nv = refl
  reduce→hop (ξ-blame {F = F-inl}) nv = refl
  reduce→hop (ξ-blame {F = F-inr}) nv = refl
  reduce→hop (ξ-blame {F = F-case x x₁}) nv = refl
  reduce→hop (ξ-blame {F = F-cast x}) nv = refl
  reduce→hop (ξ-blame {F = F-wrap i}) nv = refl
  reduce→hop (β{W = W} vw) nv
      with value? W
  ... | no nvw = ⊥-elim (nvw vw)
  ... | yes _ = refl
  reduce→hop (δ{f = f}{k}{P-Fun pb}{P-Base {ι}}{b}) nv
      with value? {Γ = ∅} ($_ k {P-Base {ι}})
  ... | no nvk
      with prim-irrelevant b pb
  ... | refl = refl
  reduce→hop (δ{f = f}{k}{P-Fun pb}{P-Base {ι}}{b}) nv | yes vk
      with canonical-base vk
  ... | ⟨ k , ⟨ p , refl ⟩ ⟩
      with prim-irrelevant b pb
  ... | refl = refl
  reduce→hop (β-if-true{f = f}) nv
      with canonical-bool {∅} (V-const{k = true}{f})
  ... | inj₁ refl = refl
  ... | inj₂ ()
  reduce→hop (β-if-false{f = f}) nv
      with canonical-bool {∅} (V-const{k = false}{f})
  ... | inj₁ ()
  ... | inj₂ refl = refl
  reduce→hop (β-fst{V = V}{W} vv vw) nv
      with value? V | value? W
  ... | no nvv | _ = ⊥-elim (nvv vv)
  ... | yes _ | no nvw = ⊥-elim (nvw vw)
  ... | yes _ | yes _ = refl
  reduce→hop (β-snd{V = V}{W} vv vw) nv
      with value? V | value? W
  ... | no nvv | _ = ⊥-elim (nvv vv)
  ... | yes _ | no nvw = ⊥-elim (nvw vw)
  ... | yes _ | yes _ = refl
  reduce→hop (β-caseL{V = V} vv) nv
      with value? V
  ... | no nvv = ⊥-elim (nvv vv)
  ... | yes _ = refl
  reduce→hop (β-caseR{V = V} vv) nv
      with value? V
  ... | no nvv = ⊥-elim (nvv vv)
  ... | yes _ = refl
  reduce→hop (cast{V = V}{c} vv {a}) nv
      with value? V
  ... | no nvv = ⊥-elim (nvv vv)
  ... | yes vv'
      with ActiveOrInert c
  ... | inj₁ a'
      with value-irrelevant vv vv'
  ... | refl
      with ActiveNotRel a a'
  ... | refl = refl
  reduce→hop (cast{V = V}{c} vv {a}) nv | yes _ | inj₂ i =
    ⊥-elim (ActiveNotInert a i)
  reduce→hop (wrap{V = V}{c} vv {i}) nv
      with value? V
  ... | no nvv = ⊥-elim (nvv vv)
  ... | yes vv'
      with ActiveOrInert c
  ... | inj₁ a = ⊥-elim (ActiveNotInert a i)
  ... | inj₂ i'
      with InertNotRel i i'
  ... | refl = refl
  reduce→hop (fun-cast{V = V}{W}{c} vv vw {x}{i}) nv
      with value? (V ⟪ i ⟫)
  ... | no nvv = ⊥-elim (nvv (V-wrap vv i))
  ... | yes vv'
      with value? W
  ... | no nvw = ⊥-elim (nvw vw)
  ... | yes _
      with vv'
  ... | (V-wrap vv'' i')
      with Inert-Cross⇒ c i'
  ... | (⟨ x' , (⟨ A1 , (⟨ A2 , refl ⟩) ⟩) ⟩) =
      refl
  reduce→hop (fst-cast {V = V}{c} vv {x}{i}) nv
      with value? (V ⟪ i ⟫)
  ... | no nvv = ⊥-elim (nvv (V-wrap vv i))
  ... | yes vv'
      with canonical-pair vv'
  ... | inj₁ (⟨ M₁ , (⟨ M₂ , (⟨ () , (⟨ vm1 , vm2 ⟩) ⟩) ⟩) ⟩)
  reduce→hop (fst-cast {V = V}{c} vv {x}{i}) nv | yes vv'
      | inj₂ (⟨ A' , (⟨ M₁ , (⟨ c' , (⟨ i' , (⟨ refl , vm1 ⟩) ⟩) ⟩) ⟩) ⟩)
      with Inert-Cross× c' i'
  ... | (⟨ x' , (⟨ A1 , (⟨ A2 , refl ⟩) ⟩) ⟩) = refl
  reduce→hop (snd-cast {V = V}{c} vv {x}{i}) nv
      with value? (V ⟪ i ⟫)
  ... | no nvv = ⊥-elim (nvv (V-wrap vv i))
  ... | yes vv'
      with canonical-pair vv'
  ... | inj₁ (⟨ M₁ , (⟨ M₂ , (⟨ () , (⟨ vm1 , vm2 ⟩) ⟩) ⟩) ⟩)
  ... | inj₂ (⟨ A' , (⟨ M₁ , (⟨ c' , (⟨ i' , (⟨ refl , vm1 ⟩) ⟩) ⟩) ⟩) ⟩)
      with Inert-Cross× c' i'
  ... | (⟨ x' , (⟨ A1 , (⟨ A2 , refl ⟩) ⟩) ⟩) = refl
  reduce→hop (case-cast {V = V}{M}{N}{c} vv {x}{i}) nv
      with value? (V ⟪ i ⟫)
  ... | no nvv = ⊥-elim (nvv (V-wrap vv i))
  ... | yes vv'
      with canonical-sum vv'
  ... | inj₁ (⟨ V' , () ⟩)
  ... | inj₂ (inj₁ (⟨ V' , () ⟩))
  ... | inj₂ (inj₂ (⟨ A' , (⟨ M₁ , (⟨ c' , (⟨ i' , (⟨ refl , vm1 ⟩) ⟩) ⟩) ⟩) ⟩))
      with Inert-Cross⊎ c' i'
  ... | (⟨ x' , (⟨ A1 , (⟨ A2 , refl ⟩) ⟩) ⟩) = 
        refl

  determinism : ∀{A : Type}{M N N' : ∅ ⊢ A}
              → M —→ N  →  M —→ N'
              → N ≡ N'
  determinism M→N M→N' =
      let h1 = reduce→hop M→N (reduce-not-value M→N) in
      let h2 = reduce→hop M→N' (reduce-not-value M→N') in
      trans (sym h1) h2
