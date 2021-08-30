module GroundCastGG where

  open import Data.Nat
  open import Data.Bool
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
     renaming (_,_ to [_,_])
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)

  open import Types
  open import Variables
  open import Labels
  open import GroundCast

  infix 6 ⟪_⟫⊑⟪_⟫
  data ⟪_⟫⊑⟪_⟫ : ∀ {A A′ B B′} → {c : Cast (A ⇒ B)} → {c′ : Cast (A′ ⇒ B′)}
                               → (i : Inert c) → (i′ : Inert c′) → Set where
    -- Inert injections
    lpii-inj : ∀ {G} {c : Cast (G ⇒ ⋆)} {c′ : Cast (G ⇒ ⋆)}
      → (g : Ground G)
        -----------------------------------------
      → ⟪ I-inj g c ⟫⊑⟪ I-inj g c′ ⟫

    -- Inert cross casts
    lpii-fun : ∀ {A A′ B B′ C C′ D D′} {c : Cast ((A ⇒ B) ⇒ (C ⇒ D))} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
     → A ⇒ B ⊑ A′ ⇒ B′
     → C ⇒ D ⊑ C′ ⇒ D′
       -------------------------------------
     → ⟪ I-fun c ⟫⊑⟪ I-fun c′ ⟫

  infix 6 ⟪_⟫⊑_
  data ⟪_⟫⊑_ : ∀ {A B} → {c : Cast (A ⇒ B)} → Inert c → Type → Set where
    -- Inert injections
    lpit-inj : ∀ {G A′} {c : Cast (G ⇒ ⋆)}
      → (g : Ground G)
      → G ⊑ A′
        -------------------------
      → ⟪ I-inj g c ⟫⊑ A′

    -- Inert cross casts
    lpit-fun : ∀ {A A′ B B′ C D} {c : Cast ((A ⇒ B) ⇒ (C ⇒ D))}
      → A ⇒ B ⊑ A′ ⇒ B′
      → C ⇒ D ⊑ A′ ⇒ B′
        ------------------------------------------
      → ⟪ I-fun c ⟫⊑ A′ ⇒ B′

  infix 6 _⊑⟪_⟫
  data _⊑⟪_⟫ : ∀ {A′ B′} → {c′ : Cast (A′ ⇒ B′)} → Type → Inert c′ → Set where
    -- Inert cross casts
    lpti-fun : ∀ {A A′ B B′ C′ D′} {c′ : Cast ((A′ ⇒ B′) ⇒ (C′ ⇒ D′))}
      → A ⇒ B ⊑ A′ ⇒ B′
      → A ⇒ B ⊑ C′ ⇒ D′
        ---------------------------------------------
      → A ⇒ B ⊑⟪ Inert.I-fun c′ ⟫

  ⊑→lpit : ∀ {A B A′} {c : Cast (A ⇒ B)}
    → (i : Inert c)
    → A ⊑ A′ → B ⊑ A′
      ------------------
    → ⟪ i ⟫⊑ A′
  ⊑→lpit (I-inj g _) lp1 lp2 = lpit-inj g lp1
  ⊑→lpit (I-fun _) (fun⊑ lp1 lp3) (fun⊑ lp2 lp4) = lpit-fun (fun⊑ lp1 lp3) (fun⊑ lp2 lp4)

  lpii→⊑ : ∀ {A A′ B B′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)} {i : Inert c} {i′ : Inert c′}
    → ⟪ i ⟫⊑⟪ i′ ⟫
      --------------------
    → (A ⊑ A′) × (B ⊑ B′)
  lpii→⊑ (lpii-inj g) = [ Refl⊑ , unk⊑ ]
  lpii→⊑ (lpii-fun lp1 lp2) = [ lp1 , lp2 ]

  lpit→⊑ : ∀ {A A′ B} {c : Cast (A ⇒ B)} {i : Inert c}
    → ⟪ i ⟫⊑ A′
      --------------------
    → (A ⊑ A′) × (B ⊑ A′)
  lpit→⊑ (lpit-inj g lp) = [ lp , unk⊑ ]
  lpit→⊑ (lpit-fun lp1 lp2) = [ lp1 , lp2 ]

  lpti→⊑ : ∀ {A A′ B′} {c′ : Cast (A′ ⇒ B′)} {i′ : Inert c′}
    → A ⊑⟪ i′ ⟫
      --------------------
    → (A ⊑ A′) × (A ⊑ B′)
  lpti→⊑ (lpti-fun lp1 lp2) = [ lp1 , lp2 ]

  open import PreCastStructureWithPrecision

  pcsp : PreCastStructWithPrecision
  pcsp = record {
           precast = pcs;
           ⟪_⟫⊑⟪_⟫ = ⟪_⟫⊑⟪_⟫;
           ⟪_⟫⊑_ = ⟪_⟫⊑_;
           _⊑⟪_⟫ = _⊑⟪_⟫;
           ⊑→lpit = ⊑→lpit;
           lpii→⊑ = lpii→⊑;
           lpit→⊑ = lpit→⊑;
           lpti→⊑ = lpti→⊑
         }

  open import CastStructureWithPrecision

  {- A few lemmas to prove `catchup`. -}
  open import ParamCCPrecision pcsp
  open import ParamGradualGuaranteeAux pcsp

  applyCast-catchup : ∀ {Γ Γ′ A A′ B} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ B)}
    → (a : Active c)
    → (vV : Value V) → Value V′
    → A ⊑ A′ → B ⊑ A′
    → Γ , Γ′ ⊢ V ⊑ᶜ V′
      ----------------------------------------------------------
    → ∃[ W ] ((Value W) × (applyCast V vV c {a} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))

  private
    wrapV-⊑-inv : ∀ {Γ Γ′ A A′} {V : Γ ⊢ A} {V′ : Γ′ ⊢ A′} {c : Cast (A ⇒ ⋆)}
      → Value V → Value V′ → (i : Inert c) → A′ ≢ ⋆
      → Γ , Γ′ ⊢ V ⟪ i ⟫ ⊑ᶜ V′
        ------------------------
      → Γ , Γ′ ⊢ V ⊑ᶜ V′
    wrapV-⊑-inv v v' (I-inj g c) nd (⊑ᶜ-wrap (lpii-inj .g) lpVi _) = contradiction refl nd
    wrapV-⊑-inv v v' i nd (⊑ᶜ-wrapl x lpVi) = lpVi

    applyCast-proj-g-catchup : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
      → (nd : B ≢ ⋆) → Ground B   -- B ≢ ⋆ is actually implied since B is ground.
      → (vV : Value V) → Value V′
      → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
        ----------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
    applyCast-proj-g-catchup {c = cast .⋆ B ℓ _} nd g v v′ lp lpV
      with ground? B
    ... | yes b-g
      with canonical⋆ _ v
    ...   | [ G , [ V₁ , [ c₁ , [ i , meq ] ] ] ] rewrite meq
      with gnd-eq? G B {inert-ground c₁ i} {b-g}
    ...     | yes ap-b rewrite ap-b
      with v
    ...       | V-wrap vV₁ .i = [ V₁ , [ vV₁ , [ V₁ ∎ , wrapV-⊑-inv vV₁ v′ i (lp-¬⋆ nd lp) lpV ] ] ]
    applyCast-proj-g-catchup {c = cast .⋆ B ℓ _} nd g v v′ lp lpV | yes b-g | [ G , [ V₁ , [ c₁ , [ I-inj g₁ _ , meq ] ] ] ] | no ap-b
      with lpV
    ...       | ⊑ᶜ-wrapl (lpit-inj _ lp₁) _ = contradiction (lp-consis-ground-eq g₁ g Refl~ lp₁ lp) ap-b
    ...       | ⊑ᶜ-wrap (lpii-inj _) _ _ = contradiction lp (nd⋢⋆ nd)
    applyCast-proj-g-catchup {c = cast .⋆ B ℓ _} nd g v v′ lp lpV | no b-ng = contradiction g b-ng

    applyCast-proj-ng-catchup : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
      → (nd : B ≢ ⋆) → ¬ Ground B
      → (vV : Value V) → Value V′
      → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
        ----------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
    applyCast-proj-ng-catchup {B = ⋆} nd ng v v′ lp lpV = contradiction refl nd
    applyCast-proj-ng-catchup {B = ` B₁} nd ng v v′ lp lpV = contradiction G-Base ng
    applyCast-proj-ng-catchup {B = B₁ ⇒ B₂} {c = cast .⋆ .(B₁ ⇒ B₂) ℓ _} nd ng v v′ lp lpV
      with ground? (B₁ ⇒ B₂)
    ... | yes b-g = contradiction b-g ng
    ... | no b-ng
      with ground (B₁ ⇒ B₂) {nd}
    ...   | [ ⋆ ⇒ ⋆ , [ G-Fun , c~ ] ]
      with applyCast-proj-g-catchup {c = cast ⋆ (⋆ ⇒ ⋆) ℓ unk~L} (ground-nd G-Fun) G-Fun v v′ (⊑-ground-relax G-Fun lp c~ nd) lpV
    ...     | [ W , [ vW , [ rd* , lpW ] ] ] =
      -- The 1st cast ⋆ ⇒ ⋆ → ⋆ is an active projection
      let a = A-proj (cast ⋆ (⋆ ⇒ ⋆) ℓ unk~L) (ground-nd G-Fun)
      -- The 2nd cast ⋆ → ⋆ ⇒ B₁ → B₂ is an inert function cast
          i = I-fun _ in
        [ W ⟪ i ⟫ ,
          [ V-wrap vW i ,
            [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {a} ⟩ rd*)) (_ —→⟨ wrap vW {i} ⟩ _ ∎) ,
              ⊑ᶜ-wrapl (⊑→lpit i (⊑-ground-relax G-Fun lp c~ nd) lp) lpW ] ] ]
    applyCast-proj-ng-catchup {B = B₁ `× B₂} {c = cast .⋆ .(B₁ `× B₂) ℓ _} nd ng v v′ lp lpV
      with ground? (B₁ `× B₂)
    ... | yes b-g = contradiction b-g ng
    ... | no b-ng
      with ground (B₁ `× B₂) {nd}
    ...   | [ ⋆ `× ⋆ , [ G-Pair , c~ ] ]
      with applyCast-proj-g-catchup {c = cast ⋆ (⋆ `× ⋆) ℓ unk~L} (ground-nd G-Pair) G-Pair v v′ (⊑-ground-relax G-Pair lp c~ nd) lpV
    ...     | [ cons W₁ W₂ , [ V-pair w₁ w₂ , [ rd* , lpW ] ] ]
      with lp | v′ | lpW
    ...       | pair⊑ lp₁ lp₂ | V-pair v′₁ v′₂ | ⊑ᶜ-cons lpW₁ lpW₂
      with applyCast-catchup {c = cast ⋆ B₁ ℓ unk~L} (from-dyn-active B₁) w₁ v′₁ unk⊑ lp₁ lpW₁
         | applyCast-catchup {c = cast ⋆ B₂ ℓ unk~L} (from-dyn-active B₂) w₂ v′₂ unk⊑ lp₂ lpW₂
    ...         | [ V₁ , [ v₁ , [ rd*₁ , lpV₁ ] ] ] | [ V₂ , [ v₂ , [ rd*₂ , lpV₂ ] ] ] =
      [ cons V₁ V₂ ,
        [ V-pair v₁ v₂ ,
          {- Here we need to prove V ⟨ ⋆ ⇒ ⋆ × ⋆ ⟩ ⟨ ⋆ × ⋆ ⇒ B₁ × B₂ ⟩ —↠ cons V₁ V₂ -}
          [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {A-proj _ (λ ())} ⟩ rd*))
                     {- cons W₁ W₂ ⟨ ⋆ × ⋆ ⇒ B₁ × B₂ ⟩ —↠ cons V₁ V₂ -}
                     (
                       -- cons W₁ W₂ ⟨ ⋆ × ⋆ ⇒ B₁ × B₂ ⟩
                       _ —→⟨ cast (V-pair w₁ w₂) {A-pair _} ⟩
                       -- -- cons (fst (cons W₁ W₂) ⟨ ⋆ ⇒ B₁ ⟩) (snd (cons W₁ W₂) ⟨ ⋆ ⇒ B₂ ⟩)
                       -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst w₁ w₂)) ⟩
                       -- -- cons (W₁ ⟨ ⋆ ⇒ B₁ ⟩) (snd (cons W₁ W₂) ⟨ ⋆ ⇒ B₂ ⟩)
                       -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd w₁ w₂)) ⟩
                       -- cons (W₁ ⟨ ⋆ ⇒ B₁ ⟩) (W₂ ⟨ ⋆ ⇒ B₂ ⟩)
                       _ —→⟨ ξ {F = F-×₂ _} (cast w₁ {from-dyn-active B₁}) ⟩
                       ↠-trans (plug-cong (F-×₂ _) rd*₁)
                       (_ —→⟨ ξ {F = F-×₁ _ v₁} (cast w₂ {from-dyn-active B₂}) ⟩
                        -- cons V₁ V₂
                        plug-cong (F-×₁ _ v₁) rd*₂)
                     ) ,
            ⊑ᶜ-cons lpV₁ lpV₂ ] ] ]
    applyCast-proj-ng-catchup {B = B₁ `⊎ B₂} {c = cast .⋆ .(B₁ `⊎ B₂) ℓ _} nd ng v v′ lp lpV
      with ground? (B₁ `⊎ B₂)
    ... | yes b-g = contradiction b-g ng
    ... | no b-ng
      with ground (B₁ `⊎ B₂) {nd}
    ...   | [ ⋆ `⊎ ⋆ , [ G-Sum , c~ ] ]
      with applyCast-proj-g-catchup {c = cast ⋆ (⋆ `⊎ ⋆) ℓ unk~L} (ground-nd G-Sum) G-Sum v v′
                                                                  (⊑-ground-relax G-Sum lp c~ nd) lpV
    ...     | [ inl W , [ V-inl w , [ rd* , lpW ] ] ]
      with lp | v′ | lpW
    ...       | sum⊑ lp₁ lp₂ | V-inl v′₁ | ⊑ᶜ-inl unk⊑ lpW₁
      with applyCast-catchup {c = cast ⋆ B₁ ℓ unk~L} (from-dyn-active B₁) w v′₁ unk⊑ lp₁ lpW₁
    ...         | [ V₁ , [ v₁ , [ rd*₁ , lpV₁ ] ] ] =
      [ inl V₁ ,
        [ V-inl v₁ ,
          {- Here we need to prove V ⟨ ⋆ ⇒ ⋆ ⊎ ⋆ ⟩ ⟨ ⋆ ⊎ ⋆ ⇒ B₁ × B₂ ⟩ —↠ inl V₁ -}
          [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {A-proj _ (λ ())} ⟩ rd*))
                     {- inl W ⟨ ⋆ ⊎ ⋆ ⇒ B₁ ⊎ B₂ ⟩ —↠ inl V₁ -}
                     (
                       -- inl W ⟨ ⋆ ⊎ ⋆ ⇒ B₁ ⊎ B₂ ⟩
                       _ —→⟨ cast (V-inl w) {A-sum _} ⟩
                       -- case (inl W) (inl ((` Z) ⟨ cast ⋆ B₁ ℓ c ⟩)) (inr ((` Z) ⟨ cast ⋆ B₂ ℓ d ⟩))
                       -- _ —→⟨ β-caseL w ⟩
                       -- (inl (` Z ⟨ ⋆ ⇒ B₂ ⟩)) [ W ] ≡ inl (W ⟨ ⋆ ⇒ B₂ ⟩)
                       _ —→⟨ ξ (cast w {from-dyn-active B₁} ) ⟩
                       plug-cong F-inl rd*₁
                       -- inl V₁
                     ),
            ⊑ᶜ-inl lp₂ lpV₁ ] ] ]
    applyCast-proj-ng-catchup {B = B₁ `⊎ B₂} {c = cast .⋆ .(B₁ `⊎ B₂) ℓ _} nd ng v v′ lp lpV
                              | no b-ng | [ ⋆ `⊎ ⋆ , [ G-Sum , c~ ] ] | [ inr W , [ V-inr w , [ rd* , lpW ] ] ]
      with lp | v′ | lpW
    ...       | sum⊑ lp₁ lp₂ | V-inr v′₂ | ⊑ᶜ-inr unk⊑ lpW₂
      with applyCast-catchup {c = cast ⋆ B₂ ℓ unk~L} (from-dyn-active B₂) w v′₂ unk⊑ lp₂ lpW₂
    ...         | [ V₂ , [ v₂ , [ rd*₂ , lpV₂ ] ] ] =
      [ inr V₂ ,
        [ V-inr v₂ ,
          {- Here we need to prove V ⟨ ⋆ ⇒ ⋆ ⊎ ⋆ ⟩ ⟨ ⋆ ⊎ ⋆ ⇒ B₁ × B₂ ⟩ —↠ inr V₂ -}
          [ ↠-trans (plug-cong (F-cast _) (_ —→⟨ cast v {A-proj _ (λ ())} ⟩ rd*))
                     {- inr W ⟨ ⋆ ⊎ ⋆ ⇒ B₁ ⊎ B₂ ⟩ —↠ inr V₂ -}
                     (
                       -- inr W ⟨ ⋆ ⊎ ⋆ ⇒ B₁ ⊎ B₂ ⟩
                       _ —→⟨ cast (V-inr w) {A-sum _} ⟩
                       -- case (inr W) (inl ((` Z) ⟨ cast ⋆ B₁ ℓ c ⟩)) (inr ((` Z) ⟨ cast ⋆ B₂ ℓ d ⟩))
                       -- _ —→⟨ β-caseR w ⟩
                       -- (inr (` Z ⟨ ⋆ ⇒ B₂ ⟩)) [ W ] ≡ inr (W ⟨ ⋆ ⇒ B₂ ⟩)
                       _ —→⟨ ξ (cast w {from-dyn-active B₂} ) ⟩
                       plug-cong F-inr rd*₂
                       -- inr V₂
                     ),
            ⊑ᶜ-inr lp₁ lpV₂ ] ] ]

    applyCast-proj-catchup : ∀ {Γ Γ′ A′ B} {V : Γ ⊢ ⋆} {V′ : Γ′ ⊢ A′} {c : Cast (⋆ ⇒ B)}
      → (nd : B ≢ ⋆)
      → (vV : Value V) → Value V′
      → B ⊑ A′ → Γ , Γ′ ⊢ V ⊑ᶜ V′
        ----------------------------------------------------------
      → ∃[ W ] ((Value W) × (applyCast V vV c {A-proj c nd} —↠ W) × (Γ , Γ′ ⊢ W ⊑ᶜ V′))
    applyCast-proj-catchup {B = B} {c = c} nd v v′ lp lpV
      with ground? B
    ... | yes g = applyCast-proj-g-catchup {c = c} nd g v v′ lp lpV
    ... | no ng = applyCast-proj-ng-catchup {c = c} nd ng v v′ lp lpV

    inert-inj-⊑-inert-inj : ∀ {G G′} → {c : Cast (G ⇒ ⋆)} → {c′ : Cast (G′ ⇒ ⋆)}
      → (g : Ground G) → (g′ : Ground G′)
      → G ⊑ G′
        ------------------------------------------
      → ⟪ Inert.I-inj g c ⟫⊑⟪ Inert.I-inj g′ c′ ⟫
    inert-inj-⊑-inert-inj g g′ lp with ground-⊑-eq g g′ lp | g | g′
    ... | refl | G-Base | G-Base = lpii-inj G-Base
    ... | refl | G-Fun  | G-Fun  = lpii-inj G-Fun
    ... | refl | G-Pair | G-Pair = lpii-inj G-Pair
    ... | refl | G-Sum  | G-Sum  = lpii-inj G-Sum

    dyn-value-⊑-wrap : ∀ {A′ B′} {V : ∅ ⊢ ⋆} {V′ : ∅ ⊢ A′} {c′ : Cast (A′ ⇒ B′)}
      → Value V → Value V′
      → (i′ : Inert c′)
      → ∅ , ∅ ⊢ V ⊑ᶜ V′
        -----------------------
      → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
    dyn-value-⊑-wrap v v′ (Inert.I-inj () (cast .⋆ .⋆ _ _)) (⊑ᶜ-wrap (lpii-inj g) lpV _)
    dyn-value-⊑-wrap v v′ (Inert.I-inj g′ (cast A′ .⋆ _ _)) (⊑ᶜ-wrapl (lpit-inj g lp) lpV)
      with ground-⊑-eq g g′ lp
    ... | refl = ⊑ᶜ-wrap (inert-inj-⊑-inert-inj g g′ lp) lpV λ _ → refl
    dyn-value-⊑-wrap v v′ (Inert.I-fun (cast .(_ ⇒ _) .(_ ⇒ _) _ _)) (⊑ᶜ-wrapl (lpit-inj G-Fun (fun⊑ _ _)) lpV) =
      ⊑ᶜ-wrapl (lpit-inj G-Fun (fun⊑ unk⊑ unk⊑)) (⊑ᶜ-wrapr (lpti-fun (fun⊑ unk⊑ unk⊑) (fun⊑ unk⊑ unk⊑)) lpV λ ())

    applyCast-⊑-wrap : ∀ {A A′ B B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
      → (v : Value V) → Value V′
      → (a : Active c) → (i′ : Inert c′)
      → A ⊑ A′ → B ⊑ B′
      → ∅ , ∅ ⊢ V ⊑ᶜ V′
        -----------------------------------------
      → ∅ , ∅ ⊢ applyCast V v c {a} ⊑ᶜ V′ ⟪ i′ ⟫
    -- Id
    applyCast-⊑-wrap v v′ (A-id _) i′ lp1 unk⊑ lpV = dyn-value-⊑-wrap v v′ i′ lpV
    -- Inj
    applyCast-⊑-wrap v v′ (A-inj (cast .⋆ .⋆ _ _) ng nd) (I-inj g′ _) unk⊑ _ lpV = ⊥-elimi (nd refl)
    applyCast-⊑-wrap v v′ (A-inj (cast .(` _) .⋆ _ _) ng nd) (I-inj G-Base _) base⊑ _ lpV = ⊥-elimi (ng G-Base)
    applyCast-⊑-wrap v v′ (A-inj (cast .(_ ⇒ _) .⋆ _ _) ng nd) (I-inj G-Fun _) (fun⊑ unk⊑ unk⊑) _ lpV = ⊥-elimi (ng G-Fun)
    applyCast-⊑-wrap v v′ (A-inj (cast .(_ `× _) .⋆ _ _) ng nd) (I-inj G-Pair _) (pair⊑ unk⊑ unk⊑) _ lpV = ⊥-elimi (ng G-Pair)
    applyCast-⊑-wrap v v′ (A-inj (cast .(_ `⊎ _) .⋆ _ _) ng nd) (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) _ lpV = ⊥-elimi (ng G-Sum)
    applyCast-⊑-wrap v v′ (A-inj (cast .⋆ .⋆ _ _) ng nd) (I-fun _) unk⊑ _ lpV = ⊥-elimi (nd refl)
    applyCast-⊑-wrap v v′ (A-inj (cast .(_ ⇒ _) .⋆ _ _) ng nd) (I-fun _) (fun⊑ lp1 lp2) _ lpV
      with ground _ {nd}
    ... | [ ⋆ ⇒ ⋆ , [ G-Fun , _ ] ] =
      ⊑ᶜ-castl (fun⊑ unk⊑ unk⊑) unk⊑ (⊑ᶜ-wrapr (lpti-fun (fun⊑ unk⊑ unk⊑) (fun⊑ unk⊑ unk⊑))
                                               (⊑ᶜ-castl (fun⊑ lp1 lp2) (fun⊑ unk⊑ unk⊑) lpV) λ ())
    -- Proj
    applyCast-⊑-wrap v v′ (A-proj (cast .⋆ B _ _) nd) (I-inj x _) _ unk⊑ lpV = ⊥-elimi (nd refl)
    applyCast-⊑-wrap v v′ (A-proj (cast .⋆ .⋆ _ _) nd) (I-fun _) _ unk⊑ lpV = ⊥-elimi (nd refl)
    applyCast-⊑-wrap v v′ (A-proj (cast .⋆ (A ⇒ B) _ _) _) (I-fun _) _ (fun⊑ lp1 lp2) lpV
      with ground? (A ⇒ B)
    ... | yes G-Fun
      with canonical⋆ _ v
    ...   | [ G , [ W , [ c₁ , [ i₁ , meq ] ] ] ] rewrite meq
      with gnd-eq? G (A ⇒ B) {inert-ground _ i₁} {G-Fun}
    ...     | yes ap rewrite ap = ⊑ᶜ-wrapr (lpti-fun (fun⊑ unk⊑ unk⊑) (fun⊑ lp1 lp2)) (wrap-⊑-value-inv (λ ()) v v′ lpV) λ ()
    ...     | no  ap with lpV
    ...       | ⊑ᶜ-wrapl (lpit-inj G-Fun (fun⊑ _ _)) lpW = contradiction refl ap
    applyCast-⊑-wrap v v′ (A-proj (cast .⋆ (A ⇒ B) _ _) nd) (I-fun _) _ (fun⊑ lp1 lp2) lpV | no ng
      with ground _ {nd}
    ... | [ ⋆ ⇒ ⋆ , [ G-Fun , _ ] ] =
      ⊑ᶜ-castl (fun⊑ unk⊑ unk⊑) (fun⊑ lp1 lp2) (⊑ᶜ-wrapr (lpti-fun (fun⊑ unk⊑ unk⊑) (fun⊑ unk⊑ unk⊑))
                                                         (⊑ᶜ-castl unk⊑ (fun⊑ unk⊑ unk⊑) lpV) λ ())


  private
    -- We reason about `~-relevant` in a seperate lemma
    applyCast-reduction-pair : ∀ {Γ A B C D} {V : Γ ⊢ A} {W : Γ ⊢ B} {ℓ}
      → (c~ : A `× B ~ C `× D)
      → (v : Value V) → (w : Value W)
      → ∃[ c~1 ] ∃[ c~2 ]
           (applyCast (cons V W) (V-pair v w) (cast (A `× B) (C `× D) ℓ c~) {A-pair _}
              —↠
            cons (V ⟨ cast A C ℓ c~1 ⟩) (W ⟨ cast B D ℓ c~2 ⟩))
    applyCast-reduction-pair c~ v w with ~-relevant c~
    ... | pair~ c~1 c~2 = [ c~1 , [ c~2 , _ ∎ ] ]

    applyCast-reduction-inj : ∀ {Γ A} {V : Γ ⊢ A} {ℓ}
      → (v : Value V)
      → (ng : ¬ Ground A) → (nd : A ≢ ⋆)
      → ∃[ G ] ∃[ c~ ] (applyCast V v (cast A ⋆ ℓ unk~R) {A-inj _ ng nd} —↠ (V ⟨ cast A G ℓ c~ ⟩) ⟨ cast G ⋆ ℓ unk~R ⟩)
    applyCast-reduction-inj {A = A} v ng nd
      with ground A {nd}
    ... | [ G , [ _ , c~ ] ] = [ G , [ c~ , _ ∎ ] ]

    applyCast-reduction-sum-left : ∀ {Γ A B C D} {V : Γ ⊢ A} {ℓ}
      → (c~ : A `⊎ B ~ C `⊎ D)
      → (v : Value V)
      → ∃[ c~1 ]
           (applyCast (inl V) (V-inl v) (cast (A `⊎ B) (C `⊎ D) ℓ c~) {A-sum _}
              —↠
            inl (V ⟨ cast A C ℓ c~1 ⟩))
    applyCast-reduction-sum-left c~ v with ~-relevant c~
    ... | sum~ c~1 c~2 = [ c~1 , _ ∎ ]

    applyCast-reduction-sum-right : ∀ {Γ A B C D} {V : Γ ⊢ B} {ℓ}
      → (c~ : A `⊎ B ~ C `⊎ D)
      → (v : Value V)
      → ∃[ c~2 ]
           (applyCast (inr V) (V-inr v) (cast (A `⊎ B) (C `⊎ D) ℓ c~) {A-sum _}
              —↠
            inr (V ⟨ cast B D ℓ c~2 ⟩))
    applyCast-reduction-sum-right c~ v with ~-relevant c~
    ... | sum~ c~1 c~2 = [ c~2 , _ ∎ ]

  applyCast-catchup (A-id _) vV vV′ lp1 lp2 lpV = [ _ , [ vV , [ _ ∎ , lpV ] ] ]

  applyCast-catchup {A = A} {V = V} {c = cast A ⋆ ℓ _} (A-inj c a-ng a-nd) vV vV′ lp1 lp2 lpV
    with ground A {a-nd}
  ... | [ G , [ g , c~ ] ]
    with g | c~ | lp1
  ...   | G-Base | base~ | _ =
    let i = I-inj g (cast G ⋆ ℓ unk~R) in
      [ V ⟪ i ⟫ , [ V-wrap vV i , [ _ —→⟨ ξ (cast vV {A-id {a = A-Base} _}) ⟩ _ —→⟨ wrap vV {i} ⟩ _ ∎ ,
                                    ⊑ᶜ-wrapl (lpit-inj g lp1) lpV ] ] ]
  ...   | G-Base | unk~L | _ = ⊥-elimi (a-nd refl)
  ...   | G-Fun | unk~L | _ = ⊥-elimi (a-nd refl)
  ...   | G-Fun | fun~ c~₁ c~₂ | fun⊑ lp11 lp12 =
    let i₁ = I-fun (cast A G ℓ (fun~ c~₁ c~₂))
        i₂ = I-inj g (cast G ⋆ ℓ unk~R) in
      [ V ⟪ i₁ ⟫ ⟪ i₂ ⟫ , [ V-wrap (V-wrap vV i₁) i₂ ,
        [ _ —→⟨ ξ (wrap vV {i₁}) ⟩ _ —→⟨ wrap (V-wrap vV i₁) {i₂} ⟩ _ ∎ ,
          ⊑ᶜ-wrapl (lpit-inj g (⊑-ground-relax g lp1 c~ (eq-unk-relevant a-nd)))
                   (⊑ᶜ-wrapl (lpit-fun lp1 ground-fun-⊑) lpV) ] ] ]
  ...   | G-Pair | unk~L | _ = ⊥-elimi (a-nd refl)
  ...   | G-Pair | pair~ c~₁ c~₂ | pair⊑ lp11 lp12
    with vV | vV′ | lpV
  ...     | V-pair {A = A₁} {B₁} {V₁} {V₂} v₁ v₂ | V-pair {V = V₁′} {W = V₂′} v₁′ v₂′ | ⊑ᶜ-cons lpV₁ lpV₂
    {- Need to prove:
      cons V₁ V₂ ⟨ A × B ⇒ ⋆ × ⋆ ⟩ ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩ —↠
      cons (V₁ ⟨ A ⇒ ⋆ ⟩) (V₂ ⟨ B ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
      Note that A ⇒ ⋆ can be either active, such as A-id or A-inj , or inert, such as I-inj , depending on A.
    -}
    with ActiveOrInert (cast A₁ ⋆ ℓ unk~R) | ActiveOrInert (cast B₁ ⋆ ℓ unk~R)
  ...       | inj₁ a₁ | inj₁ a₂ =
      let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ v₁ v₁′ lp11 unk⊑ lpV₁
          [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ v₂ v₂′ lp12 unk⊑ lpV₂ in
        [ cons W₁ W₂ ⟪ I-inj g (cast (⋆ `× ⋆) ⋆ ℓ unk~R) ⟫ ,
          [ V-wrap (V-pair w₁ w₂) _ ,
            [ _ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _})⟩
              ↠-trans (plug-cong (F-cast _) (proj₂ (proj₂ (applyCast-reduction-pair c~ v₁ v₂))))
                       -- cons (V₁ ⟨ A₁ ⇒ ⋆ ⟩) (V₂ ⟨ B₁ ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
                       (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₂ _} (cast v₁ {a₁})) ⟩
                        (↠-trans (plug-cong (F-cast _) (plug-cong (F-×₂ _) rd*₁))
                        (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₁ _ w₁} (cast v₂ {a₂})) ⟩
                        (↠-trans (plug-cong (F-cast _) (plug-cong (F-×₁ _ w₁) rd*₂))
                        (_ —→⟨ wrap (V-pair w₁ w₂) ⟩ _ ∎))))) ,
              ⊑ᶜ-wrapl (lpit-inj _ (pair⊑ unk⊑ unk⊑)) (⊑ᶜ-cons lpW₁ lpW₂) ] ] ]
  ...       | inj₂ i₁ | inj₁ a₂ =
    let [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ v₂ v₂′ lp12 unk⊑ lpV₂ in
      [ cons (V₁ ⟪ i₁ ⟫) W₂ ⟪ I-inj g (cast (⋆ `× ⋆) ⋆ ℓ unk~R) ⟫ ,
        [ V-wrap (V-pair (V-wrap v₁ i₁) w₂) _ ,
          [ _ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _})⟩
              ↠-trans (plug-cong (F-cast _) (proj₂ (proj₂ (applyCast-reduction-pair c~ v₁ v₂))))
                       -- cons (V₁ ⟨ A₁ ⇒ ⋆ ⟩) (V₂ ⟨ B₁ ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
                       (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₂ _} (wrap v₁ {i₁})) ⟩
                        _ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₁ _ (V-wrap v₁ i₁)} (cast v₂ {a₂})) ⟩
                        ↠-trans (plug-cong (F-cast _) (plug-cong (F-×₁ _ (V-wrap v₁ i₁)) rd*₂))
                                 (_ —→⟨ wrap (V-pair (V-wrap v₁ i₁) w₂) ⟩ _ ∎)) ,
            ⊑ᶜ-wrapl (⊑→lpit _ (pair⊑ unk⊑ unk⊑) lp2) (⊑ᶜ-cons (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 unk⊑) lpV₁) lpW₂) ] ] ]
  ...       | inj₁ a₁ | inj₂ i₂ =
    let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ v₁ v₁′ lp11 unk⊑ lpV₁ in
      [ cons W₁ (V₂ ⟪ i₂ ⟫) ⟪ I-inj g (cast (⋆ `× ⋆) ⋆ ℓ unk~R) ⟫ ,
        [ V-wrap (V-pair w₁ (V-wrap v₂ i₂)) _ ,
          [ _ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _})⟩
              ↠-trans (plug-cong (F-cast _) (proj₂ (proj₂ (applyCast-reduction-pair c~ v₁ v₂))))
                       -- cons (V₁ ⟨ A₁ ⇒ ⋆ ⟩) (V₂ ⟨ B₁ ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
                       (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₂ _} (cast v₁ {a₁})) ⟩
                        (↠-trans (plug-cong (F-cast _) (plug-cong (F-×₂ _) rd*₁))
                         (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₁ _ w₁} (wrap v₂ {i₂})) ⟩
                         (_ —→⟨ wrap (V-pair w₁ (V-wrap v₂ i₂)) ⟩ _ ∎)))) ,
            ⊑ᶜ-wrapl (⊑→lpit _ (pair⊑ unk⊑ unk⊑) lp2) (⊑ᶜ-cons lpW₁ (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 unk⊑) lpV₂)) ] ] ]
  ...       | inj₂ i₁ | inj₂ i₂ =
        [ cons (V₁ ⟪ i₁ ⟫) (V₂ ⟪ i₂ ⟫) ⟪ I-inj g (cast (⋆ `× ⋆) ⋆ ℓ unk~R) ⟫ ,
          [ V-wrap (V-pair (V-wrap v₁ _) (V-wrap v₂ _)) _ ,
            [ _ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _})⟩
              ↠-trans (plug-cong (F-cast _) (proj₂ (proj₂ (applyCast-reduction-pair c~ v₁ v₂))))
                       -- cons (V₁ ⟨ A₁ ⇒ ⋆ ⟩) (V₂ ⟨ B₁ ⇒ ⋆ ⟩) ⟨ ⋆ × ⋆ ⇒ ⋆ ⟩
                       (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₂ _} (wrap v₁ {i₁})) ⟩
                        _ —→⟨ ξ {F = F-cast _} (ξ {F = F-×₁ _ (V-wrap v₁ i₁)} (wrap v₂ {i₂})) ⟩
                        _ —→⟨ wrap (V-pair (V-wrap v₁ i₁) (V-wrap v₂ i₂)) ⟩
                        _ ∎) ,
              ⊑ᶜ-wrapl (lpit-inj _ (pair⊑ unk⊑ unk⊑)) (⊑ᶜ-cons (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 unk⊑) lpV₁)
                                                               (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 unk⊑) lpV₂)) ] ] ]

  applyCast-catchup {V = V} {c = cast A ⋆ ℓ _} (A-inj c a-ng a-nd) vV vV′ lp1 lp2 lpV
    | [ G , [ g , c~ ] ] | G-Sum | unk~L | _ =
    ⊥-elimi (a-nd refl)
  applyCast-catchup {V = V} {c = cast (A₁ `⊎ B₁) ⋆ ℓ _} (A-inj c a-ng a-nd) (V-inl {V = W} w) (V-inl {V = W′} w′) lp1 lp2 (⊑ᶜ-inl lpB lpW)
    | [ G , [ g , c~ ] ] | G-Sum | sum~ c~₁ c~₂ | sum⊑ lp11 lp12
    {-       (inl W ⟨ A ⊎ B ⇒ ⋆ ⊎ ⋆ ⟩) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        —↠ (case (inl W) (inl (` Z ⟨ A ⇒ ⋆ ⟩)) (inr (` Z ⟨ B ⇒ ⋆ ⟩))) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        —↠ ((inl (` Z ⟨ A ⇒ ⋆ ⟩)) [ W ]) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        —↠ inl (W ⟨ A ⇒ ⋆ ⟩) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        At this point we need to case on whether A ⇒ ⋆ is active or inert. If active, goes to:
        —↠ inl W₁ ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
        Otherwise if inert, goes to:
        —↠ inl (W ⟨ A ⇒ ⋆ ⟩) ⟨ ⋆ ⊎ ⋆ ⇒ ⋆ ⟩
    -}
    with ActiveOrInert (cast A₁ ⋆ ℓ unk~R)
  ... | inj₁ a₁ =
    let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ w w′ lp11 unk⊑ lpW in
      [ inl W₁ ⟪ I-inj G-Sum (cast (⋆ `⊎ ⋆) ⋆ ℓ unk~R) ⟫ ,
        [ V-wrap (V-inl w₁) (I-inj G-Sum _) ,
          [ _ —→⟨ ξ {F = F-cast _} (cast (V-inl w) {A-sum _}) ⟩
            ↠-trans (plug-cong (F-cast _) (proj₂ (applyCast-reduction-sum-left c~ w)))
                     (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-inl} (cast w {a₁})) ⟩
                      ↠-trans (plug-cong (F-cast _) (plug-cong F-inl rd*₁))
                               (_ —→⟨ wrap (V-inl w₁) {I-inj G-Sum _} ⟩ _ ∎)) ,
            ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) lp2) (⊑ᶜ-inl unk⊑ lpW₁) ] ] ]
  ... | inj₂ i₁ =
    [ inl (W ⟪ i₁ ⟫) ⟪ I-inj G-Sum (cast (⋆ `⊎ ⋆) ⋆ ℓ unk~R) ⟫ ,
      [ V-wrap (V-inl (V-wrap w i₁)) (I-inj G-Sum _) ,
        [ _ —→⟨ ξ {F = F-cast _} (cast (V-inl w) {A-sum _}) ⟩
          ↠-trans (plug-cong (F-cast _) (proj₂ (applyCast-reduction-sum-left c~ w)))
                   (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-inl} (wrap w {i₁})) ⟩
                    _ —→⟨ wrap (V-inl (V-wrap w i₁)) {I-inj G-Sum _} ⟩
                    _ ∎) ,
          ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) unk⊑)
                   (⊑ᶜ-inl unk⊑ (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 unk⊑) lpW)) ] ] ]
  applyCast-catchup {A = A} {V = V} {c = cast (A₁ `⊎ B₁) ⋆ ℓ _} (A-inj c a-ng a-nd) (V-inr {V = W} w) (V-inr {V = W′} w′) lp1 lp2 (⊑ᶜ-inr lpA lpW)
    | [ G , [ g , c~ ] ] | G-Sum | sum~ c~₁ c~₂ | sum⊑ lp11 lp12
    with ActiveOrInert (cast B₁ ⋆ ℓ unk~R)
  ... | inj₁ a₂ =
    let [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ w w′ lp12 unk⊑ lpW in
      [ inr W₂ ⟪ I-inj G-Sum (cast (⋆ `⊎ ⋆) ⋆ ℓ unk~R) ⟫ ,
        [ V-wrap (V-inr w₂) (I-inj G-Sum _) ,
          [ _ —→⟨ ξ {F = F-cast _} (cast (V-inr w) {A-sum _}) ⟩
            ↠-trans (plug-cong (F-cast _) (proj₂ (applyCast-reduction-sum-right c~ w)))
                     (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-inr} (cast w {a₂})) ⟩
                      ↠-trans (plug-cong (F-cast _) (plug-cong F-inr rd*₂))
                               (_ —→⟨ wrap (V-inr w₂) {I-inj G-Sum _} ⟩ _ ∎)) ,
            ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) lp2) (⊑ᶜ-inr unk⊑ lpW₂) ] ] ]
  ... | inj₂ i₂ =
    [ inr (W ⟪ i₂ ⟫) ⟪ I-inj G-Sum (cast (⋆ `⊎ ⋆) ⋆ ℓ unk~R) ⟫ ,
      [ V-wrap (V-inr (V-wrap w i₂)) (I-inj G-Sum _) ,
        [ _ —→⟨ ξ {F = F-cast _} (cast (V-inr w) {A-sum _}) ⟩
          ↠-trans (plug-cong (F-cast _) (proj₂ (applyCast-reduction-sum-right c~ w)))
                   (_ —→⟨ ξ {F = F-cast _} (ξ {F = F-inr} (wrap w {i₂})) ⟩
                    _ —→⟨ wrap (V-inr (V-wrap w i₂)) {I-inj G-Sum _} ⟩
                    _ ∎) ,
          ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) unk⊑)
                   (⊑ᶜ-inr unk⊑ (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 unk⊑) lpW)) ] ] ]


  applyCast-catchup (A-proj c b-nd) vV vV′ lp1 lp2 lpV = applyCast-proj-catchup {c = c} (eq-unk-relevant b-nd) vV vV′ lp2 lpV
  applyCast-catchup {V = cons V W} (A-pair (cast (A `× B) (C `× D) ℓ c~)) (V-pair v w) (V-pair v′ w′) (pair⊑ lp11 lp12) (pair⊑ lp21 lp22) (⊑ᶜ-cons lpV lpW)
    with ~-relevant c~
  ... | pair~ c~1 c~2
    with ActiveOrInert (cast A C ℓ c~1) | ActiveOrInert (cast B D ℓ c~2)
  ...   | inj₁ a₁ | inj₁ a₂ =
    let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ v v′ lp11 lp21 lpV
        [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ w w′ lp12 lp22 lpW in
      [ cons W₁ W₂ ,
        [ V-pair w₁ w₂ ,
          [ -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst v w)) ⟩
            -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd v w)) ⟩
            _ —→⟨ ξ {F = F-×₂ _} (cast v {a₁}) ⟩
            (↠-trans (plug-cong (F-×₂ _) rd*₁)
            (_ —→⟨ ξ {F = F-×₁ _ w₁} (cast w {a₂}) ⟩
            (↠-trans (plug-cong (F-×₁ _ w₁) rd*₂) (_ ∎)))) ,
            ⊑ᶜ-cons lpW₁ lpW₂ ] ] ]
  ...   | inj₁ a₁ | inj₂ i₂ =
    let [ W₁ , [ w₁ , [ rd*₁ , lpW₁ ] ] ] = applyCast-catchup a₁ v v′ lp11 lp21 lpV in
      [ cons W₁ (W ⟪ i₂ ⟫) ,
        [ V-pair w₁ (V-wrap w i₂) ,
          [ -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst v w)) ⟩
            -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd v w)) ⟩
            _ —→⟨ ξ {F = F-×₂ _} (cast v {a₁}) ⟩
            (↠-trans (plug-cong (F-×₂ _) rd*₁)
            (_ —→⟨ ξ {F = F-×₁ _ w₁} (wrap w {i₂}) ⟩
             (_ ∎))) ,
            ⊑ᶜ-cons lpW₁ (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 lp22) lpW) ] ] ]
  ...   | inj₂ i₁ | inj₁ a₂ =
    let [ W₂ , [ w₂ , [ rd*₂ , lpW₂ ] ] ] = applyCast-catchup a₂ w w′ lp12 lp22 lpW in
      [ cons (V ⟪ i₁ ⟫) W₂ ,
        [ V-pair (V-wrap v i₁) w₂ ,
          [ -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst v w)) ⟩
            -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd v w)) ⟩
            _ —→⟨ ξ {F = F-×₂ _} (wrap v {i₁}) ⟩
            _ —→⟨ ξ {F = F-×₁ _ (V-wrap v i₁)} (cast w {a₂}) ⟩
            (plug-cong (F-×₁ _ (V-wrap v i₁)) rd*₂) ,
            ⊑ᶜ-cons (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 lp21) lpV) lpW₂ ] ] ]
  ...   | inj₂ i₁ | inj₂ i₂ =
    [ cons (V ⟪ i₁ ⟫) (W ⟪ i₂ ⟫) ,
      [ V-pair (V-wrap v i₁) (V-wrap w i₂) ,
        [ -- _ —→⟨ ξ {F = F-×₂ _} (ξ {F = F-cast _} (β-fst v w)) ⟩
          -- _ —→⟨ ξ {F = F-×₁ _} (ξ {F = F-cast _} (β-snd v w)) ⟩
          _ —→⟨ ξ {F = F-×₂ _} (wrap v {i₁}) ⟩
          _ —→⟨ ξ {F = F-×₁ _ (V-wrap v i₁)} (wrap w {i₂}) ⟩
          _ ∎ ,
          ⊑ᶜ-cons (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 lp21) lpV) (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 lp22) lpW) ] ] ]
  applyCast-catchup {V = inl V} (A-sum (cast (A `⊎ B) (C `⊎ D) ℓ c~)) (V-inl v) (V-inl v′) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inl lpB lpV)
    with ~-relevant c~
  ... | sum~ c~1 c~2
    with ActiveOrInert (cast A C ℓ c~1)
  ...   | inj₁ a₁ =
    let [ W , [ w , [ rd* , lpW ] ] ] = applyCast-catchup a₁ v v′ lp11 lp21 lpV in
      [ inl W ,
        [ V-inl w ,
          [ -- _ —→⟨ β-caseL v ⟩
            _ —→⟨ ξ {F = F-inl} (cast v {a₁}) ⟩
            plug-cong F-inl rd* ,
            ⊑ᶜ-inl lp22 lpW ] ] ]
  ...   | inj₂ i₁ =
    [ inl (V ⟪ i₁ ⟫) ,
      [ V-inl (V-wrap v i₁) ,
        [ -- _ —→⟨ β-caseL v ⟩
          _ —→⟨ ξ {F = F-inl} (wrap v {i₁}) ⟩
          _ ∎ ,
          ⊑ᶜ-inl lp22 (⊑ᶜ-wrapl (⊑→lpit i₁ lp11 lp21) lpV) ] ] ]
  applyCast-catchup {V = inr V} (A-sum (cast (A `⊎ B) (C `⊎ D) ℓ c~)) (V-inr v) (V-inr v′) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inr lpA lpV)
    with ~-relevant c~
  ... | sum~ c~1 c~2
    with ActiveOrInert (cast B D ℓ c~2)
  ...   | inj₁ a₂ =
    let [ W , [ w , [ rd* , lpW ] ] ] = applyCast-catchup a₂ v v′ lp12 lp22 lpV in
      [ inr W ,
        [ V-inr w ,
          [ -- _ —→⟨ β-caseR v ⟩
            _ —→⟨ ξ {F = F-inr} (cast v {a₂}) ⟩
            plug-cong F-inr rd* ,
            ⊑ᶜ-inr lp21 lpW ] ] ]
  ...   | inj₂ i₂ =
    [ inr (V ⟪ i₂ ⟫) ,
      [ V-inr (V-wrap v i₂) ,
        [ -- _ —→⟨ β-caseR v ⟩
          _ —→⟨ ξ {F = F-inr} (wrap v {i₂}) ⟩
          _ ∎ ,
          ⊑ᶜ-inr lp21 (⊑ᶜ-wrapl (⊑→lpit i₂ lp12 lp22) lpV) ] ] ]


  sim-wrap : ∀ {A A′ B B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → Value V → (v′ : Value V′)
    → (i′ : Inert c′)
    → A ⊑ A′ → B ⊑ B′
    → ∅ , ∅ ⊢ V ⊑ᶜ V′
      -----------------------------------------------------
    → ∃[ N ] ((V ⟨ c ⟩ —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ V′ ⟪ i′ ⟫))
  {- In this case, A is less than a ground type A′, so it can either be ⋆ or ground.
     This is the only case where the cast ⟨ ⋆ ⇒ ⋆ ⟩ is actually active! -}
  sim-wrap v v′ (Inert.I-inj g′ _) unk⊑ unk⊑ lpV =
    [ _ , [ _ —→⟨ cast v {Active.A-id {a = A-Unk} _} ⟩ _ ∎ , dyn-value-⊑-wrap v v′ (Inert.I-inj g′ _) lpV ] ]
  sim-wrap v v′ (Inert.I-inj g′ _) base⊑ unk⊑ lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj g′ _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-inj g′) lpV (λ _ → refl) ] ]
  sim-wrap v v′ (Inert.I-inj G-Fun _) (fun⊑ unk⊑ unk⊑) unk⊑ lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj G-Fun _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-inj G-Fun) lpV (λ _ → refl) ] ]
  sim-wrap v v′ (Inert.I-inj G-Pair _) (pair⊑ unk⊑ unk⊑) unk⊑ lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj G-Pair _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-inj G-Pair) lpV (λ _ → refl) ] ]
  sim-wrap v v′ (Inert.I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) unk⊑ lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj G-Sum _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-inj G-Sum) lpV (λ _ → refl) ] ]

  sim-wrap v v′ (Inert.I-fun _) unk⊑ unk⊑ lpV =
    [ _ , [ _ —→⟨ cast v {Active.A-id {a = A-Unk} _} ⟩ _ ∎ , dyn-value-⊑-wrap v v′ (Inert.I-fun _) lpV ] ]
  -- c : ⋆ ⇒ (A → B) is an active projection
  sim-wrap v v′ (Inert.I-fun _) unk⊑ (fun⊑ lp1 lp2) lpV =
    let a = Active.A-proj _ (λ ()) in
      [ _ , [ _ —→⟨ cast v {a} ⟩ _ ∎ , applyCast-⊑-wrap v v′ a (Inert.I-fun _) unk⊑ (fun⊑ lp1 lp2) lpV ] ]
  -- c : (A → B) ⇒ ⋆ can be either active or inert
  sim-wrap {c = c} v v′ (Inert.I-fun _) (fun⊑ lp1 lp2) unk⊑ lpV
    with ActiveOrInert c
  ... | inj₁ a = [ _ , [ _ —→⟨ cast v {a} ⟩ _ ∎ , applyCast-⊑-wrap v v′ a (Inert.I-fun _) (fun⊑ lp1 lp2) unk⊑ lpV ] ]
  ... | inj₂ (Inert.I-inj G-Fun _) =
    [ _ , [ _ —→⟨ wrap v {Inert.I-inj G-Fun c} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (lpit-inj G-Fun (fun⊑ unk⊑ unk⊑)) (⊑ᶜ-wrapr (lpti-fun (fun⊑ lp1 lp2) (fun⊑ unk⊑ unk⊑)) lpV λ ()) ] ]
  sim-wrap v v′ (Inert.I-fun _) (fun⊑ lp1 lp2) (fun⊑ lp3 lp4) lpV =
    [ _ , [ _ —→⟨ wrap v {Inert.I-fun _} ⟩ _ ∎ , ⊑ᶜ-wrap (lpii-fun (fun⊑ lp1 lp2) (fun⊑ lp3 lp4)) lpV (λ ()) ] ]

  sim-cast : ∀ {A A′ B B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c : Cast (A ⇒ B)} {c′ : Cast (A′ ⇒ B′)}
    → Value V → (v′ : Value V′)
    → (a′ : Active c′)
    → A ⊑ A′ → B ⊑ B′
    → ∅ , ∅ ⊢ V ⊑ᶜ V′
      ------------------------------------------------------------
    → ∃[ N ] ((V ⟨ c ⟩ —↠ N) × (∅ , ∅ ⊢ N ⊑ᶜ applyCast V′ v′ c′ {a′}))
  sim-cast v v′ (A-id _) lp1 lp2 lpV = [ _ , [ _ ∎ , ⊑ᶜ-castl lp1 lp2 lpV ] ]
  sim-cast v v′ (A-inj (cast A′ ⋆ _ _) ng nd) lp1 unk⊑ lpV
    with ground A′ {nd}
  ... | [ G′ , _ ] = [ _ , [ _ ∎ , ⊑ᶜ-castr unk⊑ unk⊑ (⊑ᶜ-cast lp1 unk⊑ lpV) ] ]
  sim-cast v v′ (A-proj (cast ⋆ B′ _ _) nd) unk⊑ lp2 lpV
    with ground? B′
  ... | yes b′-g
    with canonical⋆ _ v′
  ...   | [ G′ , [ W′ , [ c′ , [ i′ , meq′ ] ] ] ] rewrite meq′
    with gnd-eq? G′ B′ {inert-ground _ i′} {b′-g}
  ...     | yes ap rewrite ap = [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ lp2 (value-⊑-wrap-inv v v′ lpV) ] ]
  ...     | no  ap = [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ lp2 (⊑ᶜ-blame unk⊑) ] ]
  sim-cast v v′ (A-proj (cast ⋆ B′ _ _) nd) lp1 lp2 lpV | no b′-ng
    with ground B′ {nd}
  ...   | [ G′ , [ g′ , _ ] ] = [ _ , [ _ ∎ , ⊑ᶜ-cast unk⊑ lp2 (⊑ᶜ-castr unk⊑ unk⊑ lpV) ] ]

  sim-cast (V-wrap v i) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) unk⊑ unk⊑ (⊑ᶜ-wrapl (lpit-inj G-Pair _) (⊑ᶜ-cons lpV₁ lpV₂))
    with ~-relevant c~′
  ... | pair~ c~1′ c~2′ with v
  ...   | V-pair v₁ v₂ =
    [ _ ,
      [ _ —→⟨ cast (V-wrap v i) {A-id {a = A-Unk} _} ⟩ _ ∎ ,
        ⊑ᶜ-wrapl (⊑→lpit i (pair⊑ unk⊑ unk⊑) unk⊑) (⊑ᶜ-cons (⊑ᶜ-castr unk⊑ unk⊑ lpV₁) (⊑ᶜ-castr unk⊑ unk⊑ lpV₂)) ] ]
  sim-cast (V-wrap v i) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) unk⊑ lp2 (⊑ᶜ-wrapl (lpit-inj G-Pair _) (⊑ᶜ-cons lpV₁ lpV₂))
    with ~-relevant c~′
  ... | pair~ c~1′ c~2′ = [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ lp2 (⊑ᶜ-wrapl (⊑→lpit i ground-pair-⊑ unk⊑)
                                                                    (⊑ᶜ-cons (⊑ᶜ-castr unk⊑ unk⊑ lpV₁) (⊑ᶜ-castr unk⊑ unk⊑ lpV₂))) ] ]
  sim-cast {c = c} (V-pair v₁ v₂) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) (pair⊑ lp11 lp12) unk⊑ (⊑ᶜ-cons lpV₁ lpV₂)
    with ~-relevant c~′
  ... | pair~ c~1′ c~2′
    with ActiveOrInert c
  ...   | inj₁ a with a
  ...     | A-inj (cast (A `× B) ⋆ ℓ _) ng nd =
    let [ G , [ g~ , rd*₁ ] ] = applyCast-reduction-inj {ℓ = ℓ} (V-pair v₁ v₂) (λ x₂ → ⊥-elimi (ng x₂)) (eq-unk-relevant nd) in
    let [ _ , [ _ , rd*₂ ] ] = applyCast-reduction-pair {ℓ = ℓ} g~ v₁ v₂ in
      [ _ , [ _ —→⟨ cast (V-pair v₁ v₂) {A-inj _ ng nd} ⟩
                ↠-trans rd*₁ (_ —→⟨ ξ {F = F-cast _} (cast (V-pair v₁ v₂) {A-pair _}) ⟩ plug-cong (F-cast _) rd*₂) ,
                ⊑ᶜ-castl ground-pair-⊑ unk⊑ (⊑ᶜ-cons (⊑ᶜ-cast lp11 unk⊑ lpV₁) (⊑ᶜ-cast lp12 unk⊑ lpV₂)) ] ]
  sim-cast {c = c} (V-pair v₁ v₂) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) (pair⊑ lp11 lp12) unk⊑ (⊑ᶜ-cons lpV₁ lpV₂)
    | pair~ _ _ | inj₂ i with i
  ...     | I-inj G-Pair .c =
    [ _ , [ _ —→⟨ wrap (V-pair v₁ v₂) {i} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (⊑→lpit i (pair⊑ unk⊑ unk⊑) unk⊑)
                     (⊑ᶜ-cons (⊑ᶜ-castr unk⊑ unk⊑ lpV₁) (⊑ᶜ-castr unk⊑ unk⊑ lpV₂)) ] ]
  sim-cast {c = c} (V-pair v₁ v₂) (V-pair v₁′ v₂′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) (pair⊑ lp11 lp12) (pair⊑ lp21 lp22) (⊑ᶜ-cons lpV₁ lpV₂)
    with ~-relevant c~′
  ... | pair~ c~1′ c~2′ with c
  ...   | cast (A `× B) (C `× D) ℓ c~ =
    let [ _ , [ _ , rd* ] ] = applyCast-reduction-pair (~-relevant c~) v₁ v₂ in
      [ _ , [ _ —→⟨ cast (V-pair v₁ v₂) {A-pair _} ⟩ rd* ,
              ⊑ᶜ-cons (⊑ᶜ-cast lp11 lp21 lpV₁) (⊑ᶜ-cast lp12 lp22 lpV₂) ] ]

  sim-cast (V-wrap v i) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) unk⊑ unk⊑ (⊑ᶜ-wrapl (lpit-inj G-Sum _) (⊑ᶜ-inl unk⊑ lpV))
    with ~-relevant c~′
  ... | sum~ _ _ with v
  ...   | V-inl w =
    [ _ , [ _ —→⟨ cast (V-wrap v (I-inj G-Sum _)) {A-id {a = A-Unk} _} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (⊑→lpit i ground-sum-⊑ unk⊑) (⊑ᶜ-inl unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV)) ] ]
  sim-cast (V-wrap v i) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) unk⊑ (sum⊑ lp21 lp22) (⊑ᶜ-wrapl (lpit-inj G-Sum _) (⊑ᶜ-inl lp lpV))
    with ~-relevant c~′
  ... | sum~ _ _ =
    [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ (sum⊑ lp21 lp22) (⊑ᶜ-wrapl (lpit-inj G-Sum ground-sum-⊑) (⊑ᶜ-inl unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV))) ] ]
  sim-cast {c = c} (V-inl v) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) unk⊑ (⊑ᶜ-inl lp lpV)
    with ~-relevant c~′
  ... | sum~ _ _ with ActiveOrInert c
  ...   | inj₁ a with a
  ...     | A-inj (cast (A `⊎ B) ⋆ ℓ _) ng nd =
    let [ G , [ g~ , rd*₁ ] ] = applyCast-reduction-inj {ℓ = ℓ} (V-inl v) (λ x → ⊥-elimi (ng x)) (eq-unk-relevant nd) in
    let [ _ , rd*₂ ] = applyCast-reduction-sum-left {ℓ = ℓ} (~-relevant g~) v in
      [ _ , [ _ —→⟨ cast (V-inl v) {A-inj _ ng nd} ⟩
                ↠-trans rd*₁ (_ —→⟨ ξ {F = F-cast _} (cast (V-inl v) {A-sum _}) ⟩ plug-cong (F-cast _) rd*₂) ,
                ⊑ᶜ-castl ground-sum-⊑ unk⊑ (⊑ᶜ-inl unk⊑ (⊑ᶜ-cast lp11 unk⊑ lpV)) ] ]
  sim-cast {c = c} (V-inl v) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) unk⊑ (⊑ᶜ-inl lp lpV)
    | sum~ _ _ | inj₂ i with i
  ...     | I-inj G-Sum .c =
    [ _ , [ _ —→⟨ wrap (V-inl v) {i} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (⊑→lpit i (sum⊑ unk⊑ unk⊑) unk⊑) (⊑ᶜ-inl unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV)) ] ]
  sim-cast {c = c} (V-inl v) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inl lp lpV)
    with ~-relevant c~′
  ... | sum~ _ _ with c
  ...   | cast (A `⊎ B) (C `⊎ D) ℓ c~ =
    let [ _ , rd* ] = applyCast-reduction-sum-left {ℓ = ℓ} (~-relevant c~) v in
      [ _ , [ _ —→⟨ cast (V-inl v) {A-sum _} ⟩ rd* , ⊑ᶜ-inl lp22 (⊑ᶜ-cast lp11 lp21 lpV) ] ]
  sim-cast (V-wrap v i) (V-inr v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) unk⊑ unk⊑ (⊑ᶜ-wrapl (lpit-inj G-Sum _) (⊑ᶜ-inr unk⊑ lpV))
    with ~-relevant c~′
  ... | sum~ _ _ with v
  ...   | V-inr w =
    [ _ , [ _ —→⟨ cast (V-wrap v (I-inj G-Sum _)) {A-id {a = A-Unk} _} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (⊑→lpit i ground-sum-⊑ unk⊑) (⊑ᶜ-inr unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV)) ] ]
  sim-cast (V-wrap v i) (V-inr v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) unk⊑ (sum⊑ lp21 lp22) (⊑ᶜ-wrapl (lpit-inj G-Sum _) (⊑ᶜ-inr lp lpV))
    with ~-relevant c~′
  ... | sum~ _ _ =
    [ _ , [ _ ∎ , ⊑ᶜ-castl unk⊑ (sum⊑ lp21 lp22) (⊑ᶜ-wrapl (lpit-inj G-Sum ground-sum-⊑) (⊑ᶜ-inr unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV))) ] ]
  sim-cast {c = c} (V-inr v) (V-inr v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) unk⊑ (⊑ᶜ-inr lp lpV)
    with ~-relevant c~′
  ... | sum~ _ _ with ActiveOrInert c
  ...   | inj₁ a with a
  ...     | A-inj (cast (A `⊎ B) ⋆ ℓ _) ng nd =
    let [ G , [ g~ , rd*₁ ] ] = applyCast-reduction-inj {ℓ = ℓ} (V-inr v) (λ x → (⊥-elimi (ng x))) (eq-unk-relevant nd) in
    let [ _ , rd*₂ ] = applyCast-reduction-sum-right {ℓ = ℓ} (~-relevant g~) v in
      [ _ , [ _ —→⟨ cast (V-inr v) {A-inj _ ng nd} ⟩
                ↠-trans rd*₁ (_ —→⟨ ξ {F = F-cast _} (cast (V-inr v) {A-sum _}) ⟩ plug-cong (F-cast _) rd*₂) ,
                ⊑ᶜ-castl ground-sum-⊑ unk⊑ (⊑ᶜ-inr unk⊑ (⊑ᶜ-cast lp12 unk⊑ lpV)) ] ]
  sim-cast {c = c} (V-inr v) (V-inr v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) unk⊑ (⊑ᶜ-inr lp lpV)
    | sum~ _ _ | inj₂ i with i
  ...     | I-inj G-Sum .c =
    [ _ , [ _ —→⟨ wrap (V-inr v) {i} ⟩ _ ∎ ,
            ⊑ᶜ-wrapl (⊑→lpit i (sum⊑ unk⊑ unk⊑) unk⊑) (⊑ᶜ-inr unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV)) ] ]
  sim-cast {c = c} (V-inr v) (V-inr v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inr lp lpV)
    with ~-relevant c~′
  ... | sum~ _ _ with c
  ...   | cast (A `⊎ B) (C `⊎ D) ℓ c~ =
    let [ _ , rd* ] = applyCast-reduction-sum-right {ℓ = ℓ} (~-relevant c~) v in
      [ _ , [ _ —→⟨ cast (V-inr v) {A-sum _} ⟩ rd* , ⊑ᶜ-inr lp21 (⊑ᶜ-cast lp12 lp22 lpV) ] ]

  castr-wrap : ∀ {A A′ B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c′ : Cast (A′ ⇒ B′)}
    → Value V → (v′ : Value V′)
    → (i′ : Inert c′)
    → A ⊑ A′ → A ⊑ B′
    → ∅ , ∅ ⊢ V ⊑ᶜ V′
      -----------------------------------------------------
    → ∅ , ∅ ⊢ V ⊑ᶜ V′ ⟪ i′ ⟫
  castr-wrap v v′ (I-inj g′ _) lp1 unk⊑ lpV = dyn-value-⊑-wrap v v′ (I-inj g′ _) lpV
  castr-wrap v v′ (I-fun _) unk⊑ unk⊑ lpV = dyn-value-⊑-wrap v v′ (I-fun _) lpV
  castr-wrap v v′ (I-fun _) (fun⊑ lp1 lp2) (fun⊑ lp3 lp4) lpV =
    ⊑ᶜ-wrapr (lpti-fun (fun⊑ lp1 lp2) (fun⊑ lp3 lp4)) lpV λ ()

  castr-cast : ∀ {A A′ B′} {V : ∅ ⊢ A} {V′ : ∅ ⊢ A′} {c′ : Cast (A′ ⇒ B′)}
    → Value V → (v′ : Value V′)
    → (a′ : Active c′)
    → A ⊑ A′ → A ⊑ B′
    → ∅ , ∅ ⊢ V ⊑ᶜ V′
      ------------------------------------------------------------
    → ∅ , ∅ ⊢ V ⊑ᶜ applyCast V′ v′ c′ {a′}
  castr-cast v v′ (A-id _) lp1 lp2 lpV = lpV
  castr-cast v v′ (A-inj (cast A′ ⋆ _ _) ng nd) lp1 unk⊑ lpV
    with ground A′ {nd}
  ... | [ G′ , _ ] = ⊑ᶜ-castr unk⊑ unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV)
  castr-cast v v′ (A-proj (cast ⋆ B′ _ _) nd) unk⊑ lp2 lpV
    with ground? B′
  ... | yes b′-g
    with canonical⋆ _ v′
  ...   | [ G′ , [ W′ , [ c′ , [ i′ , meq′ ] ] ] ] rewrite meq′
    with gnd-eq? G′ B′ {inert-ground _ i′} {b′-g}
  ...     | yes ap rewrite ap = value-⊑-wrap-inv v v′ lpV
  ...     | no  ap = ⊑ᶜ-blame unk⊑
  castr-cast v v′ (A-proj (cast ⋆ B′ _ _) nd) lp1 lp2 lpV | no b′-ng
    with ground B′ {nd}
  ...   | [ G′ , [ g′ , _ ] ] = ⊑ᶜ-castr unk⊑ unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpV)
  castr-cast (V-wrap v i) (V-pair v′ w′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′))
             unk⊑ unk⊑ (⊑ᶜ-wrapl (lpit-inj G-Pair (pair⊑ unk⊑ unk⊑)) lpV)
    with ~-relevant c~′
  ... | pair~ _ _ with v | lpV
  ...   | V-pair v₁ v₂ | ⊑ᶜ-cons lpV₁ lpV₂ =
    ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Pair _) (pair⊑ unk⊑ unk⊑) unk⊑) (⊑ᶜ-cons (⊑ᶜ-castr unk⊑ unk⊑ lpV₁) (⊑ᶜ-castr unk⊑ unk⊑ lpV₂))
  castr-cast (V-pair v w) (V-pair v′ w′) (A-pair (cast (A′ `× B′) (C′ `× D′) _ c~′)) (pair⊑ lp11 lp12) (pair⊑ lp21 lp22) (⊑ᶜ-cons lpV lpW)
    with ~-relevant c~′
  ... | pair~ _ _ = ⊑ᶜ-cons (⊑ᶜ-castr lp11 lp21 lpV) (⊑ᶜ-castr lp12 lp22 lpW)
  castr-cast (V-wrap v i) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′))
             unk⊑ unk⊑ (⊑ᶜ-wrapl (lpit-inj G-Sum (sum⊑ unk⊑ unk⊑)) lpV)
    with ~-relevant c~′
  ... | sum~ _ _ with v | lpV
  ...   | V-inl w | ⊑ᶜ-inl lp lpW =
      ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) unk⊑) (⊑ᶜ-inl unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpW))
  castr-cast (V-wrap v i) (V-inr v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′))
             unk⊑ unk⊑ (⊑ᶜ-wrapl (lpit-inj G-Sum (sum⊑ unk⊑ unk⊑)) lpV)
    with ~-relevant c~′
  ... | sum~ _ _ with v | lpV
  ...   | V-inr w | ⊑ᶜ-inr lp lpW =
      ⊑ᶜ-wrapl (⊑→lpit (I-inj G-Sum _) (sum⊑ unk⊑ unk⊑) unk⊑) (⊑ᶜ-inr unk⊑ (⊑ᶜ-castr unk⊑ unk⊑ lpW))
  castr-cast (V-inl v) (V-inl v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inl lp lpV)
    with ~-relevant c~′
  ... | sum~ _ _ = ⊑ᶜ-inl lp22 (⊑ᶜ-castr lp11 lp21 lpV)
  castr-cast (V-inr v) (V-inr v′) (A-sum (cast (A′ `⊎ B′) (C′ `⊎ D′) _ c~′)) (sum⊑ lp11 lp12) (sum⊑ lp21 lp22) (⊑ᶜ-inr lp lpV)
    with ~-relevant c~′
  ... | sum~ _ _ = ⊑ᶜ-inr lp21 (⊑ᶜ-castr lp12 lp22 lpV)

  open import CastStructureWithPrecision
  csp : CastStructWithPrecision
  csp = record { pcsp = pcsp ; applyCast = applyCast ;
          {------------------------------------}
          applyCast-catchup = applyCast-catchup;
          sim-cast = sim-cast;
          sim-wrap = sim-wrap;
          castr-cast = castr-cast;
          castr-wrap = castr-wrap
        }

  {- Instantiate the proof of "compilation from GTLC to CC preserves precision". -}
  open import CompilePresPrec pcsp
  open CompilePresPrecProof (λ A B ℓ {c} → cast A B ℓ c) using (compile-pres-prec) public

  {- Instantiate the proof for the gradual guarantee. -}
  open import ParamGradualGuarantee csp
