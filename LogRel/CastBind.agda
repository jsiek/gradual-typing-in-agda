{-# OPTIONS --rewriting #-}
module LogRel.CastBind where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
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
open import LogRel.CastLogRel

{----------------- ℰ-bind (Monadic Bind Lemma) -------------------------------}

data PEFrame : Set where
  `_ : Frame → PEFrame
  □ : PEFrame

_⦉_⦊ : PEFrame → Term → Term
(` F) ⦉ M ⦊ = F ⟦ M ⟧
□ ⦉ M ⦊ = M

𝒱→ℰF : Prec → Prec → PEFrame → PEFrame → Term → Term → Setᵒ
𝒱→ℰF c d F F′ M M′ = ∀ᵒ[ V ] ∀ᵒ[ V′ ] (M —↠ V)ᵒ →ᵒ (M′ —↠ V′)ᵒ
                   →ᵒ 𝒱⟦ d ⟧ V V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)

𝒱→ℰF-reduce-L : ∀{𝒫}{c}{d}{F}{F′}{M}{M′}{N}
   → M —→ N
   → 𝒫 ⊢ᵒ 𝒱→ℰF c d F F′ M M′
     -------------------------
   → 𝒫 ⊢ᵒ 𝒱→ℰF c d F F′ N M′
𝒱→ℰF-reduce-L {𝒫}{c}{d}{F}{F′}{M}{M′}{N} M→N 𝒱→ℰF[MM′] =
  Λᵒ[ V ] Λᵒ[ V′ ]
  let 𝒱→ℰF[NM′] : 𝒱⟦ d ⟧ V V′ ∷ (M′ —↠ V′)ᵒ ∷ (N —↠ V)ᵒ ∷ 𝒫
               ⊢ᵒ ℰ⟦ c ⟧  (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)
      𝒱→ℰF[NM′] = ⊢ᵒ-sucP (Sᵒ Zᵒ) λ M′—↠V′ →
               ⊢ᵒ-sucP (Sᵒ (Sᵒ Zᵒ)) λ N—↠V →
               let M—↠V = constᵒI (M —→⟨ M→N ⟩ N—↠V) in
               let 𝒱→ℰF[MM′]VV′ = Sᵒ (Sᵒ (Sᵒ
                                    (instᵒ (instᵒ 𝒱→ℰF[MM′] V) V′)))
               in appᵒ (appᵒ (appᵒ 𝒱→ℰF[MM′]VV′ M—↠V) (constᵒI M′—↠V′)) Zᵒ
  in →ᵒI (→ᵒI (→ᵒI 𝒱→ℰF[NM′]))

𝒱→ℰF-reduce-R : ∀{𝒫}{c}{d}{F}{F′}{M}{M′}{N′}
   → M′ —→ N′
   → 𝒫 ⊢ᵒ 𝒱→ℰF c d F F′ M M′
     -------------------------
   → 𝒫 ⊢ᵒ 𝒱→ℰF c d F F′ M N′
𝒱→ℰF-reduce-R {𝒫}{c}{d}{F}{F′}{M}{M′}{N′} M′→N′ 𝒱→ℰF[MM′] =
  Λᵒ[ V ] Λᵒ[ V′ ]
  let 𝒱→ℰF[MN′] : 𝒱⟦ d ⟧ V V′ ∷ (N′ —↠ V′)ᵒ ∷ (M —↠ V)ᵒ ∷ 𝒫
               ⊢ᵒ ℰ⟦ c ⟧  (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)
      𝒱→ℰF[MN′] = ⊢ᵒ-sucP (Sᵒ Zᵒ) λ N′—↠V′ →
               ⊢ᵒ-sucP (Sᵒ (Sᵒ Zᵒ)) λ M—↠V →
               let M′—↠V′ = constᵒI (M′ —→⟨ M′→N′ ⟩ N′—↠V′) in
               let 𝒱→ℰF[MM′]VV′ = Sᵒ (Sᵒ (Sᵒ
                                    (instᵒ (instᵒ 𝒱→ℰF[MM′] V) V′)))
               in appᵒ (appᵒ (appᵒ 𝒱→ℰF[MM′]VV′ (constᵒI M—↠V)) M′—↠V′) Zᵒ
  in →ᵒI (→ᵒI (→ᵒI 𝒱→ℰF[MN′]))


ℰ-blame : ∀{𝒫}{c}{M} → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ M blame
ℰ-blame {𝒫}{c}{M} = substᵒ (≡ᵒ-sym ℰ-stmt)
                            (inj₂ᵒ (inj₂ᵒ (inj₂ᵒ (constᵒI isBlame))))

ξ′ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : PEFrame)
    → M′ ≡ F ⦉ M ⦊
    → N′ ≡ F ⦉ N ⦊
    → M —→ N
      --------
    → M′ —→ N′
ξ′ (` F) refl refl M→N = ξ F M→N
ξ′ □ refl refl M→N = M→N

ξ′-blame : ∀ {M′ : Term}
   → (F : PEFrame)
   → M′ ≡ F ⦉ blame ⦊
     ------------------------
   → M′ —→ blame ⊎ M′ ≡ blame
ξ′-blame (` F) refl = inj₁ (ξ-blame F)
ξ′-blame □ refl = inj₂ refl

frame-inv3 : ∀{L N : Term}{F : PEFrame}
   → reducible L
   → F ⦉ L ⦊ —→ N
   → ∃[ L′ ] ((L —→ L′) × (N ≡ F ⦉ L′ ⦊))
frame-inv3 {L}{N}{□} rL FL→N = _ , (FL→N , refl)
frame-inv3 {L}{N}{` F} rL FL→N = frame-inv2 rL FL→N

blame-frame2 : ∀{F}{N}
   → (F ⦉ blame ⦊) —→ N
   → N ≡ blame
blame-frame2 {□}{N} Fb→N = ⊥-elim (blame-irreducible Fb→N)
blame-frame2 {` F}{N} Fb→N = blame-frame Fb→N

ℰ-bind-M : Prec → Prec → PEFrame → PEFrame → Term → Term → Setᵒ
ℰ-bind-M c d F F′ M M′ = ℰ⟦ d ⟧ M M′ →ᵒ 𝒱→ℰF c d F F′ M M′
    →ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)

ℰ-bind-prop : Prec → Prec → PEFrame → PEFrame → Setᵒ
ℰ-bind-prop c d F F′ = ∀ᵒ[ M ] ∀ᵒ[ M′ ] ℰ-bind-M c d F F′ M M′

ℰ-bind-aux : ∀{𝒫}{c}{d}{F}{F′} → 𝒫 ⊢ᵒ ℰ-bind-prop c d F F′
ℰ-bind-aux {𝒫}{c}{d}{F}{F′} = lobᵒ Goal
 where     
 Goal : ▷ᵒ ℰ-bind-prop c d F F′ ∷ 𝒫 ⊢ᵒ ℰ-bind-prop c d F F′
 Goal = Λᵒ[ M ] Λᵒ[ M′ ] →ᵒI (→ᵒI Goal′)
  where
  Goal′ : ∀{M}{M′}
     → (𝒱→ℰF c d F F′ M M′) ∷ ℰ⟦ d ⟧ M M′ ∷ ▷ᵒ ℰ-bind-prop c d F F′ ∷ 𝒫
        ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
  Goal′{M}{M′} =
     case4ᵒ (substᵒ ℰ-stmt (Sᵒ Zᵒ)) Mval MredL MredR (Mblame{F′ = F′})
   where
   𝒫′ = (𝒱→ℰF c d F F′ M M′) ∷ ℰ⟦ d ⟧ M M′ ∷ ▷ᵒ ℰ-bind-prop c d F F′ ∷ 𝒫

   Mval : 𝒱⟦ d ⟧ M M′ ∷ 𝒫′ ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
   Mval =
     let Cont = λ V → ∀ᵒ[ V′ ] (M —↠ V)ᵒ →ᵒ (M′ —↠ V′)ᵒ
                   →ᵒ 𝒱⟦ d ⟧ V V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊) in
     let Cont′ = λ V′ → (M —↠ M)ᵒ →ᵒ (M′ —↠ V′)ᵒ
                   →ᵒ 𝒱⟦ d ⟧ M V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ V′ ⦊) in
     appᵒ (appᵒ (appᵒ (instᵒ-new Cont′ (instᵒ-new Cont (Sᵒ Zᵒ) M) M′)
                      (constᵒI (M END)))
                (constᵒI (M′ END)))
          Zᵒ 

   MredL : reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′ ⊢ᵒ ℰ⟦ c ⟧(F ⦉ M ⦊)(F′ ⦉ M′ ⦊)
   MredL = substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₁ᵒ (redFM ,ᵒ presFM)))
    where
    redFM : reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′ ⊢ᵒ reducible (F ⦉ M ⦊) ᵒ
    redFM = constᵒE (proj₁ᵒ Zᵒ) λ {(N , M→N) →
      constᵒI (F ⦉ N ⦊ , ξ′ F refl refl M→N)}
    
    presFM : reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′
              ⊢ᵒ preserve-L c (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
    presFM = Λᵒ[ N ] →ᵒI ▷ℰFM′
     where
     ▷ℰFM′ : ∀{N} → (F ⦉ M ⦊ —→ N)ᵒ ∷ reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′
             ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ N (F′ ⦉ M′ ⦊))
     ▷ℰFM′ {N} =
       constᵒE Zᵒ λ FM→N →
       constᵒE (proj₁ᵒ (Sᵒ Zᵒ)) λ rM →
       let 𝒫″ = (F ⦉ M ⦊ —→ N)ᵒ ∷ reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′ in
       let finv = frame-inv3{F = F} rM FM→N in
       let N₁ = proj₁ finv in
       let M→N₁ = proj₁ (proj₂ finv) in
       let N≡ = proj₂ (proj₂ finv) in
       {-
               M   —→  N₁
           F ⟦ M ⟧ —→  F ⟦ N₁ ⟧  ≡  N
       -}
       let ▷ℰN₁M′ : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ d ⟧ N₁ M′)
           ▷ℰN₁M′ = appᵒ (instᵒ{P = λ N → ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ d ⟧ N M′))}
                              (proj₂ᵒ{𝒫″} (Sᵒ Zᵒ)) N₁) (constᵒI M→N₁) in
       let ▷M′→V→𝒱→ℰF : 𝒫″ ⊢ᵒ ▷ᵒ (𝒱→ℰF c d F F′ N₁ M′)
           ▷M′→V→𝒱→ℰF = monoᵒ (𝒱→ℰF-reduce-L{𝒫″}{c}{d}{F}{F′} M→N₁
                                  (Sᵒ (Sᵒ Zᵒ))) in
       let IH : 𝒫″ ⊢ᵒ ▷ᵒ ℰ-bind-prop c d F F′
           IH = Sᵒ (Sᵒ (Sᵒ (Sᵒ Zᵒ))) in
       let IH[N₁,M′] : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ-bind-M c d F F′ N₁ M′)
           IH[N₁,M′] =
             let F₁ = λ M → (▷ᵒ (∀ᵒ[ M′ ] ℰ-bind-M c d F F′ M M′)) in
             instᵒ (▷∀ (instᵒ{P = F₁} (▷∀ IH) N₁)) M′ in
       let ▷ℰFN₁FM′ : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ (F ⦉ N₁ ⦊) (F′ ⦉ M′ ⦊))
           ▷ℰFN₁FM′ = appᵒ (▷→ (appᵒ (▷→ IH[N₁,M′]) ▷ℰN₁M′)) ▷M′→V→𝒱→ℰF  in
       subst (λ N → 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ N (F′ ⦉ M′ ⦊))) (sym N≡) ▷ℰFN₁FM′
     
   MredR : reducible M′ ᵒ ×ᵒ preserve-R d M M′ ∷ 𝒫′
             ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
   MredR = substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ (redFM′ ,ᵒ presFM′))))
    where
    redFM′ : reducible M′ ᵒ ×ᵒ preserve-R d M M′ ∷ 𝒫′ ⊢ᵒ reducible (F′ ⦉ M′ ⦊) ᵒ
    redFM′ = constᵒE (proj₁ᵒ Zᵒ) λ {(N , M′→N) →
       constᵒI (F′ ⦉ N ⦊ , ξ′ F′ refl refl M′→N)}

    presFM′ : reducible M′ ᵒ ×ᵒ preserve-R d M M′ ∷ 𝒫′
              ⊢ᵒ preserve-R c (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
    presFM′ = Λᵒ[ N′ ] →ᵒI ▷ℰFMN′
     where
     ▷ℰFMN′ : ∀{N′} → (F′ ⦉ M′ ⦊ —→ N′)ᵒ ∷ reducible M′ ᵒ ×ᵒ preserve-R d M M′
                      ∷ 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ (F ⦉ M ⦊) N′)
     ▷ℰFMN′ {N′} =
       constᵒE Zᵒ λ FM′→N′ →
       constᵒE (proj₁ᵒ (Sᵒ Zᵒ)) λ rM′ →
       let 𝒫″ =(F′ ⦉ M′ ⦊ —→ N′)ᵒ ∷ reducible M′ ᵒ ×ᵒ preserve-R d M M′ ∷ 𝒫′ in
       let finv = frame-inv3{F = F′} rM′ FM′→N′ in
       let N₁ = proj₁ finv in
       let M′→N₁ = proj₁ (proj₂ finv) in
       let N′≡F[N₁] = proj₂ (proj₂ finv) in
       let ▷ℰMN₁ : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ d ⟧ M N₁)
           ▷ℰMN₁ = appᵒ (instᵒ{P = λ N′ → ((M′ —→ N′)ᵒ →ᵒ ▷ᵒ (ℰ⟦ d ⟧ M N′))}
                              (proj₂ᵒ{𝒫″} (Sᵒ Zᵒ)) N₁) (constᵒI M′→N₁) in
       let ▷𝒱→ℰF[M,N₁] : 𝒫″ ⊢ᵒ ▷ᵒ (𝒱→ℰF c d F F′ M N₁)
           ▷𝒱→ℰF[M,N₁] = monoᵒ (𝒱→ℰF-reduce-R{𝒫″}{c}{d}{F}{F′} M′→N₁
                                  (Sᵒ (Sᵒ Zᵒ))) in
       let IH : 𝒫″ ⊢ᵒ ▷ᵒ ℰ-bind-prop c d F F′
           IH = Sᵒ (Sᵒ (Sᵒ (Sᵒ Zᵒ))) in
       let IH[M,N₁] : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ-bind-M c d F F′ M N₁)
           IH[M,N₁] =
             let F₁ = λ M → (▷ᵒ (∀ᵒ[ M′ ] ℰ-bind-M c d F F′ M M′)) in
             let F₂ = λ M′ → ▷ᵒ ℰ-bind-M c d F F′ M M′ in
             instᵒ{P = F₂} (▷∀ (instᵒ{P = F₁} (▷∀ IH) M)) N₁ in
       let ▷ℰFMFN₁ : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ N₁ ⦊))
           ▷ℰFMFN₁ = appᵒ (▷→ (appᵒ (▷→ IH[M,N₁]) ▷ℰMN₁)) ▷𝒱→ℰF[M,N₁] in
       subst(λ N′ → 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ (F ⦉ M ⦊) N′)) (sym N′≡F[N₁]) ▷ℰFMFN₁ 

   Mblame : ∀{F′} → Blame M′ ᵒ ∷ 𝒫′ ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
   Mblame {F′}
      with F′
   ... | □ = substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₂ᵒ (inj₂ᵒ Zᵒ)))
   ... | ` F′ =
    substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ
                           (constᵒE Zᵒ λ {isBlame → redFblame ,ᵒ presFblame}))))
    where
    redFblame : (Blame blame)ᵒ ∷ 𝒫′ ⊢ᵒ (reducible (F′ ⟦ blame ⟧))ᵒ
    redFblame =
     constᵒE Zᵒ λ {isBlame → constᵒI (_ , (ξ-blame F′)) }
    
    presFblame : (Blame blame)ᵒ ∷ 𝒫′ ⊢ᵒ preserve-R c (F ⦉ M ⦊) (F′ ⟦ blame ⟧)
    presFblame = Λᵒ[ N′ ] →ᵒI (constᵒE Zᵒ λ Fb→N′ →
      let eq = blame-frame{F = F′} Fb→N′ in
      let 𝒫″ = (F′ ⟦ blame ⟧ —→ N′)ᵒ ∷ (Blame blame)ᵒ ∷ 𝒫′ in
      subst (λ N′ → 𝒫″ ⊢ᵒ ▷ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) N′) (sym eq) (monoᵒ ℰ-blame))

ℰ-bind : ∀{𝒫}{c d : Prec}{F}{F′}{M}{M′}
   → 𝒫 ⊢ᵒ ℰ⟦ d ⟧ M M′ 
   → 𝒫 ⊢ᵒ (∀ᵒ[ V ] ∀ᵒ[ V′ ] (M —↠ V)ᵒ →ᵒ (M′ —↠ V′)ᵒ
              →ᵒ 𝒱⟦ d ⟧ V V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊))
     ----------------------------------------------------------
   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
ℰ-bind {𝒫}{c}{d}{F}{F′}{M}{M′} ⊢ℰMM′ ⊢𝒱V→ℰFV =
  let F₁ = λ M → ∀ᵒ[ M′ ] ℰ-bind-M c d F F′ M M′ in
  let F₂ = λ M′ → ℰ-bind-M c d F F′ M M′ in
  let xx = instᵒ{P = F₂} (instᵒ{𝒫}{P = F₁} (ℰ-bind-aux{F = F}{F′}) M) M′ in
  appᵒ (appᵒ xx ⊢ℰMM′) ⊢𝒱V→ℰFV

