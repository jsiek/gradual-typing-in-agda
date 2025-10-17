

# Polymorphic Gradually Typed Lambda Calculus (Surface Language, PGL)

## Syntax

    Types         A, B, C  ::=  X | A → B | ∀X.A | ★
    Terms         L, M, N  ::=  x | λx:A.N | ΛX.V | L M | L[A] | M : A
    Values        V, W     ::=  λx:A.N | ΛX.V
    Environments  Γ        ::=  ∅ | Γ, x:A | Γ, X

# Free Type Variables

    FV(X) = {X}
    FV(A → B) = FV(A) ∪ FV(B)
    FV(∀X.A) = FV(A) - {X}
    FV(★) = ∅

## Consistency

    Consistency Context   Ψ ::= ∅ | Ψ,X

    -------------
    | Ψ ⊢ A ~ B |
    -------------

    ----------
    Ψ ⊢ ι ~ ι

    ----------
    Ψ ⊢ X ~ X

    ----------
    Ψ ⊢ ★ ~ ★

    ---------- (X ∈ Ψ)
    Ψ ⊢ ★ ~ X

    ---------- (X ∈ Ψ)
    Ψ ⊢ X ~ ★

    ---------
    Ψ ⊢ ★ ~ ι

    ---------
    Ψ ⊢ ι ~ ★

    Ψ ⊢ ★ ~ A   Ψ ⊢ ★ ~ B
    ----------------------
    Ψ ⊢ ★ ~ A → B

    Ψ ⊢ A ~ ★   Ψ ⊢ B ~ ★
    ----------------------
    Ψ ⊢ A → B ~ ★

    Ψ,X ⊢ A ~ ★
    -------------
    Ψ ⊢ ∀X.A ~ ★

    Ψ,X ⊢ ★ ~ B
    -------------
    Ψ ⊢ ★ ~ ∀X.B

    Ψ ⊢ A ~ A′  Ψ ⊢ B ~ B′
    ----------------------
    Ψ ⊢ A → B ~ A′ → B′
    
    Ψ ⊢ A ~ A′
    -----------------
    Ψ ⊢ ∀X.A ~ ∀X.A′

    Ψ,X ⊢ A ~ B
    -------------- (B ≠ ∀Y.C, X ∉ B)
    Ψ ⊢ ∀X.A ~ B

    Ψ,X ⊢ A ~ B
    -------------- (A ≠ ∀Y.C, X ∉ A)
    Ψ ⊢ A ~ ∀X.B

## Precision

    -------------
    | Ψ ⊢ A ⊑ B |
    -------------

    ----------
    Ψ ⊢ ι ⊑ ι

    ----------
    Ψ ⊢ X ⊑ X

    ----------
    Ψ ⊢ ★ ⊑ ★

    ---------- (X ∈ Ψ)
    Ψ ⊢ ★ ⊑ X

    ---------
    Ψ ⊢ ★ ⊑ ι

    Ψ ⊢ ★ ⊑ A   Ψ ⊢ ★ ⊑ B
    ----------------------
    Ψ ⊢ ★ ⊑ A → B

    Ψ,X ⊢ ★ ⊑ B
    -------------
    Ψ ⊢ ★ ⊑ ∀X.B

    Ψ ⊢ A ⊑ A′  Ψ ⊢ B ⊑ B′
    ----------------------
    Ψ ⊢ A → B ⊑ A′ → B′
    
    Ψ ⊢ A ⊑ A′
    -----------------
    Ψ ⊢ ∀X.A ⊑ ∀X.A′

    Ψ,X ⊢ A ⊑ B
    -------------- (A ≠ ∀Y.C, X ∉ A)
    Ψ ⊢ A ⊑ ∀X.B


## Well-formed Types


## Type System

    (x:A) ∈ Γ
    ---------
    Γ ⊢ x : A

    Γ ⊢ A ok  Γ, x:A ⊢ N : B
    ------------------------
    Γ ⊢ λx:A.N : A → B

    Γ ⊢ L : A → B     Γ ⊢ M : A
    ---------------------------
    Γ ⊢ L M : B

    Γ ⊢ L : ★     Γ ⊢ M : A
    -----------------------
    Γ ⊢ L M : ★

    Γ, X ⊢ M : B
    ---------------
    Γ ⊢ ΛX.M : ∀X.B

    Γ ⊢ L : ∀X.A    Γ ⊢ B ok
    ------------------------
    Γ ⊢ L[B] : A[B/X]

    Γ ⊢ L : ★    Γ ⊢ B ok
    ---------------------
    Γ ⊢ L[B] : ★

    Γ ⊢ M : A′   Γ ⊢ A ok
    --------------------- (A′ ~ A)
    Γ ⊢ (M : A) : A
    
## Term Precision



# Polymorphic Cast Calculus (PCC, Internal Language)

## Syntax

    Types         A, B, C  ::=  X | A → B | ∀X.A | ★
    Ground Types  G, H     ::=  ι | ★→★
    Terms         L, M, N  ::=  x | λx.N | ΛX.M | L M | L[X] | νX=A.M
                             | M⟨c⟩ | blame
    Values        V, W     ::= λx.N | ΛX.V | V⟨c → d⟩ | V⟨∀X.c⟩ | V⟨gen X.c⟩
    Coercions     c, d     ::= id | G? | G! | X↓ | X↑ | c → d | c ; d
                             | ∀X.c | gen X.c | inst X.c

    Environments  Γ        ::=  ∅ | Γ, x:A | Γ, X | Γ, X=A

## Reductions

    ----------
    | M —→ N |
    ----------

    (λx.N) V              —→  N[V/x]
    (ΛX.M)[Y]             —→  M[Y/X]
    V⟨∀X.c⟩[Y]            —→  V[Y]⟨c[Y/X]⟩
    V⟨gen X.d⟩[Y]          —→ V⟨c[Y/X]⟩
    V⟨inst X.c⟩           —→  νX=★. V[X]⟨c⟩
    V⟨id⟩                  —→  V
    V⟨X↓⟩⟨X↑⟩              —→  V
    V⟨G!⟩⟨G?⟩              —→  V
    V⟨G!⟩⟨H?l⟩             —→  blame l    (G ≠ H)
    V⟨c → d⟩ W             —→  (V W⟨c⟩)⟨d⟩
    V⟨c ; d⟩              —→  V⟨c⟩⟨d⟩

    ------------------
    | Σ ⊢ M —→ Σ ⊢ N |
    ------------------
    
    M —→ N
    --------------
    Σ ⊢ M —→ Σ ⊢ N

    Σ ⊢ M —→ Σ′ ⊢ N
    ---------------------
    Σ ⊢ F[M] —→ Σ′ ⊢ F[N]

    ----------------------
    Σ ⊢ νX.N —→  Σ, X ⊢ N
    

## Coercion Typing

    -----------------
    | Γ ⊢ c : A ⇒ B |
    -----------------

    --------------
    Γ ⊢ id : A ⇒ A

    --------------
    Γ ⊢ G? : ★ ⇒ G

    --------------
    Γ ⊢ G! : G ⇒ ★
        
    -------------- (X=A ∈ Γ)
    Γ ⊢ X↓ : A ⇒ X

    -------------- (X=A ∈ Γ)
    Γ ⊢ X↑ : X ⇒ A

    Γ,X=★ ⊢ c : A ⇒ B
    ------------------------
    Γ ⊢ gen X. c : A ⇒ ∀X.B

    Γ,X=★ ⊢ c : A ⇒ B
    ------------------------
    Γ ⊢ inst X.c : ∀X.A ⇒ B

    Γ,X ⊢ c : A ⇒ B
    ------------------------
    Γ ⊢ ∀ X.c : ∀X.A ⇒ ∀X.B

    Γ ⊢ c : C ⇒ A   Γ ⊢ d : B ⇒ D
    ------------------------------
    Γ ⊢ c → d : A → B ⇒ C → D

    Γ ⊢ c : A ⇒ B   Γ ⊢ d : B ⇒ C
    ------------------------------
    Γ ⊢ c ; d : A ⇒ C


## Type System

    -------------
    | Γ ⊢ M : A |
    -------------

    Γ ⊢ M : A   Γ ⊢ c : A ⇒ B
    -------------------------          Cast
    Γ ⊢ M⟨c⟩ : B

    Γ ⊢ L : ∀X.A
    -----------------                  Type application
    Γ ⊢ L[X] : A

    Γ, X=A ⊢ N : B
    --------------- (X ∉ B)            Generate fresh type variable
    Γ ⊢ νX=A.N : B

## Configuration Typing

    ---------
    | Γ ⊢ Σ |
    ---------

    ------
    ∅ ⊢ ∅

    -------------
    Γ, X=A ⊢ Σ, X

    -------------
    | Σ ⊢ M : A |
    -------------

    Γ ⊢ Σ   Γ ⊢ M : A
    -----------------
    Σ ⊢ M : A

## Term Precision (for the Gradual Guarantee)



# Compilation From PGL to PCC

## Compilation of Conversions

    ------------------
    | 𝒞⟦ A ⇒ B ⟧ = c |  pre: Ψ ⊢ A ~ B
    ------------------
    
    𝒞⟦ ι ⇒ ι ⟧        = id
    𝒞⟦ ★ ⇒ ★ ⟧       = id
    𝒞⟦ X ⇒ X ⟧       = id
    𝒞⟦ G ⇒ ★ ⟧ = G!
    𝒞⟦ ★ ⇒ G ⟧ = G?
    𝒞⟦ (A → B) ⇒ ★ ⟧ = (c → d) ; ★→★!
       where
       𝒞⟦ ★ ⇒ A ⟧ = c
       𝒞⟦ B ⇒ ★ ⟧ = d
    𝒞⟦ ★ ⇒ (A → B) ⟧ = ★→★? ; (c → d)     (A ≠ ★, B ≠ ★)
       where
       𝒞⟦ A ⇒ ★ ⟧ = c
       𝒞⟦ ★ ⇒ B ⟧ = d
    𝒞⟦ A ⇒ X ⟧ = X↓
    𝒞⟦ X ⇒ B ⟧ = X↑
    𝒞⟦ (A → B) ⇒ (A′ → B′) ⟧ = c → d
       where
       𝒞⟦ A′ ⇒ A ⟧ = c
       𝒞⟦ B ⇒ B′ ⟧ = d
    𝒞⟦ A ⇒ ∀X.B ⟧ = gen X. c
           where
           𝒞⟦ A ⇒ B ⟧ = c
    𝒞⟦ ∀X.A ⇒ B ⟧ = inst X. c
           where
           𝒞⟦ A ⇒ B ⟧ = c
    𝒞⟦ ∀X.A ⇒ ∀X.B ⟧ = ∀X.c
           where
           𝒞⟦ A ⇒ B ⟧ = c

## Compilation of Terms

    -----------------------
    | 𝒞⟦ Γ ⊢ M : A ⟧ = M′ |
    -----------------------

    𝒞⟦ Γ ⊢ x : A ⟧          = x

    𝒞⟦ Γ ⊢ λx:A.N : A → B ⟧ = λx.N′
       where
       𝒞⟦ Γ,x:A ⊢ N : B ⟧   = N′

    𝒞⟦ Γ ⊢ L M : B⟧         = L′  M′⟨c⟩
       where
       𝒞⟦ Γ ⊢ L : A → B⟧ = L′
       𝒞⟦ Γ ⊢ M : A′ ⟧   = M′
       𝒞⟦ A′ ⇒ A ⟧       = c

    𝒞⟦ Γ ⊢ L M : ★⟧         = L′⟨c⟩  M′⟨d⟩
       where
       𝒞⟦ Γ ⊢ L : ★⟧   = L′
       𝒞⟦ Γ ⊢ M : A ⟧  = M′
       𝒞⟦ ★ ⇒ ★ → ★ ⟧ = c
       𝒞⟦ A ⇒ ★ ⟧      = d

    𝒞⟦ Γ ⊢ L[B] : A[B/X] ⟧ = νX=B. L′[X] ⟨c⟩
       where
       𝒞⟦ Γ ⊢ L : ∀X.A ⟧ = L′
       𝒞⟦ A ⇒ A[B/X] ⟧ = c

    𝒞⟦ Γ ⊢ L[B] : ★ ⟧ = νX=B. L′⟨c⟩[X]
       where
       𝒞⟦ Γ ⊢ L : ★ ⟧ = L′
           𝒞⟦ ★ ⇒ ∀X.★ ⟧ = c
