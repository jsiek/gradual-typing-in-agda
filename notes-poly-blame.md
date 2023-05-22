

# Polymorphic Gradually Typed Lambda Calculus (Surface Language, PGL)

## Syntax

    Types         A, B, C  ::=  X | A → B | ∀X.A | ★
    Terms         L, M, N  ::=  x | λx:A.N | ΛX.M | L M | L[A] | M : A
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

    --------- (FV(A) ⊆ Ψ)     ---------- (FV(A) ⊆ Ψ)
    Ψ ⊢ ★ ~ A                 Ψ ⊢ A ~ ★

    Ψ ⊢ A ~ A′  Ψ ⊢ B ~ B′
    -----------------------
    Ψ ⊢ A → B ~ A′ → B′
    
    Ψ ⊢ A ~ A′
    -----------------
    Ψ ⊢ ∀X.A ~ ∀X.A′

    Ψ,X ⊢ A ~ B
    ------------- (B ≠ ∀Y.C, X ∉ B)
    Ψ ⊢ ∀X.A ~ B

    Ψ,X ⊢ A ~ B
    ------------- (A ≠ ∀Y.C, X ∉ A)
    Ψ ⊢ A ~ ∀X.B

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

    Γ ⊢ M : A′
    --------------- (A′ ~ A)
    Γ ⊢ (M : A) : A
    
## Term Precision



# Polymorphic Cast Calculus (PCC, Internal Language)

## Syntax

    Types         A, B, C  ::=  X | A → B | ∀X.A | ★ | α
    Ground Types  G, H     ::=  ι | ★→★ | α
    Terms         L, M, N  ::=  x | λx.N | ΛX.M | L M | L[α] | να.M
	                         | M⟨c⟩ | blame
    Values        V, W     ::= λx.N | ΛX.M | V⟨gen α.c⟩
    Coercions     c, d     ::= id | G? | G! | α↓ | α↑ | c → d | c ; d
                             | ∀X.c | gen α.c | inst α.c

    Environments  Γ        ::=  ∅ | Γ, x:A | Γ, X | Γ, α=A

## Reductions

    ----------
    | M —→ N |
    ----------

    (λx.N) V              —→  N[V/x]
    (ΛX.M)[β]             —→  M[β/X]
	V⟨gen α.c⟩[β]          —→ V⟨c[β/α]⟩
    V⟨id⟩                  —→  V
    V⟨α↓⟩⟨α↑⟩              —→  V
    V⟨G!⟩⟨G?⟩              —→  V
    V⟨G!⟩⟨H?⟩              —→  blame    (G ≠ H)
    V⟨c → d⟩              —→  λx. (V x⟨c⟩)⟨d⟩
    V⟨inst α.c⟩           —→  να. V[α]⟨c⟩
    V⟨∀X.c⟩               —→  ΛX. V⟨c⟩
	V⟨c ; d⟩              —→ V⟨c⟩⟨d⟩

    ------------------
    | Σ ⊢ M —→ Σ ⊢ N |
    ------------------
    
    M —→ N
    --------------
    Σ ⊢ M —→ Σ ⊢ N

    Σ ⊢ M —→ Σ′ ⊢ N
    ---------------------
    Σ ⊢ F[M] —→ Σ′ ⊢ F[N]

    -------------------------- (β ∉ Σ)
    Σ ⊢ να.N —→  Σ, β ⊢ N[β/α]
    

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
	
    -------------- (α=A ∈ Γ)
    Γ ⊢ α↓ : A ⇒ α

    -------------- (α=A ∈ Γ)
    Γ ⊢ α↑ : α ⇒ A

    Γ ⊢ c : A ⇒ B[α/X]
    ----------------------
    Γ ⊢ gen α.c : A ⇒ ∀X.B

    Γ ⊢ c : A[α/X] ⇒ B
    -----------------------
    Γ ⊢ inst α.c : ∀X.A ⇒ B


## Type System

    -------------
    | Γ ⊢ M : A |
    -------------

    Γ ⊢ M : A   Γ ⊢ c : A ⇒ B
    -------------------------          Cast
    Γ ⊢ M⟨c⟩ : B

    Γ ⊢ L : ∀X.A
    ----------------- (α=B ∈ Γ)        Type application
    Γ ⊢ L[α] : A[α/X]

    Γ, α=A ⊢ N : B
    --------------- (α ∉ B)            Generate fresh type variable
    Γ ⊢ να.N : B

## Configuration Typing

    ---------
    | Γ ⊢ Σ |
    ---------

    ------
    ∅ ⊢ ∅

    -------------
    Γ, α=A ⊢ Σ, α

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
    | 𝒞⟦ A ⇒ B ⟧ = c |
    ------------------
    
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
	
    𝒞⟦ A ⇒ α ⟧ = α↓

    𝒞⟦ α ⇒ B ⟧ = α↑
	
    𝒞⟦ (A → B) ⇒ (A′ → B′) ⟧ = c → d
       where
       𝒞⟦ A′ ⇒ A ⟧ = c
       𝒞⟦ B ⇒ B′ ⟧ = d

    𝒞⟦ A ⇒ A ⟧        = id
    
    𝒞⟦ A ⇒ ∀X.B ⟧ = gen α. c
	   where
	   𝒞⟦ A ⇒ B[α/X] ⟧ = c
	   
    𝒞⟦ ∀X.A ⇒ B ⟧ = inst α. c
	   where
	   𝒞⟦ A[α]X] ⇒ B ⟧ = c
	   
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

    𝒞⟦ Γ ⊢ L M : B⟧         = L′ (N′ M′)
       where
       𝒞⟦ Γ ⊢ L : A → B⟧ = L′
       𝒞⟦ Γ ⊢ M : A′ ⟧   = M′
       𝒞⟦ A ⇒ A′ ⟧       = N′

    𝒞⟦ Γ ⊢ L M : ★⟧         = (N₁ L)′ (N₂ M′)
       where
       𝒞⟦ Γ ⊢ L : ★⟧   = L′
       𝒞⟦ Γ ⊢ M : A ⟧  = M′
       𝒞⟦ ★ ⇒ ★ → ★ ⟧ = N₁
       𝒞⟦ A ⇒ ★ ⟧      = N₂

    𝒞⟦ Γ ⊢ L[B] : A[B/X] ⟧ = να. M′ L′[·]
       where
       𝒞⟦ Γ ⊢ L : ∀X.A ⟧ = L′
       𝒞⟦ A[α/X] ⇒ A[B/X] ⟧ = M′

    𝒞⟦ Γ ⊢ L[B] : ★ ⟧ = να. (N L′)[α]
       where
       𝒞⟦ Γ ⊢ L : ★ ⟧ = L′
	   𝒞⟦ ★ ⇒ ∀X.★ ⟧ = N
