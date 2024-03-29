Surface Language
    
    Type Variables X,Y,Z
    Types          A,B    ::=  X | ι | A→B | ∀X.B | ★
    Term Variables x,y,z
    Terms          L,M,N  ::=  x | λx:A.N | L M | ΛX.V | L[A]
    Values        V,W    ::=  x | λx:A.N | ΛX.V

Precision

    Constraint     C ::=  A ⊑ B
    Contraint Set  𝒞

    -------------
    | 𝒞 ⊢ A ⊑ B |
    -------------

    X ⊑ Y ∈ 𝒞
    ----------
    𝒞 ⊢ X ⊑ Y

    ★ ⊑ Y ∈ 𝒞
    ---------- (Y ≠ ∀Z.B)
    𝒞 ⊢ ★ ⊑ Y
    
    𝒞, X ⊑ Y ⊢ A ⊑ B
    -----------------
    𝒞 ⊢ ∀X.A ⊑ ∀Y.B

    𝒞, ★ ⊑ Y ⊢ A ⊑ B
    ------------------ (Y ∈ B)
    𝒞 ⊢ A ⊑ ∀Y.B

    ---------
    𝒞 ⊢ ι ⊑ ι

    𝒞 ⊢ A ⊑ A′   𝒞 ⊢ B ⊑ B′
    ------------------------
    𝒞 ⊢ A→B ⊑ A′→B′

    ----------
    𝒞 ⊢ ★ ⊑ ι

    𝒞 ⊢ ★ ⊑ A′   𝒞 ⊢ ★ ⊑ B′
    ------------------------
    𝒞 ⊢ ★ ⊑ A′→B′

Consistency

    Constraint     C ::=  A ~ B
    Contraint Set  𝒞

    -------------
    | 𝒞 ⊢ A ~ B |
    -------------

    X ~ Y ∈ 𝒞
    ----------
    𝒞 ⊢ X ~ Y

    ★ ~ Y ∈ 𝒞
    ----------
    𝒞 ⊢ ★ ~ Y

    X ~ ★ ∈ 𝒞
    ----------
    𝒞 ⊢ X ~ ★

    𝒞, X ~ Y ⊢ A ~ B
    ----------------- (X ∉ 𝒞, Y ∉ 𝒞)
    𝒞 ⊢ ∀X.A ~ ∀Y.B

    𝒞, ★ ~ Y ⊢ A ~ B
    ----------------- (Y ∉ 𝒞, Y ∈ B)
    𝒞 ⊢ A ~ ∀Y.B

    𝒞, X ~ ★ ⊢ A ~ B
    ----------------- (X ∉ 𝒞, X ∈ A)
    𝒞 ⊢ ∀X.A ~ B

    ---------
    𝒞 ⊢ ι ~ ι

    𝒞 ⊢ A ~ A′   𝒞 ⊢ B ~ B′
    ------------------------
    𝒞 ⊢ A→B ~ A′→B′

    ----------
    𝒞 ⊢ ★ ~ ι

    ----------
    𝒞 ⊢ ι ~ ★

    𝒞 ⊢ ★ ~ A′   𝒞 ⊢ ★ ~ B′
    ------------------------
    𝒞 ⊢ ★ ~ A′→B′

    𝒞 ⊢ A ~ ★   𝒞 ⊢ B ~ ★
    -----------------------
    𝒞 ⊢ A→B ~ ★

Type System

    Type Environments   Γ      ::=  ∅ | Γ, x:A | Γ, X | Γ, α=A

    -------------
    | Γ ⊢ M : A |
    -------------
	
    x:A ∈ Γ
    ----------
    Γ ⊢ x : A

    Γ, x:A ⊢ N : B
    ------------------
    Γ ⊢ λx:A.N : A → B

    Γ ⊢ L : A → B    Γ ⊢ M : A′   A ~ A′
    ------------------------------------
    Γ ⊢ L M : B

    Γ ⊢ L : ★   Γ ⊢ M : A
    ----------------------
    Γ ⊢ L M : ★

    Γ, X ⊢ V : B
    ---------------
    Γ ⊢ ΛX.V : ∀X.B

    Γ ⊢ L : ∀X.B    Γ ⊢ A
    ----------------------
    Γ ⊢ L[A] : B[A/X]

    Γ ⊢ L : ★    Γ ⊢ A
    -------------------
    Γ ⊢ L[A] : ★


Polymorphic Cast Calculus

    Terms             ::= x | λx.N | L M | ΛX.V | L[α] | M!G | M?G
	                    | να=A.M | M↓α | M↑α
	Ground Types  G,H ::= ι | ★→★

Compilation of Casts

    ----------------
    | ⟨A ⇒ B⟩ = M′ |  (pre: A ~ B)
    ----------------
    
    ⟨G ⇒ ★⟩ = (λx. x!G)
    ⟨★ ⇒ H⟩ = (λx. x?H)
    ⟨A ⇒ ★⟩ = (λx. (⟨A ⇒ G⟩ x) !G)    (A not ground, not poly)
    ⟨★ ⇒ B⟩ = (λx. ⟨H ⇒ B⟩ (x ?H))    (B not ground, not poly)
	⟨A→B ⇒ A′→B′⟩ = (λf.λx. ⟨B ⇒ B′⟩ (f (⟨A′ ⇒ A⟩ x))    (f:A→B, x:A′)
	⟨∀X.A ⇒ ∀X.B⟩ = λp. ΛX. να=X. ⟨A[α/X] ⇒ B[α/X]⟩ p[α] (p:∀X.A)
	
    ⟨∀X.A ⇒ B⟩ = λp. ⟨A[★/X] ⇒ B⟩ p[★]
	⟨A ⇒ ∀Y.B⟩ = 


Compilation of Terms to Cast Calculus

    ------------------
    | Γ ⊢ M ↝ M′ : A |
    ------------------

    x:A ∈ Γ
    --------------
    Γ ⊢ x ↝ x : A

    Γ, x:A ⊢ N ↝ N′ : B
    ---------------------------
    Γ ⊢ λx:A.N ↝ λx.N′ : A → B

    Γ ⊢ L ↝ L′ : A → B    Γ ⊢ M ↝ M′ : A′   A′ ~ A
    -----------------------------------------------
    Γ ⊢ L M ↝ L′ M⟨A′⇒A⟩ : B

    Γ ⊢ L ↝ L′ : ★   Γ ⊢ M ↝ M′ : A′
    -----------------------------------
    Γ ⊢ L M ↝ L′⟨★⇒★→★⟩ M′⟨A′⇒★⟩ : ★

    Γ, X ⊢ V ↝ V′ : B
    ------------------------
    Γ ⊢ ΛX.V ↝ ΛX.V′ : ∀X.B

    Γ ⊢ L ↝ L′ : ∀X.B    Γ ⊢ A
    ---------------------------
    Γ ⊢ L[A] ↝ L′[A] : B[A/X]

    Γ ⊢ L ↝ L′ : ★    Γ ⊢ A
    ------------------------------
    Γ ⊢ L[A] ↝ L′⟨★⇒∀X.★⟩[A] : ★
   
