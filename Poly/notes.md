================================================================================

Local Type Inference for Impredicative Polymorphism

Not so sure this makes sense... 

The thought was to replace subtyping with precision and consistency in
the setting of a statically but partially typed polymorphic calculus.

# Syntax

    A,B,C,D,E ::= α | A → B | Aₒ × ⋯ × Aₖ | ∀α.A
    L,M,N     ::= x | λx.N | L M | M : A | (Mₒ, ..., Mₖ) | M[n]

# Precision

    -------------
    | Ψ ⊢ A ⊑ B | 
    -------------

    ---------- (α ∈ Ψ)
    Ψ ⊢ α ⊑ α

    Ψ ⊢ A ⊑ C  Ψ ⊢ B ⊑ D
    ---------------------
    Ψ ⊢ A → B ⊑ C → D

    all k ∈ 0...n, Ψ ⊢ Aₖ ⊑ Bₖ
    -------------------------------
    Ψ ⊢ Aₒ × ⋯ × Aₙ ⊑ Bₒ × ⋯ × Bₙ

    Ψ, α ⊢ A ⊑ B
    -----------------
    Ψ ⊢ ∀α.A ⊑ ∀α. B

    Ψ ⊢ A ⊑ B[α:=C]
    ----------------
    Ψ ⊢ A ⊑ ∀α. B

# Consistency

    ∅ ⊢ A ⊑ C   ∅ ⊢ B ⊑ C
    ----------------------
            A ∼ B

# Type System

    Γ ⊢ L : ∀αₒ.⋯∀αₙ.A → C   Γ ⊢ M : B
	A[αₒ:=Dₒ]⋯[αₙ:=Dₙ] ∼ B
	∀Eₒ⋯Eₙ. A[αₒ:=Eₒ]⋯[αₙ:=Eₙ] ∼ B implies (for k∈0...n, Eₖ ⊑ Dₖ)
	---------------------------------------------------------------
    Γ ⊢ L M : C[αₒ:=Dₒ]⋯[αₙ:=Dₙ]

# Constraint Generation

    ------------------
    | Ψ ⊢ A ∼ B ⇒ 𝒞 |
	------------------

    α ∉ Ψ
    ---------------
    Ψ ⊢ α ~ α ⇒ ∅

    α ∈ Ψ
    ----------------------
    Ψ ⊢ α ~ B ⇒ { α ~ B }

    Ψ ⊢ A₁ ~ B₁ ⇒ 𝒞₁   Ψ ⊢ A₂ ~ B₂ ⇒ 𝒞₂
    -------------------------------------
    Ψ ⊢ A₁ → A₂ ~ B₁ → B₂ ⇒ 𝒞₁ ∪ 𝒞₂


    Ψ ⊢ ∀α.A ~ ∀α.B


================================================================================

Consistency

        ------------
        id_A : A ~ A

        p : A ~ G
        ----------------
        tag_G(p) : A ~ ★

        p : A ~ G
        ------------------
        untag_G(p) : ★ ~ A

        p : A ~ A′    q : B ~ B′
        ------------------------
        p→q : A→B ~ A′→B′

        p[X] : A[X] ~ B[X]
        -----------------------------
        ∀X.p[X] : ∀X.A[X] ~ ∀X.B[X]
		
        p[α] : A[α] ~ B
        ------------------------- (α ∉ B, ★ ∈ B)
        νᴸα.p[α] : ∀X.A[X] ~ B

        p[α] : B ~ A[α]
        ------------------------- (α ∉ B, ★ ∈ B)
        νᴿα.p[α] : B ~ ∀X.A[X]


Lemma

  If A ~ B then C ⊑ A and C ⊑ B for some C.
  If C ⊑ A and C ⊑ B then A ~ B.




   Γ ⊢ L : ★
   Γ ⊢ A
   ------------
   Γ ⊢ L A : ★

   Γ ⊢ L ↝ L′ : ★
   Γ ⊢ A
   -------------------------------
   Γ ⊢ L A ↝   L′⟨★ ⇒ ∀X.★⟩ A : ★
   

   Γ ⊢ L A ↝   L′⟨να.id_★⟩ A : ★
      where  να.id_★ : ★ ⊑ ∀X.★       (except that α ∉ ★[α])

   example:  int → int ⇒ ∀X.int → int  (Igarashi paper)
   Peter: should we use the side condition of Igarashi et al.?

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
   
