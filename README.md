# gradual-typing-in-agda
Formalizations of Gradually Typed Languages in Agda

Inventory
* [Labels.agda](./Labels.agda): Definition of blame labels.

* [Types.agda](./Types.agda): Definition of gradual types and
   operators on them, such as precision, consistency, etc.

* [Variables.agda](./Variables.agda): Definition of variables as de
   Bruijn indices.

* [GTLC.agda](./GTLC.agda): Syntax and type system of the Gradually
   Typed Lambda Calculus with pairs and sums.

* [GTLC-materialize.agda](./GTLC-materialize.agda): A version of the
   GTLC that uses the materialize rule (subsumption with precision)
   instead of using the consistency relation.
   
* [PreCastStructure.agda](./PreCastStructure.agda): A record
   definition `PreCastStruct` that abstracts the representation of a cast.
   It includes a type constructor `Cast` for casts, operations on casts
   (e.g. `dom` and `cod`) and categories of casts (`Active`, `Inert`,
   `Cross`). This record definition does not depend on the
   definition of terms.

* [CastStructure.agda](./CastStructure.agda): contains two
   record definitions: the `CastStruct` record and the
   `EfficientCastStruct`. The `CastStruct` record extends
   `PreCastStruct` with an `applyCast` operation that applies
   an active cast to a value to produce a term.
   The `EfficientCastStruct` record also extends 
   `PreCastStruct` with an `applyCast` operation,
   but also includes a `compose` operation for compressing
   two casts into a single cast.

* [ParamCastCalculus.agda](./ParamCastCalculus.agda): Syntax and type
   system (it is intrinsically typed) for the Parameterized Cast
   Calculus.It is parameterized over a type constructor `Cast`.  This
   includes the definition of substitution.
   
* [ParamCastAux.agda](./ParamCastAux.agda): defines `Value`, `Frame`,
   `plug`, the wrapper reductions based on the idea of eta expansion,
   and proves a canonical forms lemma for type dynamic.
   This module is parameterized over a `PreCastStruct`.
  
* [ParamCastReduction.agda](./ParamCastReduction.agda): Reduction
   rules and proof of type safety for the Parameterized Cast
   Calculus, parameterized over a `CastStruct`.
   
* [EfficientParamCastAux.agda](./EfficientParamCastAux.agda): defines
   `SimpleValue`, `Value`, and proves a canonical forms lemma for type
   dynamic. This module is parameterized over `PreCastStruct`.

* [EfficientParamCasts.agda](./EfficientParamCasts.agda): A
   space-efficient reduction relation for the parameterized cast
   calculus. This module requires a compose function for casts, so it
   is parameterized over `EfficientCastStruct`.  This module includes
   a proof of progress.

* [PreserveHeight.agda](./PreserveHeight.agda): Proves that the height
   of the casts in a program do not increase during reduction.  Their
   size is bounded by their height, so this result contributes to the
   proof of space efficiency.

* [SpaceEfficient.agda](./SpaceEfficient.agda): A proof that the
   space-efficient reduction relation really is space efficient.  That
   is, the casts that can accumulate during reduction only multiply
   the size of the program by a constant.

* [GTLC2CC.agda](./GTLC2CC.agda): Compilation of the GTLC to the
   Parameterized Cast Calculus.  The compilation is type preserving.
   
* [GroundCast.agda](./GroundCast.agda): Type safety of λB (Siek,
   Thiemann, Wadler 2015). ("lazy UD" of Siek, Garcia, and Taha 2009)
   
* [GroundCoercion.agda](./GroundCast.agda): Type safety of λC (Siek,
   Thiemann, Wadler 2015). ("lazy UD" of Siek, Garcia, and Taha 2009)
   
* [EfficientGroundCoercions.agda](./EfficientGroundCoercions.agda):
   Type safety of λS (Siek, Thiemann, Wadler 2015).
   ("lazy UD" of Siek, Garcia, and Taha 2009)
   
* [SimpleCast.agda](./SimpleCast.agda): Type safety of the cast
   calculus of Siek and Taha (2006). (Called "partially-eager D" by
   Siek, Garcia, and Taha 2009).
   
* [SimpleFunCast.agda](./SimpleFunCast.agda): The same as above but
   casts between function types are values.
   
* [SimpleCoercions.agda](./SimpleCoercions.agda): Type safety for the
   cast calculus of Siek and Taha (2006) again, but the calculus is
   expressed with coercions.
   
* [LazyCast.agda](./LazyCast.agda): Type safety for the "lazy D"
   calculus (Siek, Garcia, and Taha 2009).
   
* [LazyCoercions.agda](./LazyCoercions.agda): Type safety for the
   "lazy D" calculus, with casts represented as coercions.
   
* [AGT.agda](./AGT.agda): A space-efficient version of the GTLC
   inspired by Abstracting Gradual Typing (Garcia, Clark, and Tanter
   2016).  This is also closely related to the threesomes of Siek and
   Wadler (2011).
   
* [AbstractMachine.agda](./AbstractMachine.agda): A space-efficient
   abstract machine. It's a variant of the SECD machine with optimized
   tail calls. It's parameterized with respect to casts.
   
* [GroundMachine.agda](./GroundMachine.agda): The abstract machine
   instantiated with the coercions from λS. ("lazy UD")
   
* [HyperCoercions](./HyperCoercions.agda): A alternative to
   λS that optimizes the coercion representation by removing
   indirections. ("lazy UD")
   
* [EquivCast](./EquivCast.agda): Proof of equivalence (simulation)
   between two instances of the Parameterized Cast Calculus.
   
* [EquivLamBLamC](./EquivLamBLamC.agda): Proof that 
   λC simulates λB, by insantiating the above EquivCast module.
   
* [ForgetfulCast](./ForgetfulCast.agda): Inspired by Greenberg's
   forgetful contracts. (UNDER CONSTRUCTION)

* [Subtyping](./Subtyping.agda): The module defines several subtyping
   relations used in the blame-subtyping theorem. They are the same
   relations as the ones in the _Exploring the Design Space_ paper.

* [ParamCastSubtyping](./ParamCastSubtyping.agda): The module defines
   what it means for a term `M` to contain only safe casts with the 
   label `ℓ` (`CastsAllSafe`). We show that the data type `CastsAllSafe`
   is preserved during reduction.

* [ParamBlameSubtyping](./ParamBlameSubtyping.agda): A formalized
   proof of the blame-subtyping theorem. The theorem statement says
   that "if every cast labeled by `ℓ` is safe cast (respects subtyping,
   or a recursive safety definition if is coercion-based) in a term `M`
   then `M` cannot reduce to `blame ℓ`". It is slightly different,
   but equivalent to, the theorem statement in the _Refined Criteria_
   paper.
