# gradual-typing-in-agda
Formalizations of Gradually Typed Languages in Agda

Inventory
* [Labels.agda](./Labels.agda): Definition of blame labels.
* [Types.agda](./Types.agda): Definition of gradual types and operators on them,
    such as precision, consistency, etc.
* [Variables.agda](./Variables.agda): Definition of variables as de Bruijn indices.
* [GTLC.agda](./GTLC.agda): Syntax and type system of the Gradually Typed Lambda Calculus
     with pairs and sums.
* [GTLC2CC.agda](./GTLC2CC.agda): Compilation of the GTLC to the Parameterized Cast Calculus.
* [ParamCastCalculus.agda](./ParamCastCalculus.agda): Syntax and type system (intrinsically typed)
    for the Parameterized Cast Calculus. Also includes the definition of substitution.
* [ParamCastReduction.agda](./ParamCastReduction.agda): Reduction rules and proof of type safety 
    for the Parameterized Cast Calculus.
* [GroundCast.agda](./GroundCast.agda): Type safety of λB (Siek, Thiemann, Wadler 2015).
* [GroundCoercion.agda](./GroundCast.agda): Type safety of λC (Siek, Thiemann, Wadler 2015).
* [SimpleCast.agda](./SimpleCast.agda): Type safety of the cast calculus of
    Siek and Taha (2006). (Called "partially-eager D" by Siek, Garcia, and Taha 2009).
* [SimpleFunCast.agda](./SimpleFunCast.agda): The same as above but 
    casts between function types are values.
* [SimpleCoercions.agda](./SimpleCoercions.agda): Type safety for the cast calculus of 
    Siek and Taha (2006) again, but the calculus is expressed with coercions.
* [LazyCast.agda](./LazyCast.agda): Type safety for the "lazy D" calculus (Siek, Garcia, and Taha 2009).
* [LazyCoercions.agda](./LazyCoercions.agda): Type safety for the "lazy D" calculus,
    with casts represented as coercions.
* [EfficientParamCasts.agda](./EfficientParamCasts.agda): A space-efficient parameterized
    cast calculus. This module requires, in addition, a compose function for casts.
* [EfficientGroundCoercions.agda](./EfficientGroundCoercions.agda): 
   Type safety of λS (Siek, Thiemann, Wadler 2015).
