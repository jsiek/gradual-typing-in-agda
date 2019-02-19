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
* [GroundCast.agda](./GroundCast.agda): Definition of λB (Siek, Thiemann, Wadler 2015).
* [GroundCoercion.agda](./GroundCast.agda): Definition of λC (Siek, Thiemann, Wadler 2015).
* [SimpleCast.agda](./SimpleCast.agda): The cast calculus of
    Siek and Taha (2006). (Called "partially-eager D" by Siek, Garcia, and Taha 2009).
* [SimpleFunCast.agda](./SimpleFunCast.agda): The same as above but 
    casts between function types are values.
* [SimpleCoercions.agda](./SimpleCoercions.agda): The cast calculus of Siek and Taha (2006) again,
    but expressed with coercions.
* [LazyCast.agda](./LazyCast.agda): The "lazy D" calculus (Siek, Garcia, and Taha 2009).
* [LazyCoercions.agda](./LazyCoercions.agda): The "lazy D" calculus expressed with
    coercions.
* [EfficientParamCasts.agda](./EfficientParamCasts.agda): A space-efficient parameterized
    cast calculus. This module requires, in addition, a compose function for casts.

