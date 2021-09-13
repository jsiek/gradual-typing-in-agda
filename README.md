# Gradual Typing in Agda


### About

Formalizations of Gradually Typed Languages in Agda.

The current release is `v1.0`.


### Agda Version

The current release `v1.0` of this project has been checked by Agda
version `2.6.2` with the Agda standard library version `1.7`.


### Prerequisites/Dependencies

This project depends on the Abstract Binding Trees library,
specifically release `v2.1`.

https://github.com/jsiek/abstract-binding-trees

After cloning that repository, make sure to add the path to `abt.agda-lib`
to the `libraries` file in your `.agda` directory and to add `abt` to 
the `defaults` file.


### Correspondence with article in Journal of Function Programming

The article "Parameterized Cast Caculi and Reusable Meta-theory for
Gradually Typed Lambda Caculi" describes most of this Agda
development. Here we provide a mapping from sections in that article
to the files in this project.

1. Introduction - no corresponding Agda files
2. Gradually Typed Lambda Calculus: [GTLC](./GTLC.agda)
3. Parameterized Cast Calculus
    1. [PreCastStructure](./PreCastStructure.agda)
	2. [ParamCastAux](./ParamCastAux.agda)
	3. [ParamCastAux](./ParamCastAux.agda)
	4. [CastStructure](./CastStructure.agda)
	5. [ParamCastCalculusOrig](./ParamCastCalculusOrig.agda)
	6. [ParamCastReductionOrig](./ParamCastReductionOrig.agda)
	7. [ParamCastReductionOrig](./ParamCastReductionOrig.agda)
	8. [ParamCastCalculus](./ParamCastCalculus.agda), 
	   [ParamCastReduction](./ParamCastReduction.agda)
    9. [PreCastStructureWithBlameSafety](./PreCastStructureWithBlameSafety)
	   [CastStructureWithBlameSafety](./CastStructureWithBlameSafety),
	   [Subtyping](./Subtyping.agda),
	   [ParamCastSubtyping](./ParamCastSubtyping.agda),
	   and [ParamBlameSubtyping](./ParamBlameSubtyping.agda).
	10. [PreCastStructureWithPrecision](./PreCastStructureWithPrecision.agda),
	    [CastStructureWithPrecision](./CastStructureWithPrecision.agda),
        [ParamCCPrecision](./ParamCCPrecision.agda),
		[ParamGradualGuaranteeAux](./ParamGradualGuaranteeAux.agda), 
		[ParamGradualGuaranteeSim](./ParamGradualGuaranteeSim.agda), and
		[ParamGradualGuarantee](./ParamGradualGuarantee.agda).
4. Compilation of GTLC to CC: [GTLC2CCOrig](./GTLC2CCOrig.agda)
5. A Half-Dozen Cast Calculi
    1. EDA: [SimpleCast](./SimpleCast.agda)
	2. EDI: [SimpleFunCast](./SimpleFunCast.agda)
	3. λB: [GroundCast](./GroundCast.agda), [GroundCastGG](./GroundCastGG.agda)
	4. EDC: [SimpleCoercions](./SimpleCoercions.agda)
	5. LDC: [LazyCoercions](./LazyCoercions.agda)
	6. λC: [GroundCoercion](./GroundCoercion.agda)
6. Space-Efficient Parameterized Cast Caclulus
	1. [EfficientParamCastAux](./EfficientParamCastAux.agda)
	2. [CastStructure](./CastStructure.agda) (`ComposableCasts` is named `EfficientCastStruct`)
	3. [EfficientParamCasts](./EfficientParamCasts.agda)
	4. [EfficientParamCasts](./EfficientParamCasts.agda)
	5. [PreserveHeight](./PreserveHeight.agda) and [SpaceEfficient](./SpaceEfficient.agda)
7. Space-Efficient Cast Calculi
	1. [EfficientGroundCoercions](./EfficientGroundCoercions.agda)
	2. [HyperCoercions](./HyperCoercions.agda)


### Inventory

* [Labels](./Labels.agda): Definition of blame labels.

* [PrimitiveTypes](./PrimitiveTypes.agda) and [Types](./Types.agda):
   Definition of gradual types and operators on them, such as
   precision, consistency, etc.

* [Variables](./Variables.agda): Definition of variables as de
   Bruijn indices.

* [GTLC](./GTLC.agda): Syntax and type system of the Gradually
   Typed Lambda Calculus with pairs and sums.

* [GTLC-materialize](./GTLC-materialize.agda): A version of the
   GTLC that uses the materialize rule (subsumption with precision)
   instead of using the consistency relation.

* [PreCastStructure](./PreCastStructure.agda): A record
   definition `PreCastStruct` that abstracts the representation of a cast.
   It includes a type constructor `Cast` for casts, operations on casts
   (e.g. `dom` and `cod`) and categories of casts (`Active`, `Inert`,
   `Cross`). This record definition does not depend on the
   definition of terms. Two records extend `PreCastStruct` with their
   respective definitions and lemmas:

    - [PreCastStructureWithBlameSafety](./PreCastStructureWithBlameSafety.agda):
       Contains the definition of a cast being blame safe and its related lemmas.
       Used in the blame theorem proof.
    - [PreCastStructureWithPrecision](./PreCastStructureWithPrecision.agda):
       Contains precision relations between (inert) casts and their related lemmas.
       Used in the gradual guarantee proof.

* [CastStructure](./CastStructure.agda): contains two
   record definitions: the `CastStruct` record and the
   `EfficientCastStruct`. The `CastStruct` record extends
   `PreCastStruct` with an `applyCast` operation that applies
   an active cast to a value to produce a term.
   The `EfficientCastStruct` record also extends
   `PreCastStruct` with an `applyCast` operation,
   but also includes a `compose` operation for compressing
   two casts into a single cast. Two records extend `CastStruct` with their
   respective lemmas:

    - [CastStructureWithBlameSafety](./CastStructureWithBlameSafety.agda):
       Contains a preservation lemma about `CastsAllSafe` .
    - [CastStructureWithPrecision](./CastStructureWithPrecision.agda):
        Contains various simulation lemmas between less precise and more precise
        terms.

* We maintain two variants of the parameterized cast calculus (CC):

    - [ParamCastCalculusOrig](./ParamCastCalculusOrig.agda): Syntax and type
       system (it is intrinsically typed) for the Parameterized Cast
       Calculus. It is parameterized over a type constructor `Cast`. This
       includes the definition of substitution.
    - [ParamCastCalculus](./ParamCastCalculus.agda): This is mostly
       the same as the version above, except it has a separate
       term constructor for inert cast ("wrap"). This is used when defining
       the precision relation and proving the gradual guarantee.

* [ParamCastAux](./ParamCastAux): defines `Value`, `Frame`,
   `plug`, the wrapper reductions based on the idea of eta expansion,
   and proves a canonical forms lemma for type dynamic.
   This module is parameterized over a `PreCastStruct`.

* [ParamCastReductionOrig](./ParamCastReductionOrig.agda): Reduction
   rules and proof of type safety for the first version of hte
   Parameterized Cast Calculus, parameterized over a `CastStruct`.

* [ParamCastReduction](./ParamCastReduction.agda): Reduction rules and
   proof of type safety for the second version of hte Parameterized
   Cast Calculus, parameterized over a `CastStruct`.

* [ParamCastDeterministic](./ParamCastDeterministic.agda):
   A proof that reduction is deterministic.

* [EfficientParamCastAux](./EfficientParamCastAux.agda): defines
   `SimpleValue`, `Value`, and proves a canonical forms lemma for type
   dynamic. This module is parameterized over `PreCastStruct`.

* [EfficientParamCasts](./EfficientParamCasts.agda): A
   space-efficient reduction relation for the parameterized cast
   calculus. This module requires a compose function for casts, so it
   is parameterized over `EfficientCastStruct`.  This module includes
   a proof of progress.

*  **Compilation of the GTLC** to the corresponding variant of the
   Parameterized Cast Calculus (CC). The compilation is type preserving.
   
    - [GTLC2CCOrig](./GTLC2CCOrig.agda): From GTLC to `ParamCastCalculusOrig`.
    - [GTLC2CC](./GTLC2CC.agda): From GTLC to `ParamCastCalculus`.

* **Space-efficiency theorem:**

    - [PreserveHeight](./PreserveHeight.agda): Proves that the height
       of the casts in a program do not increase during reduction.  Their
       size is bounded by their height, so this result contributes to the
       proof of space efficiency.

    - [SpaceEfficient](./SpaceEfficient.agda): A proof that the
       space-efficient reduction relation really is space efficient.  That
       is, the casts that can accumulate during reduction only multiply
       the size of the program by a constant.

* **Blame-subtyping theorem:**

    - [Subtyping](./Subtyping.agda): The module defines several subtyping
      relations used in the blame-subtyping theorem. They are the same
      relations as the ones in the _Exploring the Design Space_ paper.
    - [ParamCastSubtyping](./ParamCastSubtyping.agda): The module defines
       what it means for a term `M` to contain only safe casts with the
       label `ℓ` (`CastsAllSafe`). We show that the data type `CastsAllSafe`
       is preserved during reduction.
    - [ParamBlameSubtyping](./ParamBlameSubtyping.agda): A formalized
       proof of the blame-subtyping theorem. The theorem statement says
       that "if every cast labeled by `ℓ` is safe cast (respects subtyping,
       or a recursive safety definition if is coercion-based) in a term `M`
       then `M` cannot reduce to `blame ℓ`". It is slightly different,
       but equivalent to, the theorem statement in the _Refined Criteria_
       paper (Siek, Vitousek, Cimini, and Boyland 2015).

* **The gradual guarantee:** We define this theorem as a simulation between 
   less precise and more precise terms.

    - [ParamCCPrecision](./ParamCCPrecision.agda): 
	   The definition of precision for the Parameterized Cast Calculus.
    - [ParamGradualGuaranteeAux](./ParamGradualGuaranteeAux.agda):
       This module is parameterized by `PreCastStructWithPrecision` and 
       contains inversion lemmas about less precise and more precise values,
       with inert casts wrapped around one or both sides.
    - [ParamGradualGuaranteeSim](./ParamGradualGuaranteeSim.agda):
       This module is parameterized by `CastStructWithPrecision`.
       It contains multiple simulation lemmas and a `catchup` lemma:
       the less precise side can catch up with a more precise value by 
       reducing to a value that is less precise.
    - [ParamGradualGuarantee](./ParamGradualGuarantee.agda):
       This module is also parameterized by `CastStructWithPrecision`.
       It contains the main theorem statement and proof of `gradual-guarantee`.

* [GroundCast](./GroundCast.agda): Type safety of λB (Siek,
   Thiemann, Wadler 2015). ("lazy UD" of Siek, Garcia, and Taha 2009)

* [GroundInertX](./GroundInertX.agda): The cast representation in
   _Refined Criteria_ (Siek, Vitousek, Cimini, and Boyland 2015).
   ("lazy UD" with inert cross cast)

* [GroundCoercion](./GroundCoercion.agda): Type safety of λC (Siek,
   Thiemann, Wadler 2015). ("lazy UD" of Siek, Garcia, and Taha 2009)

* [EfficientGroundCoercions](./EfficientGroundCoercions.agda):
   Type safety of λS (Siek, Thiemann, Wadler 2015).
   ("lazy UD" of Siek, Garcia, and Taha 2009)

* [HyperCoercions](./HyperCoercions.agda): A alternative to
   λS that optimizes the coercion representation by removing
   indirections. ("lazy UD")

* [SimpleCast](./SimpleCast.agda): Type safety of the cast
   calculus of Siek and Taha (2006). (Called "partially-eager D" by
   Siek, Garcia, and Taha 2009).

* [SimpleFunCast](./SimpleFunCast.agda): The same as above but
   casts between function types are values.

* [SimpleCoercions](./SimpleCoercions.agda): Type safety for the
   cast calculus of Siek and Taha (2006) again, but the calculus is
   expressed with coercions.

* [LazyCast](./LazyCast.agda): Type safety for the "lazy D"
   calculus (Siek, Garcia, and Taha 2009).

* [LazyCoercions](./LazyCoercions.agda): Type safety for the
   "lazy D" calculus, with casts represented as coercions.

* [AGT](./AGT.agda): A space-efficient version of the GTLC
   inspired by Abstracting Gradual Typing (Garcia, Clark, and Tanter
   2016).  This is also closely related to the threesomes of Siek and
   Wadler (2011).

* [AbstractMachine](./AbstractMachine.agda): A space-efficient
   abstract machine. It's a variant of the SECD machine with optimized
   tail calls. It's parameterized with respect to casts.

* [GroundMachine](./GroundMachine.agda): The abstract machine
   instantiated with the coercions from λS. ("lazy UD")

* [EquivCast](./EquivCast.agda): Proof of equivalence (simulation)
   between two instances of the Parameterized Cast Calculus.

* [EquivLamBLamC](./EquivLamBLamC.agda): Proof that
   λC simulates λB, by insantiating the above EquivCast module.

* [ForgetfulCast](./ForgetfulCast.agda): Inspired by Greenberg's
   forgetful contracts. ( 🚧 UNDER CONSTRUCTION 🚧 )
