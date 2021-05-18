
%.agdai: %.agda
	/usr/bin/env agda  $<

AGDA = Labels.agda Types.agda Variables.agda \
	GTLC.agda GTLC2CC.agda \
	PreCastStructure.agda CastStructure.agda \
	ParamCastCalculus.agda ParamCastReduction.agda ParamCastDeterministic.agda \
	Subtyping.agda CastStructureWithBlameSafety.agda ParamCastSubtyping.agda ParamBlameSubtyping.agda \
	ParamCCPrecision.agda ParamGradualGuaranteeAux.agda ParamGradualGuaranteeSim.agda ParamGradualGuarantee.agda \
	GroundCast.agda GroundCastBlame.agda GroundCastGG.agda \
	GroundInertX.agda GroundInertXBlame.agda GroundInertXGG.agda \
	GroundCoercions.agda GroundCoercionsBlame.agda \
	SimpleCast.agda SimpleCastBlame.agda \
	SimpleFunCast.agda SimpleFunCastBlame.agda \
	SimpleCoercions.agda \
	LazyCast.agda LazyCastBlame.agda \
	LazyCoercions.agda LazyCoercionsBlame.agda \
	EfficientParamCasts.agda SpaceEfficient.agda PreserveHeight.agda \
	EfficientGroundCoercions.agda \
	HyperCoercions.agda 

AGDAI = $(AGDA:%.agda=%.agdai)

all: ${AGDA} ${AGDAI}

clean:
	rm -f *.agdai *~
