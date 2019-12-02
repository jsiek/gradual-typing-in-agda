
%.agdai: %.agda
	/usr/local/bin/agda  $<

AGDA = Labels.agda Types.agda Variables.agda \
	GTLC.agda GTLC2CC.agda \
	PreCastStructure.agda CastStructure.agda \
	ParamCastCalculus.agda ParamCastReduction.agda EfficientParamCasts.agda \
	GroundCast.agda GroundCoercions.agda EfficientGroundCoercions.agda \
	SimpleCast.agda SimpleFunCast.agda SimpleCoercions.agda \
	LazyCast.agda LazyCoercions.agda \
	HyperCoercions.agda AGT.agda 

AGDAI = $(AGDA:%.agda=%.agdai)

all: ${AGDA} ${AGDAI}

clean:
	rm -f *.agdai *~
