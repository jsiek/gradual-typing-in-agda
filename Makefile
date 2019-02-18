
%.agdai: %.agda
	agda  $<

AGDA = Labels.agda Types.agda Variables.agda \
	GTLC.agda GTLC2CC.agda \
	ParamCastCalculus.agda ParamCastReduction.agda \
	GroundCast.agda GroundCoercions.agda \
	SimpleCast.agda SimpleFunCast.agda SimpleCoercions.agda \
	LazyCast.agda LazyCoercions.agda 

AGDAI = $(AGDA:%.agda=%.agdai)

all: ${AGDA} ${AGDAI}

clean:
	rm -f *.agdai *~
