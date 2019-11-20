open import CastStructure
import ParamCastCalculus
import ParamCastAux
import ParamCastReduction

module MakeCastCalculus (C : CastStruct) where
  open CastStruct C
  open ParamCastCalculus Cast public
  open ParamCastAux precast public
  open ParamCastReduction C public


