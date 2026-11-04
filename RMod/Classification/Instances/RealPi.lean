import RMod.Classification.Abstract.Pi
import RMod.Definitions.RealRModData
import Superfusion.RMod.FromRawDCT.RealPairing

/-!
# The coefficient-one parity object of the actual real regular-module model

This concrete constructor is deliberately outside the abstract branch. Its
underlying category is exactly the already constructed `realRModData`.
-/

set_option autoImplicit false

namespace RMod.Classification

open Superfusion.RMod.FromRawDCT

/-- The singleton `(0,1)` and the coefficient-one odd maps in both directions. -/
def realPi : PiData RMod.realRModData where
  object := Obj.singleton (0, 1)
  hom := RealPairing.singletonShiftHom 0 1 0
  inv := RealPairing.singletonShiftHom 0 0 1

/-- The concrete model contains precisely the old category data and the
new specified parity data. No laws occur in its computational fields. -/
def realPiData : PiSuperfusionData.{0, 0} where
  toWeaklyPointedSuperfusionData := RMod.realRModData
  pi := realPi

end RMod.Classification
