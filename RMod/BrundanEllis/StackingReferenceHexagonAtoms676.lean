import RMod.BrundanEllis.StackingReferenceHexagonAtoms667
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms676
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 7 6) (LeftIndex 6 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocBCA

theorem assocABC_eq : associatorZ 6 7 6 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocBCA_eq

def outerABC : Matrix (LeftIndex 7 6 6) (RightIndex 6 7 6) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 7 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 6 6) (LeftIndex 7 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocCAB

theorem assocBAC_eq : associatorZ 7 6 6 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 6 6) (LeftIndex 6 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.innerACB

theorem innerABC_eq : innerLeftZ 6 7 6 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.innerACB_eq

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522416,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21525472,
    decodeIntegerRow 16 3 1 21523872,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525460,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 35301460,
    decodeIntegerRow 16 3 1 36482440,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 36324976]

def innerRightABC : Matrix (RightIndex 6 6 7) (RightIndex 6 7 6) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 6 6 7 r) []).getD (rightPosition 6 7 6 s) 0

theorem innerRightABC_eq : innerRightZ 6 7 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562754]

def inverseACB : Matrix (LeftIndex 6 6 7) (RightIndex 6 6 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 6 7 r) []).getD (rightPosition 6 6 7 s) 0

theorem inverseACB_eq : associatorInverseZ 6 6 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 6 7) (LeftIndex 6 6 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.innerABC

theorem innerACB_eq : innerLeftZ 6 6 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.innerABC_eq

def assocBCA : Matrix (RightIndex 7 6 6) (LeftIndex 7 6 6) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 7 6 6 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21464311]

def innerRightBAC : Matrix (RightIndex 7 6 6) (RightIndex 7 6 6) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 7 6 6 r) []).getD (rightPosition 7 6 6 s) 0

theorem innerRightBAC_eq : innerRightZ 7 6 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 6 6 7) (LeftIndex 6 6 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocABC

theorem assocCAB_eq : associatorZ 6 6 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocABC_eq

def outerLeftABC : Matrix (RightIndex 6 6 7) (LeftIndex 6 7 6) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 7 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms676
