import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21562754,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 6643498,
    decodeIntegerRow 16 3 1 15148174,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 21339658]

def assocABC : Matrix (RightIndex 4 5 6) (LeftIndex 4 5 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 5 6 r) []).getD (leftPosition 4 5 6 s) 0

theorem assocABC_eq : associatorZ 4 5 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 5 6 4) (RightIndex 4 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 5 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19988032,
    decodeIntegerRow 16 3 1 21168832,
    decodeIntegerRow 16 3 1 16718520,
    decodeIntegerRow 16 3 1 7167160,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 22232200,
    decodeIntegerRow 16 3 1 23176840,
    decodeIntegerRow 16 3 1 35864980,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 22231696,
    decodeIntegerRow 16 3 1 23176624,
    decodeIntegerRow 16 3 1 19988140,
    decodeIntegerRow 16 3 1 21169300,
    decodeIntegerRow 16 3 1 16722896,
    decodeIntegerRow 16 3 1 7168624]

def assocBAC : Matrix (RightIndex 5 4 6) (LeftIndex 5 4 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 5 4 6 r) []).getD (leftPosition 5 4 6 s) 0

theorem assocBAC_eq : associatorZ 5 4 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 5 4 6) (LeftIndex 4 5 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 4 5 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 6 5) (RightIndex 4 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 5 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21365888,
    decodeIntegerRow 16 3 1 21470848,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 5580940,
    decodeIntegerRow 16 3 1 16211380,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21589000]

def inverseACB : Matrix (LeftIndex 4 6 5) (RightIndex 4 6 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 6 5 r) []).getD (rightPosition 4 6 5 s) 0

theorem inverseACB_eq : associatorInverseZ 4 6 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 4 5) (LeftIndex 4 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 4 6 5 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21365888,
    decodeIntegerRow 16 3 1 21470848,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 5580940,
    decodeIntegerRow 16 3 1 16211380,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21589000]

def assocBCA : Matrix (RightIndex 5 6 4) (LeftIndex 5 6 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 6 4 r) []).getD (leftPosition 5 6 4 s) 0

theorem assocBCA_eq : associatorZ 5 6 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 5 6 4) (RightIndex 5 4 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 5 4 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16720960,
    decodeIntegerRow 16 3 1 7168000,
    decodeIntegerRow 16 3 1 23176000,
    decodeIntegerRow 16 3 1 22229760,
    decodeIntegerRow 16 3 1 21166880,
    decodeIntegerRow 16 3 1 19987360,
    decodeIntegerRow 16 3 1 7180960,
    decodeIntegerRow 16 3 1 16759840,
    decodeIntegerRow 16 3 1 35878936,
    decodeIntegerRow 16 3 1 26326264,
    decodeIntegerRow 16 3 1 20812584,
    decodeIntegerRow 16 3 1 19869256,
    decodeIntegerRow 16 3 1 23057908,
    decodeIntegerRow 16 3 1 21875468,
    decodeIntegerRow 16 3 1 26286412,
    decodeIntegerRow 16 3 1 35865652]

def assocCAB : Matrix (RightIndex 6 4 5) (LeftIndex 6 4 5) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 4 5 r) []).getD (leftPosition 6 4 5 s) 0

theorem assocCAB_eq : associatorZ 6 4 5 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 6 4 5) (LeftIndex 4 5 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 5 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456
