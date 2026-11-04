import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16760182,
    decodeIntegerRow 16 3 1 35879062,
    decodeIntegerRow 16 3 1 21169798,
    decodeIntegerRow 16 3 1 23178918,
    decodeIntegerRow 16 3 1 26325958,
    decodeIntegerRow 16 3 1 7180762,
    decodeIntegerRow 16 3 1 22231222,
    decodeIntegerRow 16 3 1 19985898,
    decodeIntegerRow 16 3 1 35878594,
    decodeIntegerRow 16 3 1 16759966,
    decodeIntegerRow 16 3 1 23174546,
    decodeIntegerRow 16 3 1 21168334,
    decodeIntegerRow 16 3 1 7181266,
    decodeIntegerRow 16 3 1 26326066,
    decodeIntegerRow 16 3 1 19990274,
    decodeIntegerRow 16 3 1 22232674]

def assocABC : Matrix (RightIndex 3 4 7) (LeftIndex 3 4 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 4 7 r) []).getD (leftPosition 3 4 7 s) 0

theorem assocABC_eq : associatorZ 3 4 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
    decodeIntegerRow 16 3 1 27824216,
    decodeIntegerRow 16 3 1 24674772,
    decodeIntegerRow 16 3 1 36220984,
    decodeIntegerRow 16 3 1 35169748,
    decodeIntegerRow 16 3 1 15227096,
    decodeIntegerRow 16 3 1 18376212,
    decodeIntegerRow 16 3 1 6827704,
    decodeIntegerRow 16 3 1 27981624,
    decodeIntegerRow 16 3 1 7534828,
    decodeIntegerRow 16 3 1 36588376,
    decodeIntegerRow 16 3 1 24753452,
    decodeIntegerRow 16 3 1 27977144,
    decodeIntegerRow 16 3 1 7535788,
    decodeIntegerRow 16 3 1 36586456,
    decodeIntegerRow 16 3 1 24749292]

def outerABC : Matrix (LeftIndex 4 7 3) (RightIndex 3 4 7) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 4 7 3 r) []).getD (rightPosition 3 4 7 s) 0

theorem outerABC_eq : outerRightZ 3 4 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21516808,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 35872024]

def assocBAC : Matrix (RightIndex 4 3 7) (LeftIndex 4 3 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 4 3 7 r) []).getD (leftPosition 4 3 7 s) 0

theorem assocBAC_eq : associatorZ 4 3 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 4 3 7) (LeftIndex 3 4 7) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 4 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 7 4) (RightIndex 3 4 7) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 4 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523606,
    decodeIntegerRow 16 3 1 21523442,
    decodeIntegerRow 16 3 1 21525574,
    decodeIntegerRow 16 3 1 21524098,
    decodeIntegerRow 16 3 1 21523440,
    decodeIntegerRow 16 3 1 21523600,
    decodeIntegerRow 16 3 1 21524080,
    decodeIntegerRow 16 3 1 21525520,
    decodeIntegerRow 16 3 1 16681342,
    decodeIntegerRow 16 3 1 36049414,
    decodeIntegerRow 16 3 1 20985358,
    decodeIntegerRow 16 3 1 23137366,
    decodeIntegerRow 16 3 1 7351600,
    decodeIntegerRow 16 3 1 26247280,
    decodeIntegerRow 16 3 1 19948720,
    decodeIntegerRow 16 3 1 22048240]

def inverseACB : Matrix (LeftIndex 3 7 4) (RightIndex 3 7 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 7 4 r) []).getD (rightPosition 3 7 4 s) 0

theorem inverseACB_eq : associatorInverseZ 3 7 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 3 4) (LeftIndex 3 7 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 7 4 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21525656,
    decodeIntegerRow 16 3 1 21522868,
    decodeIntegerRow 16 3 1 21524344,
    decodeIntegerRow 16 3 1 21525492,
    decodeIntegerRow 16 3 1 35170240,
    decodeIntegerRow 16 3 1 15224800,
    decodeIntegerRow 16 3 1 18374080,
    decodeIntegerRow 16 3 1 6826720,
    decodeIntegerRow 16 3 1 6459304,
    decodeIntegerRow 16 3 1 24751372,
    decodeIntegerRow 16 3 1 15067336,
    decodeIntegerRow 16 3 1 7535308,
    decodeIntegerRow 16 3 1 21525440,
    decodeIntegerRow 16 3 1 21522400,
    decodeIntegerRow 16 3 1 21522880,
    decodeIntegerRow 16 3 1 21521120]

def assocBCA : Matrix (RightIndex 4 7 3) (LeftIndex 4 7 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 4 7 3 r) []).getD (leftPosition 4 7 3 s) 0

theorem assocBCA_eq : associatorZ 4 7 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 4 7 3) (RightIndex 4 3 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 4 3 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21562754,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 36404194,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 35339854,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21352762,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 27902758]

def assocCAB : Matrix (RightIndex 7 3 4) (LeftIndex 7 3 4) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 3 4 r) []).getD (leftPosition 7 3 4 s) 0

theorem assocCAB_eq : associatorZ 7 3 4 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 6643012,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 15146068]

def outerLeftABC : Matrix (RightIndex 7 3 4) (LeftIndex 3 4 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 3 4 r) []).getD (leftPosition 3 4 7 s) 0

theorem outerLeftABC_eq : outerLeftZ 3 4 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347
