import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 31089296,
    decodeIntegerRow 16 3 1 40655240,
    decodeIntegerRow 16 3 1 20460460,
    decodeIntegerRow 16 3 1 19397632,
    decodeIntegerRow 16 3 1 21405100,
    decodeIntegerRow 16 3 1 21287488,
    decodeIntegerRow 16 3 1 21535024,
    decodeIntegerRow 16 3 1 21552520,
    decodeIntegerRow 16 3 1 21508780,
    decodeIntegerRow 16 3 1 21546688,
    decodeIntegerRow 16 3 1 21405424,
    decodeIntegerRow 16 3 1 21759880,
    decodeIntegerRow 16 3 1 20460496,
    decodeIntegerRow 16 3 1 23649160,
    decodeIntegerRow 16 3 1 11957420,
    decodeIntegerRow 16 3 1 40655232]

def assocABC : Matrix (RightIndex 5 1 6) (LeftIndex 5 1 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 1 6 r) []).getD (leftPosition 5 1 6 s) 0

theorem assocABC_eq : associatorZ 5 1 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def outerABC : Matrix (LeftIndex 1 6 5) (RightIndex 5 1 6) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 1 6 5 r) []).getD (rightPosition 5 1 6 s) 0

theorem outerABC_eq : outerRightZ 5 1 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21617968,
    decodeIntegerRow 16 3 1 21745300,
    decodeIntegerRow 16 3 1 21272260,
    decodeIntegerRow 16 3 1 21382096,
    decodeIntegerRow 16 3 1 9831696,
    decodeIntegerRow 16 3 1 1328580,
    decodeIntegerRow 16 3 1 3454380,
    decodeIntegerRow 16 3 1 14083152,
    decodeIntegerRow 16 3 1 28963500,
    decodeIntegerRow 16 3 1 39592368,
    decodeIntegerRow 16 3 1 1328624,
    decodeIntegerRow 16 3 1 9831620,
    decodeIntegerRow 16 3 1 21375940,
    decodeIntegerRow 16 3 1 21275824,
    decodeIntegerRow 16 3 1 21299152,
    decodeIntegerRow 16 3 1 21434260]

def assocBAC : Matrix (RightIndex 1 5 6) (LeftIndex 1 5 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 5 6 r) []).getD (leftPosition 1 5 6 s) 0

theorem assocBAC_eq : associatorZ 1 5 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 5 6) (LeftIndex 5 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 1 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 6 1) (RightIndex 5 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 1 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21602092,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21693946,
    decodeIntegerRow 16 3 1 21483994,
    decodeIntegerRow 16 3 1 21523334,
    decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 15146068,
    decodeIntegerRow 16 3 1 36403708,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 21521254,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21525628]

def inverseACB : Matrix (LeftIndex 5 6 1) (RightIndex 5 6 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 6 1 r) []).getD (rightPosition 5 6 1 s) 0

theorem inverseACB_eq : associatorInverseZ 5 6 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 5 1) (LeftIndex 5 6 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 6 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 21707068,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21523334,
    decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 15146068,
    decodeIntegerRow 16 3 1 36403708,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21523846,
    decodeIntegerRow 16 3 1 21522388,
    decodeIntegerRow 16 3 1 21521092]

def assocBCA : Matrix (RightIndex 1 6 5) (LeftIndex 1 6 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 6 5 r) []).getD (leftPosition 1 6 5 s) 0

theorem assocBCA_eq : associatorZ 1 6 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 6 5) (RightIndex 1 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 5 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21655876,
    decodeIntegerRow 16 3 1 21736552,
    decodeIntegerRow 16 3 1 21626716,
    decodeIntegerRow 16 3 1 21263512,
    decodeIntegerRow 16 3 1 10894556,
    decodeIntegerRow 16 3 1 4517288,
    decodeIntegerRow 16 3 1 13020284,
    decodeIntegerRow 16 3 1 42781032,
    decodeIntegerRow 16 3 1 4517208,
    decodeIntegerRow 16 3 1 32152196,
    decodeIntegerRow 16 3 1 42780968,
    decodeIntegerRow 16 3 1 30026396,
    decodeIntegerRow 16 3 1 21730072,
    decodeIntegerRow 16 3 1 21393436,
    decodeIntegerRow 16 3 1 21258328,
    decodeIntegerRow 16 3 1 21416764]

def assocCAB : Matrix (RightIndex 6 5 1) (LeftIndex 6 5 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 5 1 r) []).getD (leftPosition 6 5 1 s) 0

theorem assocCAB_eq : associatorZ 6 5 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919]

def outerLeftABC : Matrix (RightIndex 6 5 1) (LeftIndex 5 1 6) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 6 5 1 r) []).getD (leftPosition 5 1 6 s) 0

theorem outerLeftABC_eq : outerLeftZ 5 1 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516
