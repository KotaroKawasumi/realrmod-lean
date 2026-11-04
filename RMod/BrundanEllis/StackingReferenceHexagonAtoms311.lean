import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms311
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18166408,
    decodeIntegerRow 16 3 1 6722204,
    decodeIntegerRow 16 3 1 7744316,
    decodeIntegerRow 16 3 1 28086472,
    decodeIntegerRow 16 3 1 7667528,
    decodeIntegerRow 16 3 1 27714844,
    decodeIntegerRow 16 3 1 24543676,
    decodeIntegerRow 16 3 1 36482952,
    decodeIntegerRow 16 3 1 7746204,
    decodeIntegerRow 16 3 1 14964472,
    decodeIntegerRow 16 3 1 18161848,
    decodeIntegerRow 16 3 1 36325436,
    decodeIntegerRow 16 3 1 24539164,
    decodeIntegerRow 16 3 1 6564792,
    decodeIntegerRow 16 3 1 7665528,
    decodeIntegerRow 16 3 1 15327676]

def assocABC : Matrix (RightIndex 3 1 1) (LeftIndex 3 1 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 1 1 r) []).getD (leftPosition 3 1 1 s) 0

theorem assocABC_eq : associatorZ 3 1 1 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 1 1 3) (RightIndex 3 1 1) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 1 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 35872996,
    decodeIntegerRow 16 3 1 20991676,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21516796,
    decodeIntegerRow 16 3 1 21503676,
    decodeIntegerRow 16 3 1 7175182,
    decodeIntegerRow 16 3 1 16742578,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 21346222,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21529918]

def assocBAC : Matrix (RightIndex 1 3 1) (LeftIndex 1 3 1) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 3 1 r) []).getD (leftPosition 1 3 1 s) 0

theorem assocBAC_eq : associatorZ 1 3 1 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 3 1) (LeftIndex 3 1 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 1 1 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 36403708,
    decodeIntegerRow 16 3 1 35340826,
    decodeIntegerRow 16 3 1 15146068,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21707068,
    decodeIntegerRow 16 3 1 21693946,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 21523846,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21522388,
    decodeIntegerRow 16 3 1 21523366,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523348]

def innerRightABC : Matrix (RightIndex 3 1 1) (RightIndex 3 1 1) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 3 1 1 r) []).getD (rightPosition 3 1 1 s) 0

theorem innerRightABC_eq : innerRightZ 3 1 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 15314560,
    decodeIntegerRow 16 3 1 7626164,
    decodeIntegerRow 16 3 1 36363884,
    decodeIntegerRow 16 3 1 18153280,
    decodeIntegerRow 16 3 1 35263040,
    decodeIntegerRow 16 3 1 14973364,
    decodeIntegerRow 16 3 1 18520684,
    decodeIntegerRow 16 3 1 6604160,
    decodeIntegerRow 16 3 1 36443588,
    decodeIntegerRow 16 3 1 24530560,
    decodeIntegerRow 16 3 1 14977600,
    decodeIntegerRow 16 3 1 35261148,
    decodeIntegerRow 16 3 1 24897988,
    decodeIntegerRow 16 3 1 6681920,
    decodeIntegerRow 16 3 1 7628160,
    decodeIntegerRow 16 3 1 15318748]

def inverseACB : Matrix (LeftIndex 3 1 1) (RightIndex 3 1 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 1 1 r) []).getD (rightPosition 3 1 1 s) 0

theorem inverseACB_eq : associatorInverseZ 3 1 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 3 1) (LeftIndex 3 1 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 1 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 7116160,
    decodeIntegerRow 16 3 1 16919716,
    decodeIntegerRow 16 3 1 23111044,
    decodeIntegerRow 16 3 1 22074240,
    decodeIntegerRow 16 3 1 16565440,
    decodeIntegerRow 16 3 1 35812516,
    decodeIntegerRow 16 3 1 21011844,
    decodeIntegerRow 16 3 1 23124160,
    decodeIntegerRow 16 3 1 23124328,
    decodeIntegerRow 16 3 1 21011360,
    decodeIntegerRow 16 3 1 7232800,
    decodeIntegerRow 16 3 1 26485672,
    decodeIntegerRow 16 3 1 22074728,
    decodeIntegerRow 16 3 1 23111200,
    decodeIntegerRow 16 3 1 26131360,
    decodeIntegerRow 16 3 1 35932072]

def assocBCA : Matrix (RightIndex 1 1 3) (LeftIndex 1 1 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 1 3 r) []).getD (leftPosition 1 1 3 s) 0

theorem assocBCA_eq : associatorZ 1 1 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 1 3) (RightIndex 1 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 3 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 35872996,
    decodeIntegerRow 16 3 1 20991676,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21516796,
    decodeIntegerRow 16 3 1 21503676,
    decodeIntegerRow 16 3 1 7175182,
    decodeIntegerRow 16 3 1 16742578,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 21346222,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21529918]

def assocCAB : Matrix (RightIndex 1 3 1) (LeftIndex 1 3 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 1 3 1 r) []).getD (leftPosition 1 3 1 s) 0

theorem assocCAB_eq : associatorZ 1 3 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 1 3 1) (LeftIndex 3 1 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 1 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms311
