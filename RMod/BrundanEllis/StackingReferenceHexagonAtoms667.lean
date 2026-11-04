import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21484480]

def assocABC : Matrix (RightIndex 6 6 7) (LeftIndex 6 6 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 6 6 7 r) []).getD (leftPosition 6 6 7 s) 0

theorem assocABC_eq : associatorZ 6 6 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 6 7 6) (RightIndex 6 6 7) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 6 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 6 7) (LeftIndex 6 6 7) ℤ := assocABC

theorem assocBAC_eq : associatorZ 6 6 7 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
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

def innerABC : Matrix (LeftIndex 6 6 7) (LeftIndex 6 6 7) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 6 6 7 r) []).getD (leftPosition 6 6 7 s) 0

theorem innerABC_eq : innerLeftZ 6 6 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21524306,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21521266,
    decodeIntegerRow 16 3 1 21522902,
    decodeIntegerRow 16 3 1 21521242,
    decodeIntegerRow 16 3 1 21522846,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 18518422,
    decodeIntegerRow 16 3 1 7784626,
    decodeIntegerRow 16 3 1 6682378,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 35419558]

def innerRightABC : Matrix (RightIndex 6 7 6) (RightIndex 6 6 7) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 6 7 6 r) []).getD (rightPosition 6 6 7 s) 0

theorem innerRightABC_eq : innerRightZ 6 6 7 = innerRightABC := by
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

def inverseACB : Matrix (LeftIndex 6 7 6) (RightIndex 6 7 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 7 6 r) []).getD (rightPosition 6 7 6 s) 0

theorem inverseACB_eq : associatorInverseZ 6 7 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21524306,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21521266,
    decodeIntegerRow 16 3 1 21522902,
    decodeIntegerRow 16 3 1 21521242,
    decodeIntegerRow 16 3 1 21522846,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 18518422,
    decodeIntegerRow 16 3 1 7784626,
    decodeIntegerRow 16 3 1 6682378,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 35419558]

def innerACB : Matrix (LeftIndex 7 6 6) (LeftIndex 6 7 6) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 7 6 6 r) []).getD (leftPosition 6 7 6 s) 0

theorem innerACB_eq : innerLeftZ 6 7 6 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21484480]

def assocBCA : Matrix (RightIndex 6 7 6) (LeftIndex 6 7 6) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 7 6 r) []).getD (leftPosition 6 7 6 s) 0

theorem assocBCA_eq : associatorZ 6 7 6 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 7 6) (RightIndex 6 6 7) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 6 6 7 = innerRightBAC := innerRightABC_eq

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20932654,
    decodeIntegerRow 16 3 1 23294758,
    decodeIntegerRow 16 3 1 26315074,
    decodeIntegerRow 16 3 1 7155498,
    decodeIntegerRow 16 3 1 16749142,
    decodeIntegerRow 16 3 1 35853314,
    decodeIntegerRow 16 3 1 21995482,
    decodeIntegerRow 16 3 1 20106094,
    decodeIntegerRow 16 3 1 26310706,
    decodeIntegerRow 16 3 1 35892678,
    decodeIntegerRow 16 3 1 22113634,
    decodeIntegerRow 16 3 1 23294902,
    decodeIntegerRow 16 3 1 21996022,
    decodeIntegerRow 16 3 1 22940446,
    decodeIntegerRow 16 3 1 26301958,
    decodeIntegerRow 16 3 1 35851854]

def assocCAB : Matrix (RightIndex 7 6 6) (LeftIndex 7 6 6) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 6 6 r) []).getD (leftPosition 7 6 6 s) 0

theorem assocCAB_eq : associatorZ 7 6 6 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 7 6 6) (LeftIndex 6 6 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 6 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667
