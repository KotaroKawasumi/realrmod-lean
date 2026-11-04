import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms622
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21525494,
    decodeIntegerRow 16 3 1 21523858,
    decodeIntegerRow 16 3 1 21522394,
    decodeIntegerRow 16 3 1 21521118,
    decodeIntegerRow 16 3 1 36574294,
    decodeIntegerRow 16 3 1 27940018,
    decodeIntegerRow 16 3 1 24633274,
    decodeIntegerRow 16 3 1 35157118,
    decodeIntegerRow 16 3 1 21523834,
    decodeIntegerRow 16 3 1 21521282,
    decodeIntegerRow 16 3 1 21521066,
    decodeIntegerRow 16 3 1 21524338,
    decodeIntegerRow 16 3 1 27861286,
    decodeIntegerRow 16 3 1 6813598,
    decodeIntegerRow 16 3 1 35524534,
    decodeIntegerRow 16 3 1 18255982]

def assocABC : Matrix (RightIndex 6 2 2) (LeftIndex 6 2 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 6 2 2 r) []).getD (leftPosition 6 2 2 s) 0

theorem assocABC_eq : associatorZ 6 2 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 2 6) (RightIndex 6 2 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 2 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19988032,
    decodeIntegerRow 16 3 1 21877420,
    decodeIntegerRow 16 3 1 7167160,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 26328200,
    decodeIntegerRow 16 3 1 7168624,
    decodeIntegerRow 16 3 1 21168832,
    decodeIntegerRow 16 3 1 23058580,
    decodeIntegerRow 16 3 1 22232200,
    decodeIntegerRow 16 3 1 23176624,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 35864980,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 19869880,
    decodeIntegerRow 16 3 1 20815024]

def assocBAC : Matrix (RightIndex 2 6 2) (LeftIndex 2 6 2) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 6 2 r) []).getD (leftPosition 2 6 2 s) 0

theorem assocBAC_eq : associatorZ 2 6 2 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 6 2) (LeftIndex 6 2 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 2 2 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043]

def innerRightABC : Matrix (RightIndex 6 2 2) (RightIndex 6 2 2) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 6 2 2 r) []).getD (rightPosition 6 2 2 s) 0

theorem innerRightABC_eq : innerRightZ 6 2 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 24714274]

def inverseACB : Matrix (LeftIndex 6 2 2) (RightIndex 6 2 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 2 2 r) []).getD (rightPosition 6 2 2 s) 0

theorem inverseACB_eq : associatorInverseZ 6 2 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 6 2) (LeftIndex 6 2 2) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 6 2 2 = innerACB := innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 7705920,
    decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 27900664,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 21691840,
    decodeIntegerRow 16 3 1 21562240,
    decodeIntegerRow 16 3 1 21445600,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21696052]

def assocBCA : Matrix (RightIndex 2 2 6) (LeftIndex 2 2 6) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 2 6 r) []).getD (leftPosition 2 2 6 s) 0

theorem assocBCA_eq : associatorZ 2 2 6 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 2 6) (RightIndex 2 6 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 6 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 2 6 2) (LeftIndex 2 6 2) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 2 6 2 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 2 6 2) (LeftIndex 6 2 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 2 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms622
