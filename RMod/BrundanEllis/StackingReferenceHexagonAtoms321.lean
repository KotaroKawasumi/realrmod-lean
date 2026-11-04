import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms321
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21562754,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21352762,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 36404194,
    decodeIntegerRow 16 3 1 35339854,
    decodeIntegerRow 16 3 1 27898546]

def assocABC : Matrix (RightIndex 3 2 1) (LeftIndex 3 2 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 2 1 r) []).getD (leftPosition 3 2 1 s) 0

theorem assocABC_eq : associatorZ 3 2 1 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35170732,
    decodeIntegerRow 16 3 1 15222504,
    decodeIntegerRow 16 3 1 18371948,
    decodeIntegerRow 16 3 1 6825736,
    decodeIntegerRow 16 3 1 7876972,
    decodeIntegerRow 16 3 1 27819624,
    decodeIntegerRow 16 3 1 24670508,
    decodeIntegerRow 16 3 1 36219016,
    decodeIntegerRow 16 3 1 15065096,
    decodeIntegerRow 16 3 1 35511892,
    decodeIntegerRow 16 3 1 6458344,
    decodeIntegerRow 16 3 1 18293268,
    decodeIntegerRow 16 3 1 15069576,
    decodeIntegerRow 16 3 1 35510932,
    decodeIntegerRow 16 3 1 6460264,
    decodeIntegerRow 16 3 1 18297428]

def outerABC : Matrix (LeftIndex 2 1 3) (RightIndex 3 2 1) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 1 3 r) []).getD (rightPosition 3 2 1 s) 0

theorem outerABC_eq : outerRightZ 3 2 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26306338,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 22054802,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 35872240,
    decodeIntegerRow 16 3 1 16740400,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21529840,
    decodeIntegerRow 16 3 1 21698320,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21344026]

def assocBAC : Matrix (RightIndex 2 3 1) (LeftIndex 2 3 1) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 3 1 r) []).getD (leftPosition 2 3 1 s) 0

theorem assocBAC_eq : associatorZ 2 3 1 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 3 1) (LeftIndex 3 2 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 2 1 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21525656,
    decodeIntegerRow 16 3 1 21522868,
    decodeIntegerRow 16 3 1 21524344,
    decodeIntegerRow 16 3 1 21525492,
    decodeIntegerRow 16 3 1 21521280,
    decodeIntegerRow 16 3 1 21524320,
    decodeIntegerRow 16 3 1 21523840,
    decodeIntegerRow 16 3 1 21525600,
    decodeIntegerRow 16 3 1 35170240,
    decodeIntegerRow 16 3 1 15224800,
    decodeIntegerRow 16 3 1 18374080,
    decodeIntegerRow 16 3 1 6826720,
    decodeIntegerRow 16 3 1 36587416,
    decodeIntegerRow 16 3 1 18295348,
    decodeIntegerRow 16 3 1 27979384,
    decodeIntegerRow 16 3 1 35511412]

def innerRightABC : Matrix (RightIndex 3 1 2) (RightIndex 3 2 1) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 3 1 2 r) []).getD (rightPosition 3 2 1 s) 0

theorem innerRightABC_eq : innerRightZ 3 2 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35871538,
    decodeIntegerRow 16 3 1 16742578,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 20992162,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 21503676,
    decodeIntegerRow 16 3 1 21516796,
    decodeIntegerRow 16 3 1 21346204,
    decodeIntegerRow 16 3 1 21464284,
    decodeIntegerRow 16 3 1 21516802,
    decodeIntegerRow 16 3 1 21503678,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21346222]

def inverseACB : Matrix (LeftIndex 3 1 2) (RightIndex 3 1 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 1 2 r) []).getD (rightPosition 3 1 2 s) 0

theorem inverseACB_eq : associatorInverseZ 3 1 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 3 2) (LeftIndex 3 1 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 1 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523333]

def assocBCA : Matrix (RightIndex 2 1 3) (LeftIndex 2 1 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 1 3 r) []).getD (leftPosition 2 1 3 s) 0

theorem assocBCA_eq : associatorZ 2 1 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 1 3) (RightIndex 2 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 3 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21525556,
    decodeIntegerRow 16 3 1 21522604,
    decodeIntegerRow 16 3 1 21523604,
    decodeIntegerRow 16 3 1 21523276,
    decodeIntegerRow 16 3 1 20972236,
    decodeIntegerRow 16 3 1 19922476,
    decodeIntegerRow 16 3 1 16563244,
    decodeIntegerRow 16 3 1 7115404,
    decodeIntegerRow 16 3 1 22035118,
    decodeIntegerRow 16 3 1 23111122,
    decodeIntegerRow 16 3 1 26129182,
    decodeIntegerRow 16 3 1 35813218,
    decodeIntegerRow 16 3 1 21525538,
    decodeIntegerRow 16 3 1 21522658,
    decodeIntegerRow 16 3 1 21523602,
    decodeIntegerRow 16 3 1 21523282]

def assocCAB : Matrix (RightIndex 1 3 2) (LeftIndex 1 3 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 1 3 2 r) []).getD (leftPosition 1 3 2 s) 0

theorem assocCAB_eq : associatorZ 1 3 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def outerLeftABC : Matrix (RightIndex 1 3 2) (LeftIndex 3 2 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 3 2 r) []).getD (leftPosition 3 2 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 3 2 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms321
