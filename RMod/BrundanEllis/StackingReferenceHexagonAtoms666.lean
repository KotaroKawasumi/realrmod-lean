import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms666
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043]

def assocABC : Matrix (RightIndex 6 6 6) (LeftIndex 6 6 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 6 6 6 r) []).getD (leftPosition 6 6 6 s) 0

theorem assocABC_eq : associatorZ 6 6 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 6 6 6) (RightIndex 6 6 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 6 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 6 6) (LeftIndex 6 6 6) ℤ := assocABC

theorem assocBAC_eq : associatorZ 6 6 6 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409]

def innerABC : Matrix (LeftIndex 6 6 6) (LeftIndex 6 6 6) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 6 6 6 r) []).getD (leftPosition 6 6 6 s) 0

theorem innerABC_eq : innerLeftZ 6 6 6 = innerABC := by
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
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409]

def innerRightABC : Matrix (RightIndex 6 6 6) (RightIndex 6 6 6) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 6 6 6 r) []).getD (rightPosition 6 6 6 s) 0

theorem innerRightABC_eq : innerRightZ 6 6 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361]

def inverseACB : Matrix (LeftIndex 6 6 6) (RightIndex 6 6 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 6 6 r) []).getD (rightPosition 6 6 6 s) 0

theorem inverseACB_eq : associatorInverseZ 6 6 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 6 6) (LeftIndex 6 6 6) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 6 6 6 = innerACB := innerABC_eq

def assocBCA : Matrix (RightIndex 6 6 6) (LeftIndex 6 6 6) ℤ := assocABC

theorem assocBCA_eq : associatorZ 6 6 6 = assocBCA := assocABC_eq

def innerRightBAC : Matrix (RightIndex 6 6 6) (RightIndex 6 6 6) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 6 6 6 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 6 6 6) (LeftIndex 6 6 6) ℤ := assocABC

theorem assocCAB_eq : associatorZ 6 6 6 = assocCAB := assocABC_eq

def outerLeftABC : Matrix (RightIndex 6 6 6) (LeftIndex 6 6 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 6 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms666
