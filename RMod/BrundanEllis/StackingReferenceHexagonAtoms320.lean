import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms320
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def assocABC : Matrix (RightIndex 3 2 0) (LeftIndex 3 2 0) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 2 0 r) []).getD (leftPosition 3 2 0 s) 0

theorem assocABC_eq : associatorZ 3 2 0 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 0 3) (RightIndex 3 2 0) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 2 0 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def assocBAC : Matrix (RightIndex 2 3 0) (LeftIndex 2 3 0) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 3 0 r) []).getD (leftPosition 2 3 0 s) 0

theorem assocBAC_eq : associatorZ 2 3 0 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 3 0) (LeftIndex 3 2 0) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 2 0 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 0 2) (RightIndex 3 2 0) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 2 0 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def inverseACB : Matrix (LeftIndex 3 0 2) (RightIndex 3 0 2) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem inverseACB_eq : associatorInverseZ 3 0 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 0 3 2) (LeftIndex 3 0 2) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 0 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 2 0 3) (LeftIndex 2 0 3) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem assocBCA_eq : associatorZ 2 0 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 0 3) (RightIndex 2 3 0) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 3 0 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def assocCAB : Matrix (RightIndex 0 3 2) (LeftIndex 0 3 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 0 3 2 r) []).getD (leftPosition 0 3 2 s) 0

theorem assocCAB_eq : associatorZ 0 3 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 0 3 2) (LeftIndex 3 2 0) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 2 0 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms320
