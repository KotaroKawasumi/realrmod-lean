import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms330
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

def assocABC : Matrix (RightIndex 3 3 0) (LeftIndex 3 3 0) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 3 0 r) []).getD (leftPosition 3 3 0 s) 0

theorem assocABC_eq : associatorZ 3 3 0 = assocABC := by
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

def outerABC : Matrix (LeftIndex 3 0 3) (RightIndex 3 3 0) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 3 0 3 r) []).getD (rightPosition 3 3 0 s) 0

theorem outerABC_eq : outerRightZ 3 3 0 = outerABC := by
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

def assocBAC : Matrix (RightIndex 3 3 0) (LeftIndex 3 3 0) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 3 3 0 r) []).getD (leftPosition 3 3 0 s) 0

theorem assocBAC_eq : associatorZ 3 3 0 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
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

def innerABC : Matrix (LeftIndex 3 3 0) (LeftIndex 3 3 0) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 3 3 0 r) []).getD (leftPosition 3 3 0 s) 0

theorem innerABC_eq : innerLeftZ 3 3 0 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 0 3) (RightIndex 3 3 0) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 3 0 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def inverseACB : Matrix (LeftIndex 3 0 3) (RightIndex 3 0 3) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem inverseACB_eq : associatorInverseZ 3 0 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 0 3 3) (LeftIndex 3 0 3) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 0 3 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 3 0 3) (LeftIndex 3 0 3) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem assocBCA_eq : associatorZ 3 0 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 3 0 3) (RightIndex 3 3 0) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 3 3 0 = innerRightBAC := by
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

def assocCAB : Matrix (RightIndex 0 3 3) (LeftIndex 0 3 3) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 0 3 3 r) []).getD (leftPosition 0 3 3 s) 0

theorem assocCAB_eq : associatorZ 0 3 3 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 0 3 3) (LeftIndex 3 3 0) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 3 0 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms330
