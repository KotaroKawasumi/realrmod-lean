import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577
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

def assocABC : Matrix (RightIndex 5 7 7) (LeftIndex 5 7 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 7 7 r) []).getD (leftPosition 5 7 7 s) 0

theorem assocABC_eq : associatorZ 5 7 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 7 7 5) (RightIndex 5 7 7) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 7 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808]

def assocBAC : Matrix (RightIndex 7 5 7) (LeftIndex 7 5 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 7 5 7 r) []).getD (leftPosition 7 5 7 s) 0

theorem assocBAC_eq : associatorZ 7 5 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 7 5 7) (LeftIndex 5 7 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 7 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21700510,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 35872024,
    decodeIntegerRow 16 3 1 16740310,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21529912]

def innerRightABC : Matrix (RightIndex 5 7 7) (RightIndex 5 7 7) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 5 7 7 r) []).getD (rightPosition 5 7 7 s) 0

theorem innerRightABC_eq : innerRightZ 5 7 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def inverseACB : Matrix (LeftIndex 5 7 7) (RightIndex 5 7 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 7 7 r) []).getD (rightPosition 5 7 7 s) 0

theorem inverseACB_eq : associatorInverseZ 5 7 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 5 7) (LeftIndex 5 7 7) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 5 7 7 = innerACB := innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808]

def assocBCA : Matrix (RightIndex 7 7 5) (LeftIndex 7 7 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 7 5 r) []).getD (leftPosition 7 7 5 s) 0

theorem assocBCA_eq : associatorZ 7 7 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 7 5) (RightIndex 7 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 5 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 7 5 7) (LeftIndex 7 5 7) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 7 5 7 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 7 5 7) (LeftIndex 5 7 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 7 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577
