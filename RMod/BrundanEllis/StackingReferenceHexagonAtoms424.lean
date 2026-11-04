import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523117]

def assocABC : Matrix (RightIndex 4 2 4) (LeftIndex 4 2 4) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 2 4 r) []).getD (leftPosition 4 2 4 s) 0

theorem assocABC_eq : associatorZ 4 2 4 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 4 4) (RightIndex 4 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 2 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21529912]

def assocBAC : Matrix (RightIndex 2 4 4) (LeftIndex 2 4 4) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 4 4 r) []).getD (leftPosition 2 4 4 s) 0

theorem assocBAC_eq : associatorZ 2 4 4 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 4 4) (LeftIndex 4 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 4 2 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 4 2) (RightIndex 4 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 2 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21529912]

def inverseACB : Matrix (LeftIndex 4 4 2) (RightIndex 4 4 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 4 2 r) []).getD (rightPosition 4 4 2 s) 0

theorem inverseACB_eq : associatorInverseZ 4 4 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def innerACB : Matrix (LeftIndex 4 4 2) (LeftIndex 4 4 2) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 4 4 2 r) []).getD (leftPosition 4 4 2 s) 0

theorem innerACB_eq : innerLeftZ 4 4 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 2 4 4) (LeftIndex 2 4 4) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 2 4 4 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def innerRightBAC : Matrix (RightIndex 2 4 4) (RightIndex 2 4 4) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 2 4 4 r) []).getD (rightPosition 2 4 4 s) 0

theorem innerRightBAC_eq : innerRightZ 2 4 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 21877654,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 21525546,
    decodeIntegerRow 16 3 1 21524086,
    decodeIntegerRow 16 3 1 21523108,
    decodeIntegerRow 16 3 1 21523252,
    decodeIntegerRow 16 3 1 35865706,
    decodeIntegerRow 16 3 1 26286646,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 21523594,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21522628]

def assocCAB : Matrix (RightIndex 4 4 2) (LeftIndex 4 4 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 4 4 2 r) []).getD (leftPosition 4 4 2 s) 0

theorem assocCAB_eq : associatorZ 4 4 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 4 4 2) (LeftIndex 4 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 2 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424
