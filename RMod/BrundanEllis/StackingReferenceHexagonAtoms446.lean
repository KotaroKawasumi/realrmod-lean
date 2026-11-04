import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523414,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21524086,
    decodeIntegerRow 16 3 1 35865706,
    decodeIntegerRow 16 3 1 16720708,
    decodeIntegerRow 16 3 1 23058634,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 16760074]

def assocABC : Matrix (RightIndex 4 4 6) (LeftIndex 4 4 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 4 6 r) []).getD (leftPosition 4 4 6 s) 0

theorem assocABC_eq : associatorZ 4 4 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 4 6 4) (RightIndex 4 4 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 4 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 4 6) (LeftIndex 4 4 6) ℤ := assocABC

theorem assocBAC_eq : associatorZ 4 4 6 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def innerABC : Matrix (LeftIndex 4 4 6) (LeftIndex 4 4 6) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 4 4 6 r) []).getD (leftPosition 4 4 6 s) 0

theorem innerABC_eq : innerLeftZ 4 4 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 6 4) (RightIndex 4 4 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 4 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def inverseACB : Matrix (LeftIndex 4 6 4) (RightIndex 4 6 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 6 4 r) []).getD (rightPosition 4 6 4 s) 0

theorem inverseACB_eq : associatorInverseZ 4 6 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 4 4) (LeftIndex 4 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 4 6 4 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def assocBCA : Matrix (RightIndex 4 6 4) (LeftIndex 4 6 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 4 6 4 r) []).getD (leftPosition 4 6 4 s) 0

theorem assocBCA_eq : associatorZ 4 6 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 4 6 4) (RightIndex 4 4 6) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 4 6 = innerRightBAC := innerRightABC_eq

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21529912,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248]

def assocCAB : Matrix (RightIndex 6 4 4) (LeftIndex 6 4 4) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 4 4 r) []).getD (leftPosition 6 4 4 s) 0

theorem assocCAB_eq : associatorZ 6 4 4 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 6 4 4) (LeftIndex 4 4 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 4 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446
