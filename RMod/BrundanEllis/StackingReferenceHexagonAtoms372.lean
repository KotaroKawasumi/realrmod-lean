import RMod.BrundanEllis.StackingReferenceHexagonAtoms327
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21769600,
    decodeIntegerRow 16 3 1 21380800,
    decodeIntegerRow 16 3 1 21614080,
    decodeIntegerRow 16 3 1 21303040,
    decodeIntegerRow 16 3 1 41718156,
    decodeIntegerRow 16 3 1 9831636,
    decodeIntegerRow 16 3 1 28963548,
    decodeIntegerRow 16 3 1 3454332,
    decodeIntegerRow 16 3 1 1328640,
    decodeIntegerRow 16 3 1 33215040,
    decodeIntegerRow 16 3 1 14083200,
    decodeIntegerRow 16 3 1 39592320,
    decodeIntegerRow 16 3 1 21775756,
    decodeIntegerRow 16 3 1 21377236,
    decodeIntegerRow 16 3 1 21616348,
    decodeIntegerRow 16 3 1 21297532]

def assocABC : Matrix (RightIndex 3 7 2) (LeftIndex 3 7 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 7 2 r) []).getD (leftPosition 3 7 2 s) 0

theorem assocABC_eq : associatorZ 3 7 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def outerABC : Matrix (LeftIndex 7 2 3) (RightIndex 3 7 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 7 2 3 r) []).getD (rightPosition 3 7 2 s) 0

theorem outerABC_eq : outerRightZ 3 7 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 3 2) (LeftIndex 7 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocCAB

theorem assocBAC_eq : associatorZ 7 3 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 3 2) (LeftIndex 3 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.innerACB

theorem innerABC_eq : innerLeftZ 3 7 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 2 7) (RightIndex 3 7 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 7 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 27900664,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 21337384,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21483508,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21445600,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 21562240,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 36403680,
    decodeIntegerRow 16 3 1 15146080]

def inverseACB : Matrix (LeftIndex 3 2 7) (RightIndex 3 2 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 2 7 r) []).getD (rightPosition 3 2 7 s) 0

theorem inverseACB_eq : associatorInverseZ 3 2 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 3 7) (LeftIndex 3 2 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.innerABC

theorem innerACB_eq : innerLeftZ 3 2 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712000,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21562240,
    decodeIntegerRow 16 3 1 21691840,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146056]

def assocBCA : Matrix (RightIndex 7 2 3) (LeftIndex 7 2 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 2 3 r) []).getD (leftPosition 7 2 3 s) 0

theorem assocBCA_eq : associatorZ 7 2 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 2 3) (RightIndex 7 3 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 3 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 2 3 7) (LeftIndex 2 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocBAC

theorem assocCAB_eq : associatorZ 2 3 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 23117683]

def outerLeftABC : Matrix (RightIndex 2 3 7) (LeftIndex 3 7 2) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 2 3 7 r) []).getD (leftPosition 3 7 2 s) 0

theorem outerLeftABC_eq : outerLeftZ 3 7 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372
