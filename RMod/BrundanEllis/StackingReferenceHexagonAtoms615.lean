import RMod.BrundanEllis.StackingReferenceHexagonAtoms516
import RMod.BrundanEllis.StackingReferenceHexagonAtoms561
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms615
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 1 5) (LeftIndex 6 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.assocBCA

theorem assocABC_eq : associatorZ 6 1 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919]

def outerABC : Matrix (LeftIndex 1 5 6) (RightIndex 6 1 5) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 1 5 6 r) []).getD (rightPosition 6 1 5 s) 0

theorem outerABC_eq : outerRightZ 6 1 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 1 6 5) (LeftIndex 1 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocBCA

theorem assocBAC_eq : associatorZ 1 6 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocBCA_eq

def innerABC : Matrix (LeftIndex 1 6 5) (LeftIndex 6 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 1 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 5 1) (RightIndex 6 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 1 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21771544,
    decodeIntegerRow 16 3 1 21376264,
    decodeIntegerRow 16 3 1 21618292,
    decodeIntegerRow 16 3 1 21302068,
    decodeIntegerRow 16 3 1 41718104,
    decodeIntegerRow 16 3 1 9831624,
    decodeIntegerRow 16 3 1 28963572,
    decodeIntegerRow 16 3 1 3454388,
    decodeIntegerRow 16 3 1 3454344,
    decodeIntegerRow 16 3 1 28963496,
    decodeIntegerRow 16 3 1 33215028,
    decodeIntegerRow 16 3 1 1328588,
    decodeIntegerRow 16 3 1 21748216,
    decodeIntegerRow 16 3 1 21434584,
    decodeIntegerRow 16 3 1 21381772,
    decodeIntegerRow 16 3 1 21773812]

def inverseACB : Matrix (LeftIndex 6 5 1) (RightIndex 6 5 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 5 1 r) []).getD (rightPosition 6 5 1 s) 0

theorem inverseACB_eq : associatorInverseZ 6 5 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 6 1) (LeftIndex 6 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 6 5 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 1 5 6) (LeftIndex 1 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocBAC

theorem assocBCA_eq : associatorZ 1 5 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 1 5 6) (RightIndex 1 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 6 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 6 1) (LeftIndex 5 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.assocABC

theorem assocCAB_eq : associatorZ 5 6 1 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def outerLeftABC : Matrix (RightIndex 5 6 1) (LeftIndex 6 1 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 6 1 r) []).getD (leftPosition 6 1 5 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 1 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms615
