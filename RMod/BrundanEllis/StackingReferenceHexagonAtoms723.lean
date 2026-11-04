import RMod.BrundanEllis.StackingReferenceHexagonAtoms327
import RMod.BrundanEllis.StackingReferenceHexagonAtoms372
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms723
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 2 3) (LeftIndex 7 2 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.assocBCA

theorem assocABC_eq : associatorZ 7 2 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523359,
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

def outerABC : Matrix (LeftIndex 2 3 7) (RightIndex 7 2 3) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 3 7 r) []).getD (rightPosition 7 2 3 s) 0

theorem outerABC_eq : outerRightZ 7 2 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 2 7 3) (LeftIndex 2 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocBCA

theorem assocBAC_eq : associatorZ 2 7 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocBCA_eq

def innerABC : Matrix (LeftIndex 2 7 3) (LeftIndex 7 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 2 3 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 3 2) (RightIndex 7 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 7 2 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523684,
    decodeIntegerRow 16 3 1 21523522,
    decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21524818,
    decodeIntegerRow 16 3 1 11957422,
    decodeIntegerRow 16 3 1 2391484,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 23649124,
    decodeIntegerRow 16 3 1 21523324,
    decodeIntegerRow 16 3 1 21523378,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 21510238,
    decodeIntegerRow 16 3 1 21549604,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21759556]

def inverseACB : Matrix (LeftIndex 7 3 2) (RightIndex 7 3 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 3 2 r) []).getD (rightPosition 7 3 2 s) 0

theorem inverseACB_eq : associatorInverseZ 7 3 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 7 2) (LeftIndex 7 3 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 7 3 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 2 3 7) (LeftIndex 2 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocBAC

theorem assocBCA_eq : associatorZ 2 3 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 2 3 7) (RightIndex 2 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 7 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 3 7 2) (LeftIndex 3 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.assocABC

theorem assocCAB_eq : associatorZ 3 7 2 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.assocABC_eq

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

def outerLeftABC : Matrix (RightIndex 3 7 2) (LeftIndex 7 2 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 7 2 r) []).getD (leftPosition 7 2 3 s) 0

theorem outerLeftABC_eq : outerLeftZ 7 2 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms723
