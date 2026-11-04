import RMod.BrundanEllis.StackingReferenceHexagonAtoms426
import RMod.BrundanEllis.StackingReferenceHexagonAtoms462
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms624
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 2 4) (LeftIndex 6 2 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.assocBCA

theorem assocABC_eq : associatorZ 6 2 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.assocBCA_eq

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

def outerABC : Matrix (LeftIndex 2 4 6) (RightIndex 6 2 4) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 4 6 r) []).getD (rightPosition 6 2 4 s) 0

theorem outerABC_eq : outerRightZ 6 2 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 2 6 4) (LeftIndex 2 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocBCA

theorem assocBAC_eq : associatorZ 2 6 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocBCA_eq

def innerABC : Matrix (LeftIndex 2 6 4) (LeftIndex 6 2 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 2 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 4 2) (RightIndex 6 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 2 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21641458,
    decodeIntegerRow 16 3 1 21549604,
    decodeIntegerRow 16 3 1 21510238,
    decodeIntegerRow 16 3 1 21523324,
    decodeIntegerRow 16 3 1 21523378,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 40655236,
    decodeIntegerRow 16 3 1 20460478,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 21521902,
    decodeIntegerRow 16 3 1 21520444,
    decodeIntegerRow 16 3 1 21523522,
    decodeIntegerRow 16 3 1 21523684]

def inverseACB : Matrix (LeftIndex 6 4 2) (RightIndex 6 4 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 4 2 r) []).getD (rightPosition 6 4 2 s) 0

theorem inverseACB_eq : associatorInverseZ 6 4 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 6 2) (LeftIndex 6 4 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 6 4 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 2 4 6) (LeftIndex 2 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocBAC

theorem assocBCA_eq : associatorZ 2 4 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 2 4 6) (RightIndex 2 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 6 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 4 6 2) (LeftIndex 4 6 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.assocABC

theorem assocCAB_eq : associatorZ 4 6 2 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.assocABC_eq

def outerLeftABC : Matrix (RightIndex 4 6 2) (LeftIndex 6 2 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 2 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms624
