import RMod.BrundanEllis.StackingReferenceHexagonAtoms416
import RMod.BrundanEllis.StackingReferenceHexagonAtoms461
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms614
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 1 4) (LeftIndex 6 1 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.assocBCA

theorem assocABC_eq : associatorZ 6 1 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.assocBCA_eq

def outerABC : Matrix (LeftIndex 1 4 6) (RightIndex 6 1 4) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 1 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 1 6 4) (LeftIndex 1 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocBCA

theorem assocBAC_eq : associatorZ 1 6 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocBCA_eq

def innerABC : Matrix (LeftIndex 1 6 4) (LeftIndex 6 1 4) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 1 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 4 1) (RightIndex 6 1 4) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 1 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21529918,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582382,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 23117764,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35872996,
    decodeIntegerRow 16 3 1 7175182,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19929118,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464284,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21516796]

def inverseACB : Matrix (LeftIndex 6 4 1) (RightIndex 6 4 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 4 1 r) []).getD (rightPosition 6 4 1 s) 0

theorem inverseACB_eq : associatorInverseZ 6 4 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 6 1) (LeftIndex 6 4 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 6 4 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 1 4 6) (LeftIndex 1 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocBAC

theorem assocBCA_eq : associatorZ 1 4 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 1 4 6) (RightIndex 1 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 6 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 4 6 1) (LeftIndex 4 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.assocABC

theorem assocCAB_eq : associatorZ 4 6 1 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.assocABC_eq

def outerLeftABC : Matrix (RightIndex 4 6 1) (LeftIndex 6 1 4) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 1 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms614
