import RMod.BrundanEllis.StackingReferenceHexagonAtoms324
import RMod.BrundanEllis.StackingReferenceHexagonAtoms342
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms423
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 4 2 3) (LeftIndex 4 2 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.assocBCA

theorem assocABC_eq : associatorZ 4 2 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.assocBCA_eq

def outerABC : Matrix (LeftIndex 2 3 4) (RightIndex 4 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 2 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 2 4 3) (LeftIndex 2 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocBCA

theorem assocBAC_eq : associatorZ 2 4 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocBCA_eq

def innerABC : Matrix (LeftIndex 2 4 3) (LeftIndex 4 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 4 2 3 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 3 2) (RightIndex 4 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 2 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21543034,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 7174534,
    decodeIntegerRow 16 3 1 26306572,
    decodeIntegerRow 16 3 1 21700508,
    decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23116954,
    decodeIntegerRow 16 3 1 21529894,
    decodeIntegerRow 16 3 1 21543052,
    decodeIntegerRow 16 3 1 16740634,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21582412,
    decodeIntegerRow 16 3 1 21700506]

def inverseACB : Matrix (LeftIndex 4 3 2) (RightIndex 4 3 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 3 2 r) []).getD (rightPosition 4 3 2 s) 0

theorem inverseACB_eq : associatorInverseZ 4 3 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 4 2) (LeftIndex 4 3 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 4 3 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 2 3 4) (LeftIndex 2 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocBAC

theorem assocBCA_eq : associatorZ 2 3 4 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 2 3 4) (RightIndex 2 4 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 4 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 3 4 2) (LeftIndex 3 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.assocABC

theorem assocCAB_eq : associatorZ 3 4 2 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.assocABC_eq

def outerLeftABC : Matrix (RightIndex 3 4 2) (LeftIndex 4 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 2 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms423
