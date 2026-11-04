import RMod.BrundanEllis.StackingReferenceHexagonAtoms506
import RMod.BrundanEllis.StackingReferenceHexagonAtoms560
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms605
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 0 5) (LeftIndex 6 0 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.assocBCA

theorem assocABC_eq : associatorZ 6 0 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.assocBCA_eq

def outerABC : Matrix (LeftIndex 0 5 6) (RightIndex 6 0 5) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 0 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 0 6 5) (LeftIndex 0 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocBCA

theorem assocBAC_eq : associatorZ 0 6 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocBCA_eq

def innerABC : Matrix (LeftIndex 0 6 5) (LeftIndex 6 0 5) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 0 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 5 0) (RightIndex 6 0 5) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 0 5 = innerRightABC := by
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

def inverseACB : Matrix (LeftIndex 6 5 0) (RightIndex 6 5 0) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 5 0 r) []).getD (rightPosition 6 5 0 s) 0

theorem inverseACB_eq : associatorInverseZ 6 5 0 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 6 0) (LeftIndex 6 5 0) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 6 5 0 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 0 5 6) (LeftIndex 0 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocBAC

theorem assocBCA_eq : associatorZ 0 5 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 0 5 6) (RightIndex 0 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 0 6 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 6 0) (LeftIndex 5 6 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.assocABC

theorem assocCAB_eq : associatorZ 5 6 0 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.assocABC_eq

def outerLeftABC : Matrix (RightIndex 5 6 0) (LeftIndex 6 0 5) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 0 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms605
