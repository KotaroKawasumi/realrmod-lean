import RMod.BrundanEllis.StackingReferenceHexagonAtoms506
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560
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

def assocABC : Matrix (RightIndex 5 6 0) (LeftIndex 5 6 0) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 6 0 r) []).getD (leftPosition 5 6 0 s) 0

theorem assocABC_eq : associatorZ 5 6 0 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 6 0 5) (RightIndex 5 6 0) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 6 0 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 5 0) (LeftIndex 6 5 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocCAB

theorem assocBAC_eq : associatorZ 6 5 0 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 5 0) (LeftIndex 5 6 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.innerACB

theorem innerABC_eq : innerLeftZ 5 6 0 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 0 6) (RightIndex 5 6 0) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 6 0 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def inverseACB : Matrix (LeftIndex 5 0 6) (RightIndex 5 0 6) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem inverseACB_eq : associatorInverseZ 5 0 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 0 5 6) (LeftIndex 5 0 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.innerABC

theorem innerACB_eq : innerLeftZ 5 0 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.innerABC_eq

def assocBCA : Matrix (RightIndex 6 0 5) (LeftIndex 6 0 5) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem assocBCA_eq : associatorZ 6 0 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 0 5) (RightIndex 6 5 0) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 5 0 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 0 5 6) (LeftIndex 0 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocBAC

theorem assocCAB_eq : associatorZ 0 5 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 0 5 6) (LeftIndex 5 6 0) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 6 0 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560
