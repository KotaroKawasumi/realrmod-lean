import RMod.BrundanEllis.StackingReferenceHexagonAtoms424
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms442
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 4 4 2) (LeftIndex 4 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.assocCAB

theorem assocABC_eq : associatorZ 4 4 2 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.assocCAB_eq

def outerABC : Matrix (LeftIndex 4 2 4) (RightIndex 4 4 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 4 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 4 2) (LeftIndex 4 4 2) ℤ := assocABC

theorem assocBAC_eq : associatorZ 4 4 2 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 4 4 2) (LeftIndex 4 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.innerACB

theorem innerABC_eq : innerLeftZ 4 4 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 2 4) (RightIndex 4 4 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 4 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def inverseACB : Matrix (LeftIndex 4 2 4) (RightIndex 4 2 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 2 4 r) []).getD (rightPosition 4 2 4 s) 0

theorem inverseACB_eq : associatorInverseZ 4 2 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 4 4) (LeftIndex 4 2 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.innerABC

theorem innerACB_eq : innerLeftZ 4 2 4 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.innerABC_eq

def assocBCA : Matrix (RightIndex 4 2 4) (LeftIndex 4 2 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.assocABC

theorem assocBCA_eq : associatorZ 4 2 4 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 2 4) (RightIndex 4 4 2) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 4 2 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 2 4 4) (LeftIndex 2 4 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.assocBAC

theorem assocCAB_eq : associatorZ 2 4 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms424.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 2 4 4) (LeftIndex 4 4 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 4 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms442
