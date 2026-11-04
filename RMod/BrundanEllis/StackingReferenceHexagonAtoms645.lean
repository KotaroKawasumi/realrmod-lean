import RMod.BrundanEllis.StackingReferenceHexagonAtoms456
import RMod.BrundanEllis.StackingReferenceHexagonAtoms465
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms645
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 4 5) (LeftIndex 6 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocCAB

theorem assocABC_eq : associatorZ 6 4 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocCAB_eq

def outerABC : Matrix (LeftIndex 4 5 6) (RightIndex 6 4 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 4 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 6 5) (LeftIndex 4 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocABC

theorem assocBAC_eq : associatorZ 4 6 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocABC_eq

def innerABC : Matrix (LeftIndex 4 6 5) (LeftIndex 6 4 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 4 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 5 4) (RightIndex 6 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 4 5 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21562754,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 6643498,
    decodeIntegerRow 16 3 1 15148174,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 21339658]

def inverseACB : Matrix (LeftIndex 6 5 4) (RightIndex 6 5 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 5 4 r) []).getD (rightPosition 6 5 4 s) 0

theorem inverseACB_eq : associatorInverseZ 6 5 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 6 4) (LeftIndex 6 5 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 6 5 4 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 4 5 6) (LeftIndex 4 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocABC

theorem assocBCA_eq : associatorZ 4 5 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 5 6) (RightIndex 4 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 6 5 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 6 4) (LeftIndex 5 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBCA

theorem assocCAB_eq : associatorZ 5 6 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 5 6 4) (LeftIndex 6 4 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 4 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms645
