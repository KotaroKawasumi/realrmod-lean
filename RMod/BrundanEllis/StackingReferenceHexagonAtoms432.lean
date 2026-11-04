import RMod.BrundanEllis.StackingReferenceHexagonAtoms324
import RMod.BrundanEllis.StackingReferenceHexagonAtoms342
import RMod.BrundanEllis.StackingReferenceHexagonAtoms423
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms432
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 4 3 2) (LeftIndex 4 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocCAB

theorem assocABC_eq : associatorZ 4 3 2 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocCAB_eq

def outerABC : Matrix (LeftIndex 3 2 4) (RightIndex 4 3 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 3 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 4 2) (LeftIndex 3 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.assocABC

theorem assocBAC_eq : associatorZ 3 4 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.assocABC_eq

def innerABC : Matrix (LeftIndex 3 4 2) (LeftIndex 4 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms423.innerACB

theorem innerABC_eq : innerLeftZ 4 3 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms423.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 2 3) (RightIndex 4 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.innerRightBAC

theorem innerRightABC_eq : innerRightZ 4 3 2 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 21465040,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 21344026,
    decodeIntegerRow 16 3 1 21583138,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 22054800,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 21503920,
    decodeIntegerRow 16 3 1 21529840,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 23117686,
    decodeIntegerRow 16 3 1 20991918]

def inverseACB : Matrix (LeftIndex 4 2 3) (RightIndex 4 2 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 2 3 r) []).getD (rightPosition 4 2 3 s) 0

theorem inverseACB_eq : associatorInverseZ 4 2 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 4 3) (LeftIndex 4 2 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms423.innerABC

theorem innerACB_eq : innerLeftZ 4 2 3 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms423.innerABC_eq

def assocBCA : Matrix (RightIndex 3 2 4) (LeftIndex 3 2 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocABC

theorem assocBCA_eq : associatorZ 3 2 4 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 2 4) (RightIndex 3 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 4 2 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342.innerRightABC_eq

def assocCAB : Matrix (RightIndex 2 4 3) (LeftIndex 2 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocBCA

theorem assocCAB_eq : associatorZ 2 4 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 2 4 3) (LeftIndex 4 3 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 3 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms432
