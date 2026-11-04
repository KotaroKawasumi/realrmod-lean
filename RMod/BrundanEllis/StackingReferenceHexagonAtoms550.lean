import RMod.BrundanEllis.StackingReferenceHexagonAtoms505
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms550
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 5 0) (LeftIndex 5 5 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.assocCAB

theorem assocABC_eq : associatorZ 5 5 0 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.assocCAB_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36575260,
    decodeIntegerRow 16 3 1 27937776,
    decodeIntegerRow 16 3 1 24635408,
    decodeIntegerRow 16 3 1 35156620,
    decodeIntegerRow 16 3 1 35157616,
    decodeIntegerRow 16 3 1 24631140,
    decodeIntegerRow 16 3 1 15104460,
    decodeIntegerRow 16 3 1 6473392,
    decodeIntegerRow 16 3 1 18253904,
    decodeIntegerRow 16 3 1 35524060,
    decodeIntegerRow 16 3 1 36234100,
    decodeIntegerRow 16 3 1 15187728,
    decodeIntegerRow 16 3 1 27863580,
    decodeIntegerRow 16 3 1 6814576,
    decodeIntegerRow 16 3 1 35525008,
    decodeIntegerRow 16 3 1 18258060]

def outerABC : Matrix (LeftIndex 5 0 5) (RightIndex 5 5 0) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 5 0 5 r) []).getD (rightPosition 5 5 0 s) 0

theorem outerABC_eq : outerRightZ 5 5 0 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 5 0) (LeftIndex 5 5 0) ℤ := assocABC

theorem assocBAC_eq : associatorZ 5 5 0 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 5 5 0) (LeftIndex 5 5 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.innerACB

theorem innerABC_eq : innerLeftZ 5 5 0 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 0 5) (RightIndex 5 5 0) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 5 0 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def inverseACB : Matrix (LeftIndex 5 0 5) (RightIndex 5 0 5) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem inverseACB_eq : associatorInverseZ 5 0 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 0 5 5) (LeftIndex 5 0 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.innerABC

theorem innerACB_eq : innerLeftZ 5 0 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.innerABC_eq

def assocBCA : Matrix (RightIndex 5 0 5) (LeftIndex 5 0 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.assocABC

theorem assocBCA_eq : associatorZ 5 0 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 0 5) (RightIndex 5 5 0) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 5 0 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 0 5 5) (LeftIndex 0 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.assocBAC

theorem assocCAB_eq : associatorZ 0 5 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms505.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 0 5 5) (LeftIndex 5 5 0) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 5 0 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms550
