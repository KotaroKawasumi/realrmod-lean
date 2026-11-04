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
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms546
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 4 6) (LeftIndex 5 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBAC

theorem assocABC_eq : associatorZ 5 4 6 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBAC_eq

def outerABC : Matrix (LeftIndex 4 6 5) (RightIndex 5 4 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 4 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 5 6) (LeftIndex 4 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocABC

theorem assocBAC_eq : associatorZ 4 5 6 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocABC_eq

def innerABC : Matrix (LeftIndex 4 5 6) (LeftIndex 5 4 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 4 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 6 4) (RightIndex 5 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.innerRightBAC

theorem innerRightABC_eq : innerRightZ 5 4 6 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26328200,
    decodeIntegerRow 16 3 1 35879560,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 23176840,
    decodeIntegerRow 16 3 1 22232200,
    decodeIntegerRow 16 3 1 19988032,
    decodeIntegerRow 16 3 1 21168832,
    decodeIntegerRow 16 3 1 35864980,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 35878096,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 21877420,
    decodeIntegerRow 16 3 1 23058580,
    decodeIntegerRow 16 3 1 20815024,
    decodeIntegerRow 16 3 1 19870096]

def inverseACB : Matrix (LeftIndex 5 6 4) (RightIndex 5 6 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 6 4 r) []).getD (rightPosition 5 6 4 s) 0

theorem inverseACB_eq : associatorInverseZ 5 6 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 5 4) (LeftIndex 5 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 6 4 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 4 6 5) (LeftIndex 4 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocABC

theorem assocBCA_eq : associatorZ 4 6 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 6 5) (RightIndex 4 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 5 6 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.innerRightABC_eq

def assocCAB : Matrix (RightIndex 6 5 4) (LeftIndex 6 5 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocBCA

theorem assocCAB_eq : associatorZ 6 5 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 6 5 4) (LeftIndex 5 4 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 4 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms546
