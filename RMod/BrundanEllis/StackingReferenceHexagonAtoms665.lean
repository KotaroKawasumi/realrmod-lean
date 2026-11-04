import RMod.BrundanEllis.StackingReferenceHexagonAtoms566
import RMod.BrundanEllis.StackingReferenceHexagonAtoms656
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms665
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 6 5) (LeftIndex 6 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocBCA

theorem assocABC_eq : associatorZ 6 6 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocBCA_eq

def outerABC : Matrix (LeftIndex 6 5 6) (RightIndex 6 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 6 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 6 5) (LeftIndex 6 6 5) ℤ := assocABC

theorem assocBAC_eq : associatorZ 6 6 5 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 6 6 5) (LeftIndex 6 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms656.innerACB

theorem innerABC_eq : innerLeftZ 6 6 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms656.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 5 6) (RightIndex 6 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 6 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 22072288,
    decodeIntegerRow 16 3 1 23111824,
    decodeIntegerRow 16 3 1 26128940,
    decodeIntegerRow 16 3 1 35931400,
    decodeIntegerRow 16 3 1 19921720,
    decodeIntegerRow 16 3 1 22032940,
    decodeIntegerRow 16 3 1 35813296,
    decodeIntegerRow 16 3 1 16563488,
    decodeIntegerRow 16 3 1 7115488,
    decodeIntegerRow 16 3 1 26129424,
    decodeIntegerRow 16 3 1 19936300,
    decodeIntegerRow 16 3 1 22076680,
    decodeIntegerRow 16 3 1 16563000,
    decodeIntegerRow 16 3 1 7233580,
    decodeIntegerRow 16 3 1 22037296,
    decodeIntegerRow 16 3 1 23123488]

def inverseACB : Matrix (LeftIndex 6 5 6) (RightIndex 6 5 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 5 6 r) []).getD (rightPosition 6 5 6 s) 0

theorem inverseACB_eq : associatorInverseZ 6 5 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 6 6) (LeftIndex 6 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms656.innerABC

theorem innerACB_eq : innerLeftZ 6 5 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms656.innerABC_eq

def assocBCA : Matrix (RightIndex 6 5 6) (LeftIndex 6 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocBAC

theorem assocBCA_eq : associatorZ 6 5 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 6 5 6) (RightIndex 6 6 5) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 6 6 5 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 6 6) (LeftIndex 5 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocABC

theorem assocCAB_eq : associatorZ 5 6 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocABC_eq

def outerLeftABC : Matrix (RightIndex 5 6 6) (LeftIndex 6 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 6 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms665
