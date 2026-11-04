import RMod.BrundanEllis.StackingReferenceHexagonAtoms427
import RMod.BrundanEllis.StackingReferenceHexagonAtoms472
import RMod.BrundanEllis.StackingReferenceHexagonAtoms724
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms742
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 4 2) (LeftIndex 7 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocCAB

theorem assocABC_eq : associatorZ 7 4 2 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocCAB_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522848,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21521260,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21521248,
    decodeIntegerRow 16 3 1 21524304,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 6721744,
    decodeIntegerRow 16 3 1 7745260,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 36482440]

def outerABC : Matrix (LeftIndex 4 2 7) (RightIndex 7 4 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 4 2 7 r) []).getD (rightPosition 7 4 2 s) 0

theorem outerABC_eq : outerRightZ 7 4 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 7 2) (LeftIndex 4 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.assocABC

theorem assocBAC_eq : associatorZ 4 7 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.assocABC_eq

def innerABC : Matrix (LeftIndex 4 7 2) (LeftIndex 7 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms724.innerACB

theorem innerABC_eq : innerLeftZ 7 4 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms724.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 2 4) (RightIndex 7 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 4 2 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 24880480,
    decodeIntegerRow 16 3 1 36324032,
    decodeIntegerRow 16 3 1 35301000,
    decodeIntegerRow 16 3 1 14964640,
    decodeIntegerRow 16 3 1 35379680,
    decodeIntegerRow 16 3 1 15332032,
    decodeIntegerRow 16 3 1 18507400,
    decodeIntegerRow 16 3 1 6565280,
    decodeIntegerRow 16 3 1 35380704,
    decodeIntegerRow 16 3 1 27719200,
    decodeIntegerRow 16 3 1 24543520,
    decodeIntegerRow 16 3 1 6563280,
    decodeIntegerRow 16 3 1 24884704,
    decodeIntegerRow 16 3 1 6720800,
    decodeIntegerRow 16 3 1 7744800,
    decodeIntegerRow 16 3 1 14960080]

def inverseACB : Matrix (LeftIndex 7 2 4) (RightIndex 7 2 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 2 4 r) []).getD (rightPosition 7 2 4 s) 0

theorem inverseACB_eq : associatorInverseZ 7 2 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 7 4) (LeftIndex 7 2 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms724.innerABC

theorem innerACB_eq : innerLeftZ 7 2 4 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms724.innerABC_eq

def assocBCA : Matrix (RightIndex 4 2 7) (LeftIndex 4 2 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocABC

theorem assocBCA_eq : associatorZ 4 2 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 2 7) (RightIndex 4 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 7 2 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.innerRightABC_eq

def assocCAB : Matrix (RightIndex 2 7 4) (LeftIndex 2 7 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocBCA

theorem assocCAB_eq : associatorZ 2 7 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 2 7 4) (LeftIndex 7 4 2) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 4 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms742
