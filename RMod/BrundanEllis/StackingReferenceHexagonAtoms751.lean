import RMod.BrundanEllis.StackingReferenceHexagonAtoms517
import RMod.BrundanEllis.StackingReferenceHexagonAtoms571
import RMod.BrundanEllis.StackingReferenceHexagonAtoms715
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms751
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 5 1) (LeftIndex 7 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocCAB

theorem assocABC_eq : associatorZ 7 5 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocCAB_eq

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

def outerABC : Matrix (LeftIndex 5 1 7) (RightIndex 7 5 1) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 5 1 7 r) []).getD (rightPosition 7 5 1 s) 0

theorem outerABC_eq : outerRightZ 7 5 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 7 1) (LeftIndex 5 7 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.assocABC

theorem assocBAC_eq : associatorZ 5 7 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.assocABC_eq

def innerABC : Matrix (LeftIndex 5 7 1) (LeftIndex 7 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms715.innerACB

theorem innerABC_eq : innerLeftZ 7 5 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms715.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 1 5) (RightIndex 7 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 5 1 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.innerRightBAC_eq

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

def inverseACB : Matrix (LeftIndex 7 1 5) (RightIndex 7 1 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 1 5 r) []).getD (rightPosition 7 1 5 s) 0

theorem inverseACB_eq : associatorInverseZ 7 1 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 7 5) (LeftIndex 7 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms715.innerABC

theorem innerACB_eq : innerLeftZ 7 1 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms715.innerABC_eq

def assocBCA : Matrix (RightIndex 5 1 7) (LeftIndex 5 1 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocABC

theorem assocBCA_eq : associatorZ 5 1 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 1 7) (RightIndex 5 7 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 7 1 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 7 5) (LeftIndex 1 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocBCA

theorem assocCAB_eq : associatorZ 1 7 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 1 7 5) (LeftIndex 7 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 5 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms751
