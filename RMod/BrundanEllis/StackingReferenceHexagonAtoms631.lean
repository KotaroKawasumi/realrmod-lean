import RMod.BrundanEllis.StackingReferenceHexagonAtoms316
import RMod.BrundanEllis.StackingReferenceHexagonAtoms361
import RMod.BrundanEllis.StackingReferenceHexagonAtoms613
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms631
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 3 1) (LeftIndex 6 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocCAB

theorem assocABC_eq : associatorZ 6 3 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocCAB_eq

def outerABC : Matrix (LeftIndex 3 1 6) (RightIndex 6 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 3 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 6 1) (LeftIndex 3 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.assocABC

theorem assocBAC_eq : associatorZ 3 6 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.assocABC_eq

def innerABC : Matrix (LeftIndex 3 6 1) (LeftIndex 6 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms613.innerACB

theorem innerABC_eq : innerLeftZ 6 3 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms613.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 1 3) (RightIndex 6 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 3 1 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18148888,
    decodeIntegerRow 16 3 1 35261636,
    decodeIntegerRow 16 3 1 36365288,
    decodeIntegerRow 16 3 1 14977756,
    decodeIntegerRow 16 3 1 35419044,
    decodeIntegerRow 16 3 1 24530392,
    decodeIntegerRow 16 3 1 15318916,
    decodeIntegerRow 16 3 1 6602648,
    decodeIntegerRow 16 3 1 36442076,
    decodeIntegerRow 16 3 1 27732328,
    decodeIntegerRow 16 3 1 24526204,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 14973208,
    decodeIntegerRow 16 3 1 36363396,
    decodeIntegerRow 16 3 1 7784168,
    decodeIntegerRow 16 3 1 24893596]

def inverseACB : Matrix (LeftIndex 6 1 3) (RightIndex 6 1 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 1 3 r) []).getD (rightPosition 6 1 3 s) 0

theorem inverseACB_eq : associatorInverseZ 6 1 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 6 3) (LeftIndex 6 1 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms613.innerABC

theorem innerACB_eq : innerLeftZ 6 1 3 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms613.innerABC_eq

def assocBCA : Matrix (RightIndex 3 1 6) (LeftIndex 3 1 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocABC

theorem assocBCA_eq : associatorZ 3 1 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 1 6) (RightIndex 3 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 6 1 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 6 3) (LeftIndex 1 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocBCA

theorem assocCAB_eq : associatorZ 1 6 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocBCA_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523366,
    decodeIntegerRow 16 3 1 21523334,
    decodeIntegerRow 16 3 1 21523332,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21523846,
    decodeIntegerRow 16 3 1 21521254,
    decodeIntegerRow 16 3 1 21521092,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21483994,
    decodeIntegerRow 16 3 1 21693946,
    decodeIntegerRow 16 3 1 21707068,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 18334714,
    decodeIntegerRow 16 3 1 35340826,
    decodeIntegerRow 16 3 1 36403708,
    decodeIntegerRow 16 3 1 15146068]

def outerLeftABC : Matrix (RightIndex 1 6 3) (LeftIndex 6 3 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 6 3 r) []).getD (leftPosition 6 3 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 3 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms631
