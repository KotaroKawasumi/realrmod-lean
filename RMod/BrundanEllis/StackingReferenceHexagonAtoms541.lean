import RMod.BrundanEllis.StackingReferenceHexagonAtoms415
import RMod.BrundanEllis.StackingReferenceHexagonAtoms451
import RMod.BrundanEllis.StackingReferenceHexagonAtoms514
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms541
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 4 1) (LeftIndex 5 4 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocCAB

theorem assocABC_eq : associatorZ 5 4 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocCAB_eq

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

def outerABC : Matrix (LeftIndex 4 1 5) (RightIndex 5 4 1) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 4 1 5 r) []).getD (rightPosition 5 4 1 s) 0

theorem outerABC_eq : outerRightZ 5 4 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 5 1) (LeftIndex 4 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.assocABC

theorem assocBAC_eq : associatorZ 4 5 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.assocABC_eq

def innerABC : Matrix (LeftIndex 4 5 1) (LeftIndex 5 4 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms514.innerACB

theorem innerABC_eq : innerLeftZ 5 4 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms514.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 1 4) (RightIndex 5 4 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.innerRightBAC

theorem innerRightABC_eq : innerRightZ 5 4 1 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21560458,
    decodeIntegerRow 16 3 1 21351802,
    decodeIntegerRow 16 3 1 21339166,
    decodeIntegerRow 16 3 1 21599986,
    decodeIntegerRow 16 3 1 21353746,
    decodeIntegerRow 16 3 1 21481726,
    decodeIntegerRow 16 3 1 21604198,
    decodeIntegerRow 16 3 1 21706582,
    decodeIntegerRow 16 3 1 7705882,
    decodeIntegerRow 16 3 1 18334742,
    decodeIntegerRow 16 3 1 27900626,
    decodeIntegerRow 16 3 1 36403714,
    decodeIntegerRow 16 3 1 18334686,
    decodeIntegerRow 16 3 1 35340814,
    decodeIntegerRow 16 3 1 36403702,
    decodeIntegerRow 16 3 1 15146042]

def inverseACB : Matrix (LeftIndex 5 1 4) (RightIndex 5 1 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 1 4 r) []).getD (rightPosition 5 1 4 s) 0

theorem inverseACB_eq : associatorInverseZ 5 1 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 5 4) (LeftIndex 5 1 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms514.innerABC

theorem innerACB_eq : innerLeftZ 5 1 4 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms514.innerABC_eq

def assocBCA : Matrix (RightIndex 4 1 5) (LeftIndex 4 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocABC

theorem assocBCA_eq : associatorZ 4 1 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 1 5) (RightIndex 4 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 5 1 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 5 4) (LeftIndex 1 5 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocBCA

theorem assocCAB_eq : associatorZ 1 5 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocBCA_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523348,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21522388,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21602092,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 6643012,
    decodeIntegerRow 16 3 1 27900652]

def outerLeftABC : Matrix (RightIndex 1 5 4) (LeftIndex 5 4 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 5 4 r) []).getD (leftPosition 5 4 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 5 4 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms541
