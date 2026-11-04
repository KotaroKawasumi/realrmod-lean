import RMod.BrundanEllis.StackingReferenceHexagonAtoms347
import RMod.BrundanEllis.StackingReferenceHexagonAtoms374
import RMod.BrundanEllis.StackingReferenceHexagonAtoms473
import RMod.BrundanEllis.StackingReferenceHexagonAtoms734
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms743
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 4 3) (LeftIndex 7 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocBCA

theorem assocABC_eq : associatorZ 7 4 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 6643012,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 15146068]

def outerABC : Matrix (LeftIndex 4 3 7) (RightIndex 7 4 3) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 4 3 7 r) []).getD (rightPosition 7 4 3 s) 0

theorem outerABC_eq : outerRightZ 7 4 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 7 3) (LeftIndex 4 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBCA

theorem assocBAC_eq : associatorZ 4 7 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBCA_eq

def innerABC : Matrix (LeftIndex 4 7 3) (LeftIndex 7 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms734.innerACB

theorem innerABC_eq : innerLeftZ 7 4 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms734.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 3 4) (RightIndex 7 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms473.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 4 3 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms473.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 36402736,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21339640,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 36404680,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 27902920]

def inverseACB : Matrix (LeftIndex 7 3 4) (RightIndex 7 3 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 3 4 r) []).getD (rightPosition 7 3 4 s) 0

theorem inverseACB_eq : associatorInverseZ 7 3 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 7 4) (LeftIndex 7 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms734.innerABC

theorem innerACB_eq : innerLeftZ 7 3 4 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms734.innerABC_eq

def assocBCA : Matrix (RightIndex 4 3 7) (LeftIndex 4 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBAC

theorem assocBCA_eq : associatorZ 4 3 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 4 3 7) (RightIndex 4 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms473.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 7 3 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms473.innerRightABC_eq

def assocCAB : Matrix (RightIndex 3 7 4) (LeftIndex 3 7 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocABC

theorem assocCAB_eq : associatorZ 3 7 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
    decodeIntegerRow 16 3 1 27824216,
    decodeIntegerRow 16 3 1 24674772,
    decodeIntegerRow 16 3 1 36220984,
    decodeIntegerRow 16 3 1 35169748,
    decodeIntegerRow 16 3 1 15227096,
    decodeIntegerRow 16 3 1 18376212,
    decodeIntegerRow 16 3 1 6827704,
    decodeIntegerRow 16 3 1 27981624,
    decodeIntegerRow 16 3 1 7534828,
    decodeIntegerRow 16 3 1 36588376,
    decodeIntegerRow 16 3 1 24753452,
    decodeIntegerRow 16 3 1 27977144,
    decodeIntegerRow 16 3 1 7535788,
    decodeIntegerRow 16 3 1 36586456,
    decodeIntegerRow 16 3 1 24749292]

def outerLeftABC : Matrix (RightIndex 3 7 4) (LeftIndex 7 4 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 7 4 r) []).getD (leftPosition 7 4 3 s) 0

theorem outerLeftABC_eq : outerLeftZ 7 4 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms743
