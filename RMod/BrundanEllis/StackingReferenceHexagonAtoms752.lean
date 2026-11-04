import RMod.BrundanEllis.StackingReferenceHexagonAtoms527
import RMod.BrundanEllis.StackingReferenceHexagonAtoms572
import RMod.BrundanEllis.StackingReferenceHexagonAtoms725
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms752
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 5 2) (LeftIndex 7 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocCAB

theorem assocABC_eq : associatorZ 7 5 2 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocCAB_eq

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

def outerABC : Matrix (LeftIndex 5 2 7) (RightIndex 7 5 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 5 2 7 r) []).getD (rightPosition 7 5 2 s) 0

theorem outerABC_eq : outerRightZ 7 5 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 7 2) (LeftIndex 5 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.assocABC

theorem assocBAC_eq : associatorZ 5 7 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.assocABC_eq

def innerABC : Matrix (LeftIndex 5 7 2) (LeftIndex 7 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms725.innerACB

theorem innerABC_eq : innerLeftZ 7 5 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms725.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 2 5) (RightIndex 7 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 5 2 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35169748,
    decodeIntegerRow 16 3 1 15227096,
    decodeIntegerRow 16 3 1 18376212,
    decodeIntegerRow 16 3 1 6827704,
    decodeIntegerRow 16 3 1 24753452,
    decodeIntegerRow 16 3 1 6458344,
    decodeIntegerRow 16 3 1 7534828,
    decodeIntegerRow 16 3 1 15065096,
    decodeIntegerRow 16 3 1 18371948,
    decodeIntegerRow 16 3 1 36220984,
    decodeIntegerRow 16 3 1 35170732,
    decodeIntegerRow 16 3 1 27824216,
    decodeIntegerRow 16 3 1 7535788,
    decodeIntegerRow 16 3 1 27977144,
    decodeIntegerRow 16 3 1 24749292,
    decodeIntegerRow 16 3 1 36586456]

def inverseACB : Matrix (LeftIndex 7 2 5) (RightIndex 7 2 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 2 5 r) []).getD (rightPosition 7 2 5 s) 0

theorem inverseACB_eq : associatorInverseZ 7 2 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 7 5) (LeftIndex 7 2 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms725.innerABC

theorem innerACB_eq : innerLeftZ 7 2 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms725.innerABC_eq

def assocBCA : Matrix (RightIndex 5 2 7) (LeftIndex 5 2 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocABC

theorem assocBCA_eq : associatorZ 5 2 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 2 7) (RightIndex 5 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 7 2 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.innerRightABC_eq

def assocCAB : Matrix (RightIndex 2 7 5) (LeftIndex 2 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocBCA

theorem assocCAB_eq : associatorZ 2 7 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 2 7 5) (LeftIndex 7 5 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 5 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms752
