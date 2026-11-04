import RMod.BrundanEllis.StackingReferenceHexagonAtoms516
import RMod.BrundanEllis.StackingReferenceHexagonAtoms561
import RMod.BrundanEllis.StackingReferenceHexagonAtoms615
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms651
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 5 1) (LeftIndex 6 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocCAB

theorem assocABC_eq : associatorZ 6 5 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocCAB_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919]

def outerABC : Matrix (LeftIndex 5 1 6) (RightIndex 6 5 1) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 5 1 6 r) []).getD (rightPosition 6 5 1 s) 0

theorem outerABC_eq : outerRightZ 6 5 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 6 1) (LeftIndex 5 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.assocABC

theorem assocBAC_eq : associatorZ 5 6 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.assocABC_eq

def innerABC : Matrix (LeftIndex 5 6 1) (LeftIndex 6 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms615.innerACB

theorem innerABC_eq : innerLeftZ 6 5 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms615.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 1 5) (RightIndex 6 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 5 1 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 22586246,
    decodeIntegerRow 16 3 1 19397598,
    decodeIntegerRow 16 3 1 31089334,
    decodeIntegerRow 16 3 1 2391502,
    decodeIntegerRow 16 3 1 21761014,
    decodeIntegerRow 16 3 1 21408178,
    decodeIntegerRow 16 3 1 21496954,
    decodeIntegerRow 16 3 1 21536158,
    decodeIntegerRow 16 3 1 21497278,
    decodeIntegerRow 16 3 1 21509914,
    decodeIntegerRow 16 3 1 21288622,
    decodeIntegerRow 16 3 1 21402346,
    decodeIntegerRow 16 3 1 11957458,
    decodeIntegerRow 16 3 1 2391466,
    decodeIntegerRow 16 3 1 22586238,
    decodeIntegerRow 16 3 1 23649126]

def inverseACB : Matrix (LeftIndex 6 1 5) (RightIndex 6 1 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 1 5 r) []).getD (rightPosition 6 1 5 s) 0

theorem inverseACB_eq : associatorInverseZ 6 1 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 6 5) (LeftIndex 6 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms615.innerABC

theorem innerACB_eq : innerLeftZ 6 1 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms615.innerABC_eq

def assocBCA : Matrix (RightIndex 5 1 6) (LeftIndex 5 1 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocABC

theorem assocBCA_eq : associatorZ 5 1 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 1 6) (RightIndex 5 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 6 1 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561.innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 6 5) (LeftIndex 1 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocBCA

theorem assocCAB_eq : associatorZ 1 6 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocBCA_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def outerLeftABC : Matrix (RightIndex 1 6 5) (LeftIndex 6 5 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 6 5 r) []).getD (leftPosition 6 5 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 5 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms651
