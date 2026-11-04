import RMod.BrundanEllis.StackingReferenceHexagonAtoms426
import RMod.BrundanEllis.StackingReferenceHexagonAtoms462
import RMod.BrundanEllis.StackingReferenceHexagonAtoms624
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms642
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 4 2) (LeftIndex 6 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocCAB

theorem assocABC_eq : associatorZ 6 4 2 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocCAB_eq

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

def outerABC : Matrix (LeftIndex 4 2 6) (RightIndex 6 4 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 4 2 6 r) []).getD (rightPosition 6 4 2 s) 0

theorem outerABC_eq : outerRightZ 6 4 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 6 2) (LeftIndex 4 6 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.assocABC

theorem assocBAC_eq : associatorZ 4 6 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.assocABC_eq

def innerABC : Matrix (LeftIndex 4 6 2) (LeftIndex 6 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms624.innerACB

theorem innerABC_eq : innerLeftZ 6 4 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms624.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 2 4) (RightIndex 6 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 4 2 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21346942,
    decodeIntegerRow 16 3 1 21462124,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21530164,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21543124,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 23117684,
    decodeIntegerRow 16 3 1 22054798,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929038]

def inverseACB : Matrix (LeftIndex 6 2 4) (RightIndex 6 2 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 2 4 r) []).getD (rightPosition 6 2 4 s) 0

theorem inverseACB_eq : associatorInverseZ 6 2 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 6 4) (LeftIndex 6 2 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms624.innerABC

theorem innerACB_eq : innerLeftZ 6 2 4 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms624.innerABC_eq

def assocBCA : Matrix (RightIndex 4 2 6) (LeftIndex 4 2 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocABC

theorem assocBCA_eq : associatorZ 4 2 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 2 6) (RightIndex 4 6 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 6 2 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462.innerRightABC_eq

def assocCAB : Matrix (RightIndex 2 6 4) (LeftIndex 2 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocBCA

theorem assocCAB_eq : associatorZ 2 6 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocBCA_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 23117683]

def outerLeftABC : Matrix (RightIndex 2 6 4) (LeftIndex 6 4 2) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 2 6 4 r) []).getD (leftPosition 6 4 2 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 4 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms642
