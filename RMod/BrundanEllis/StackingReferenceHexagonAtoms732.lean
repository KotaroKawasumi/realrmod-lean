import RMod.BrundanEllis.StackingReferenceHexagonAtoms327
import RMod.BrundanEllis.StackingReferenceHexagonAtoms372
import RMod.BrundanEllis.StackingReferenceHexagonAtoms723
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms732
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 3 2) (LeftIndex 7 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocCAB

theorem assocABC_eq : associatorZ 7 3 2 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocCAB_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def outerABC : Matrix (LeftIndex 3 2 7) (RightIndex 7 3 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 3 2 7 r) []).getD (rightPosition 7 3 2 s) 0

theorem outerABC_eq : outerRightZ 7 3 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 7 2) (LeftIndex 3 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.assocABC

theorem assocBAC_eq : associatorZ 3 7 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.assocABC_eq

def innerABC : Matrix (LeftIndex 3 7 2) (LeftIndex 7 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms723.innerACB

theorem innerABC_eq : innerLeftZ 7 3 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms723.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 2 3) (RightIndex 7 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 3 2 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 24712034,
    decodeIntegerRow 16 3 1 7705906,
    decodeIntegerRow 16 3 1 6643018,
    decodeIntegerRow 16 3 1 27900678,
    decodeIntegerRow 16 3 1 21604198,
    decodeIntegerRow 16 3 1 21340138,
    decodeIntegerRow 16 3 1 21692974,
    decodeIntegerRow 16 3 1 21481726,
    decodeIntegerRow 16 3 1 21599986,
    decodeIntegerRow 16 3 1 21339166,
    decodeIntegerRow 16 3 1 21694918,
    decodeIntegerRow 16 3 1 21486262,
    decodeIntegerRow 16 3 1 24711978,
    decodeIntegerRow 16 3 1 7705882,
    decodeIntegerRow 16 3 1 6643006,
    decodeIntegerRow 16 3 1 27900626]

def inverseACB : Matrix (LeftIndex 7 2 3) (RightIndex 7 2 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 2 3 r) []).getD (rightPosition 7 2 3 s) 0

theorem inverseACB_eq : associatorInverseZ 7 2 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 7 3) (LeftIndex 7 2 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms723.innerABC

theorem innerACB_eq : innerLeftZ 7 2 3 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms723.innerABC_eq

def assocBCA : Matrix (RightIndex 3 2 7) (LeftIndex 3 2 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocABC

theorem assocBCA_eq : associatorZ 3 2 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 2 7) (RightIndex 3 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 7 2 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms372.innerRightABC_eq

def assocCAB : Matrix (RightIndex 2 7 3) (LeftIndex 2 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocBCA

theorem assocCAB_eq : associatorZ 2 7 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327.assocBCA_eq

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

def outerLeftABC : Matrix (RightIndex 2 7 3) (LeftIndex 7 3 2) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 2 7 3 r) []).getD (leftPosition 7 3 2 s) 0

theorem outerLeftABC_eq : outerLeftZ 7 3 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms732
