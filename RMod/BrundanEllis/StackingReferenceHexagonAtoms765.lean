import RMod.BrundanEllis.StackingReferenceHexagonAtoms567
import RMod.BrundanEllis.StackingReferenceHexagonAtoms576
import RMod.BrundanEllis.StackingReferenceHexagonAtoms675
import RMod.BrundanEllis.StackingReferenceHexagonAtoms756
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms765
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 6 5) (LeftIndex 7 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocBCA

theorem assocABC_eq : associatorZ 7 6 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def outerABC : Matrix (LeftIndex 6 5 7) (RightIndex 7 6 5) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 6 5 7 r) []).getD (rightPosition 7 6 5 s) 0

theorem outerABC_eq : outerRightZ 7 6 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 7 5) (LeftIndex 6 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBCA

theorem assocBAC_eq : associatorZ 6 7 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBCA_eq

def innerABC : Matrix (LeftIndex 6 7 5) (LeftIndex 7 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms756.innerACB

theorem innerABC_eq : innerLeftZ 7 6 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms756.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 5 6) (RightIndex 7 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms675.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 6 5 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms675.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21707074,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 35339854,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 6643498]

def inverseACB : Matrix (LeftIndex 7 5 6) (RightIndex 7 5 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 5 6 r) []).getD (rightPosition 7 5 6 s) 0

theorem inverseACB_eq : associatorInverseZ 7 5 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 7 6) (LeftIndex 7 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms756.innerABC

theorem innerACB_eq : innerLeftZ 7 5 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms756.innerABC_eq

def assocBCA : Matrix (RightIndex 6 5 7) (LeftIndex 6 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBAC

theorem assocBCA_eq : associatorZ 6 5 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 6 5 7) (RightIndex 6 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms675.innerRightABC

theorem innerRightBAC_eq : innerRightZ 6 7 5 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms675.innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 7 6) (LeftIndex 5 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocABC

theorem assocCAB_eq : associatorZ 5 7 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36575260,
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

def outerLeftABC : Matrix (RightIndex 5 7 6) (LeftIndex 7 6 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 7 6 r) []).getD (leftPosition 7 6 5 s) 0

theorem outerLeftABC_eq : outerLeftZ 7 6 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms765
