import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21346942,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 21529678,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 26306356,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991916]

def assocABC : Matrix (RightIndex 4 1 5) (LeftIndex 4 1 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 1 5 r) []).getD (leftPosition 4 1 5 s) 0

theorem assocABC_eq : associatorZ 4 1 5 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 1 5 4) (RightIndex 4 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 1 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35525032,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 15183192,
    decodeIntegerRow 16 3 1 6814564,
    decodeIntegerRow 16 3 1 6473404,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 36575272,
    decodeIntegerRow 16 3 1 15108996,
    decodeIntegerRow 16 3 1 27859044,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 18253848]

def assocBAC : Matrix (RightIndex 1 4 5) (LeftIndex 1 4 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 4 5 r) []).getD (leftPosition 1 4 5 s) 0

theorem assocBAC_eq : associatorZ 1 4 5 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 4 5) (LeftIndex 4 1 5) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 4 1 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 5 1) (RightIndex 4 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 1 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21529912,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 35872024]

def inverseACB : Matrix (LeftIndex 4 5 1) (RightIndex 4 5 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 5 1 r) []).getD (rightPosition 4 5 1 s) 0

theorem inverseACB_eq : associatorInverseZ 4 5 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 4 1) (LeftIndex 4 5 1) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 4 5 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 35340340,
    decodeIntegerRow 16 3 1 24714112,
    decodeIntegerRow 16 3 1 15148336,
    decodeIntegerRow 16 3 1 6642040,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 36402736,
    decodeIntegerRow 16 3 1 15143800]

def assocBCA : Matrix (RightIndex 1 5 4) (LeftIndex 1 5 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 5 4 r) []).getD (leftPosition 1 5 4 s) 0

theorem assocBCA_eq : associatorZ 1 5 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 5 4) (RightIndex 1 4 5) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 4 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 27942312,
    decodeIntegerRow 16 3 1 36573316,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 15187676,
    decodeIntegerRow 16 3 1 18253848,
    decodeIntegerRow 16 3 1 7522684,
    decodeIntegerRow 16 3 1 15108996,
    decodeIntegerRow 16 3 1 36575272,
    decodeIntegerRow 16 3 1 7890076,
    decodeIntegerRow 16 3 1 24635352,
    decodeIntegerRow 16 3 1 18258116,
    decodeIntegerRow 16 3 1 35525032,
    decodeIntegerRow 16 3 1 36232156,
    decodeIntegerRow 16 3 1 15183192]

def assocCAB : Matrix (RightIndex 5 4 1) (LeftIndex 5 4 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 5 4 1 r) []).getD (leftPosition 5 4 1 s) 0

theorem assocCAB_eq : associatorZ 5 4 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

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

def outerLeftABC : Matrix (RightIndex 5 4 1) (LeftIndex 4 1 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 4 1 r) []).getD (leftPosition 4 1 5 s) 0

theorem outerLeftABC_eq : outerLeftZ 4 1 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415
