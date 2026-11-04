import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507]

def assocABC : Matrix (RightIndex 5 6 7) (LeftIndex 5 6 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 6 7 r) []).getD (leftPosition 5 6 7 s) 0

theorem assocABC_eq : associatorZ 5 6 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

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

def outerABC : Matrix (LeftIndex 6 7 5) (RightIndex 5 6 7) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 6 7 5 r) []).getD (rightPosition 5 6 7 s) 0

theorem outerABC_eq : outerRightZ 5 6 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21562754,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 21707074,
    decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 36404194]

def assocBAC : Matrix (RightIndex 6 5 7) (LeftIndex 6 5 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 6 5 7 r) []).getD (leftPosition 6 5 7 s) 0

theorem assocBAC_eq : associatorZ 6 5 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 6 5 7) (LeftIndex 5 6 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 6 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 24712034,
    decodeIntegerRow 16 3 1 7705906,
    decodeIntegerRow 16 3 1 6643018,
    decodeIntegerRow 16 3 1 27900678,
    decodeIntegerRow 16 3 1 21442522,
    decodeIntegerRow 16 3 1 21706582,
    decodeIntegerRow 16 3 1 21353746,
    decodeIntegerRow 16 3 1 21564994,
    decodeIntegerRow 16 3 1 21351802,
    decodeIntegerRow 16 3 1 21486262,
    decodeIntegerRow 16 3 1 21599986,
    decodeIntegerRow 16 3 1 21707554,
    decodeIntegerRow 16 3 1 36403714,
    decodeIntegerRow 16 3 1 27900626,
    decodeIntegerRow 16 3 1 24711978,
    decodeIntegerRow 16 3 1 35340838]

def innerRightABC : Matrix (RightIndex 5 7 6) (RightIndex 5 6 7) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 5 7 6 r) []).getD (rightPosition 5 6 7 s) 0

theorem innerRightABC_eq : innerRightZ 5 6 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547]

def inverseACB : Matrix (LeftIndex 5 7 6) (RightIndex 5 7 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 7 6 r) []).getD (rightPosition 5 7 6 s) 0

theorem inverseACB_eq : associatorInverseZ 5 7 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 5 6) (LeftIndex 5 7 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 7 6 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 23117682,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 22054798,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21543124,
    decodeIntegerRow 16 3 1 21530164,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21699778]

def assocBCA : Matrix (RightIndex 6 7 5) (LeftIndex 6 7 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 7 5 r) []).getD (leftPosition 6 7 5 s) 0

theorem assocBCA_eq : associatorZ 6 7 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 7 5) (RightIndex 6 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 5 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 6642040,
    decodeIntegerRow 16 3 1 15148336,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 7706380]

def assocCAB : Matrix (RightIndex 7 5 6) (LeftIndex 7 5 6) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 5 6 r) []).getD (leftPosition 7 5 6 s) 0

theorem assocCAB_eq : associatorZ 7 5 6 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

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

def outerLeftABC : Matrix (RightIndex 7 5 6) (LeftIndex 5 6 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 5 6 r) []).getD (leftPosition 5 6 7 s) 0

theorem outerLeftABC_eq : outerLeftZ 5 6 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567
