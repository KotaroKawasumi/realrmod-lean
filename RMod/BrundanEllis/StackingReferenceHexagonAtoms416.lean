import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 7705408,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21484020,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21602064,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 36404680]

def assocABC : Matrix (RightIndex 4 1 6) (LeftIndex 4 1 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 1 6 r) []).getD (leftPosition 4 1 6 s) 0

theorem assocABC_eq : associatorZ 4 1 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 1 6 4) (RightIndex 4 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 1 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 24880336,
    decodeIntegerRow 16 3 1 35381136,
    decodeIntegerRow 16 3 1 36325488,
    decodeIntegerRow 16 3 1 27714832,
    decodeIntegerRow 16 3 1 35302460,
    decodeIntegerRow 16 3 1 24539140,
    decodeIntegerRow 16 3 1 14964460,
    decodeIntegerRow 16 3 1 6563820,
    decodeIntegerRow 16 3 1 36481980,
    decodeIntegerRow 16 3 1 14960260,
    decodeIntegerRow 16 3 1 18503020,
    decodeIntegerRow 16 3 1 35300460,
    decodeIntegerRow 16 3 1 27719056,
    decodeIntegerRow 16 3 1 6722256,
    decodeIntegerRow 16 3 1 35379248,
    decodeIntegerRow 16 3 1 18161872]

def assocBAC : Matrix (RightIndex 1 4 6) (LeftIndex 1 4 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 4 6 r) []).getD (leftPosition 1 4 6 s) 0

theorem assocBAC_eq : associatorZ 1 4 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 4 6) (LeftIndex 4 1 6) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 4 1 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 6 1) (RightIndex 4 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 1 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21503920,
    decodeIntegerRow 16 3 1 21465040,
    decodeIntegerRow 16 3 1 21344026,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 20991918,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 21529840,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21698320]

def inverseACB : Matrix (LeftIndex 4 6 1) (RightIndex 4 6 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 6 1 r) []).getD (rightPosition 4 6 1 s) 0

theorem inverseACB_eq : associatorInverseZ 4 6 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 4 1) (LeftIndex 4 6 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 4 6 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 18162016,
    decodeIntegerRow 16 3 1 7667040,
    decodeIntegerRow 16 3 1 6720800,
    decodeIntegerRow 16 3 1 15332032,
    decodeIntegerRow 16 3 1 7744800,
    decodeIntegerRow 16 3 1 18507400,
    decodeIntegerRow 16 3 1 28086640,
    decodeIntegerRow 16 3 1 36481440,
    decodeIntegerRow 16 3 1 7666016,
    decodeIntegerRow 16 3 1 24880480,
    decodeIntegerRow 16 3 1 15327520,
    decodeIntegerRow 16 3 1 36324032,
    decodeIntegerRow 16 3 1 18503200,
    decodeIntegerRow 16 3 1 35301000,
    decodeIntegerRow 16 3 1 36483440,
    decodeIntegerRow 16 3 1 14964640]

def assocBCA : Matrix (RightIndex 1 6 4) (LeftIndex 1 6 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 6 4 r) []).getD (leftPosition 1 6 4 s) 0

theorem assocBCA_eq : associatorZ 1 6 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 6 4) (RightIndex 1 4 6) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 4 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 7174452,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 19929028,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21700426,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 21700588,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21543772,
    decodeIntegerRow 16 3 1 21518986]

def assocCAB : Matrix (RightIndex 6 4 1) (LeftIndex 6 4 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 4 1 r) []).getD (leftPosition 6 4 1 s) 0

theorem assocCAB_eq : associatorZ 6 4 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 6 4 1) (LeftIndex 4 1 6) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 1 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416
