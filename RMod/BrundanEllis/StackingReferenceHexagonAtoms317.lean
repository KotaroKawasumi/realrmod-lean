import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35813974,
    decodeIntegerRow 16 3 1 16919734,
    decodeIntegerRow 16 3 1 23124322,
    decodeIntegerRow 16 3 1 20972478,
    decodeIntegerRow 16 3 1 16565422,
    decodeIntegerRow 16 3 1 35932018,
    decodeIntegerRow 16 3 1 22034874,
    decodeIntegerRow 16 3 1 19935514,
    decodeIntegerRow 16 3 1 23111038,
    decodeIntegerRow 16 3 1 22035362,
    decodeIntegerRow 16 3 1 7116106,
    decodeIntegerRow 16 3 1 16561066,
    decodeIntegerRow 16 3 1 20971994,
    decodeIntegerRow 16 3 1 19922554,
    decodeIntegerRow 16 3 1 16915342,
    decodeIntegerRow 16 3 1 7234258]

def assocABC : Matrix (RightIndex 3 1 7) (LeftIndex 3 1 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 1 7 r) []).getD (leftPosition 3 1 7 s) 0

theorem assocABC_eq : associatorZ 3 1 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 1 7 3) (RightIndex 3 1 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 1 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 20991892,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 16740388,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 21346294,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21504406,
    decodeIntegerRow 16 3 1 21532108]

def assocBAC : Matrix (RightIndex 1 3 7) (LeftIndex 1 3 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 3 7 r) []).getD (leftPosition 1 3 7 s) 0

theorem assocBAC_eq : associatorZ 1 3 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 3 7) (LeftIndex 3 1 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 1 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 7 1) (RightIndex 3 1 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 1 7 = innerRightABC := by
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

def inverseACB : Matrix (LeftIndex 3 7 1) (RightIndex 3 7 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 7 1 r) []).getD (rightPosition 3 7 1 s) 0

theorem inverseACB_eq : associatorInverseZ 3 7 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 3 1) (LeftIndex 3 7 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 7 1 = innerACB := by
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

def assocBCA : Matrix (RightIndex 1 7 3) (LeftIndex 1 7 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 7 3 r) []).getD (leftPosition 1 7 3 s) 0

theorem assocBCA_eq : associatorZ 1 7 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 7 3) (RightIndex 1 3 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 3 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18166408,
    decodeIntegerRow 16 3 1 7665528,
    decodeIntegerRow 16 3 1 6721284,
    decodeIntegerRow 16 3 1 15331876,
    decodeIntegerRow 16 3 1 7746204,
    decodeIntegerRow 16 3 1 18503044,
    decodeIntegerRow 16 3 1 28086472,
    decodeIntegerRow 16 3 1 36481928,
    decodeIntegerRow 16 3 1 36482952,
    decodeIntegerRow 16 3 1 14964472,
    decodeIntegerRow 16 3 1 18507556,
    decodeIntegerRow 16 3 1 35302404,
    decodeIntegerRow 16 3 1 27719044,
    decodeIntegerRow 16 3 1 6722204,
    decodeIntegerRow 16 3 1 35379192,
    decodeIntegerRow 16 3 1 18161848]

def assocCAB : Matrix (RightIndex 7 3 1) (LeftIndex 7 3 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 3 1 r) []).getD (leftPosition 7 3 1 s) 0

theorem assocCAB_eq : associatorZ 7 3 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 7 3 1) (LeftIndex 3 1 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 1 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317
