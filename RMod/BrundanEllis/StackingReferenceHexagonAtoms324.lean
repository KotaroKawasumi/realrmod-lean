import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 21465040,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 21344026,
    decodeIntegerRow 16 3 1 21583138,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 22054800,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 21503920,
    decodeIntegerRow 16 3 1 21529840,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 23117686,
    decodeIntegerRow 16 3 1 20991918]

def assocABC : Matrix (RightIndex 3 2 4) (LeftIndex 3 2 4) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 2 4 r) []).getD (leftPosition 3 2 4 s) 0

theorem assocABC_eq : associatorZ 3 2 4 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 4 3) (RightIndex 3 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 2 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21543034,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 7174534,
    decodeIntegerRow 16 3 1 26306572,
    decodeIntegerRow 16 3 1 21700508,
    decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23116954,
    decodeIntegerRow 16 3 1 21529894,
    decodeIntegerRow 16 3 1 21543052,
    decodeIntegerRow 16 3 1 16740634,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21582412,
    decodeIntegerRow 16 3 1 21700506]

def assocBAC : Matrix (RightIndex 2 3 4) (LeftIndex 2 3 4) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 3 4 r) []).getD (leftPosition 2 3 4 s) 0

theorem assocBAC_eq : associatorZ 2 3 4 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 3 4) (LeftIndex 3 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 2 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 4 2) (RightIndex 3 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 2 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16720456,
    decodeIntegerRow 16 3 1 7181068,
    decodeIntegerRow 16 3 1 23176000,
    decodeIntegerRow 16 3 1 21166880,
    decodeIntegerRow 16 3 1 22229760,
    decodeIntegerRow 16 3 1 23059360,
    decodeIntegerRow 16 3 1 35878936,
    decodeIntegerRow 16 3 1 16760308,
    decodeIntegerRow 16 3 1 35865760,
    decodeIntegerRow 16 3 1 16720960,
    decodeIntegerRow 16 3 1 21875468,
    decodeIntegerRow 16 3 1 23177464,
    decodeIntegerRow 16 3 1 23057908,
    decodeIntegerRow 16 3 1 20812584,
    decodeIntegerRow 16 3 1 16759840,
    decodeIntegerRow 16 3 1 7168000]

def inverseACB : Matrix (LeftIndex 3 4 2) (RightIndex 3 4 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 4 2 r) []).getD (rightPosition 3 4 2 s) 0

theorem inverseACB_eq : associatorInverseZ 3 4 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 3 2) (LeftIndex 3 4 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 4 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 26326264,
    decodeIntegerRow 16 3 1 35865652,
    decodeIntegerRow 16 3 1 19870720,
    decodeIntegerRow 16 3 1 21879840,
    decodeIntegerRow 16 3 1 20816960,
    decodeIntegerRow 16 3 1 19987360,
    decodeIntegerRow 16 3 1 7167784,
    decodeIntegerRow 16 3 1 26286412,
    decodeIntegerRow 16 3 1 7180960,
    decodeIntegerRow 16 3 1 26325760,
    decodeIntegerRow 16 3 1 21171252,
    decodeIntegerRow 16 3 1 19869256,
    decodeIntegerRow 16 3 1 19988812,
    decodeIntegerRow 16 3 1 22234136,
    decodeIntegerRow 16 3 1 26286880,
    decodeIntegerRow 16 3 1 35878720]

def assocBCA : Matrix (RightIndex 2 4 3) (LeftIndex 2 4 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 4 3 r) []).getD (leftPosition 2 4 3 s) 0

theorem assocBCA_eq : associatorZ 2 4 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 4 3) (RightIndex 2 3 4) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 3 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7175182,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464284,
    decodeIntegerRow 16 3 1 19929118,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 21503678,
    decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21582382,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35872996,
    decodeIntegerRow 16 3 1 21529918,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 20992162,
    decodeIntegerRow 16 3 1 19928956]

def assocCAB : Matrix (RightIndex 4 3 2) (LeftIndex 4 3 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 4 3 2 r) []).getD (leftPosition 4 3 2 s) 0

theorem assocCAB_eq : associatorZ 4 3 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 4 3 2) (LeftIndex 3 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 2 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms324
