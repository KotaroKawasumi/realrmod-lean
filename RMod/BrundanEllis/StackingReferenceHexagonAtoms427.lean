import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 20991918,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21344026]

def assocABC : Matrix (RightIndex 4 2 7) (LeftIndex 4 2 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 2 7 r) []).getD (leftPosition 4 2 7 s) 0

theorem assocABC_eq : associatorZ 4 2 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 7 4) (RightIndex 4 2 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 2 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21522631]

def assocBAC : Matrix (RightIndex 2 4 7) (LeftIndex 2 4 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 4 7 r) []).getD (leftPosition 2 4 7 s) 0

theorem assocBAC_eq : associatorZ 2 4 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 4 7) (LeftIndex 4 2 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 4 2 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 7 2) (RightIndex 4 2 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 2 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21530002,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21702694,
    decodeIntegerRow 16 3 1 22054802,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 35872294,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 16740382]

def inverseACB : Matrix (LeftIndex 4 7 2) (RightIndex 4 7 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 7 2 r) []).getD (rightPosition 4 7 2 s) 0

theorem inverseACB_eq : associatorInverseZ 4 7 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 4 2) (LeftIndex 4 7 2) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 4 7 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21530002,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21702694,
    decodeIntegerRow 16 3 1 22054802,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 35872294,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 16740382]

def assocBCA : Matrix (RightIndex 2 7 4) (LeftIndex 2 7 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 7 4 r) []).getD (leftPosition 2 7 4 s) 0

theorem assocBCA_eq : associatorZ 2 7 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 7 4) (RightIndex 2 4 7) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 4 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35419558,
    decodeIntegerRow 16 3 1 27730066,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 6682378,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 7784626,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 24528298,
    decodeIntegerRow 16 3 1 21521098,
    decodeIntegerRow 16 3 1 21522846,
    decodeIntegerRow 16 3 1 21524306,
    decodeIntegerRow 16 3 1 21521242,
    decodeIntegerRow 16 3 1 21523818,
    decodeIntegerRow 16 3 1 21521086,
    decodeIntegerRow 16 3 1 21521266,
    decodeIntegerRow 16 3 1 21522362]

def assocCAB : Matrix (RightIndex 7 4 2) (LeftIndex 7 4 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 4 2 r) []).getD (leftPosition 7 4 2 s) 0

theorem assocCAB_eq : associatorZ 7 4 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523874,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21525478,
    decodeIntegerRow 16 3 1 21522414,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 21522902,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525454,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 36364342,
    decodeIntegerRow 16 3 1 35419558,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 18518422,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 35262094]

def outerLeftABC : Matrix (RightIndex 7 4 2) (LeftIndex 4 2 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 4 2 r) []).getD (leftPosition 4 2 7 s) 0

theorem outerLeftABC_eq : outerLeftZ 4 2 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427
