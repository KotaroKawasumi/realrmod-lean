import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517
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

def assocABC : Matrix (RightIndex 5 1 7) (LeftIndex 5 1 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 1 7 r) []).getD (leftPosition 5 1 7 s) 0

theorem assocABC_eq : associatorZ 5 1 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 1 7 5) (RightIndex 5 1 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 1 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21346294,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21543772,
    decodeIntegerRow 16 3 1 7174452,
    decodeIntegerRow 16 3 1 16740388,
    decodeIntegerRow 16 3 1 23117674,
    decodeIntegerRow 16 3 1 22054774,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 21464068,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21527734]

def assocBAC : Matrix (RightIndex 1 5 7) (LeftIndex 1 5 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 5 7 r) []).getD (leftPosition 1 5 7 s) 0

theorem assocBAC_eq : associatorZ 1 5 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 5 7) (LeftIndex 5 1 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 1 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 7 1) (RightIndex 5 1 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 1 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21445114,
    decodeIntegerRow 16 3 1 21696214,
    decodeIntegerRow 16 3 1 21341758,
    decodeIntegerRow 16 3 1 21483022,
    decodeIntegerRow 16 3 1 15146074,
    decodeIntegerRow 16 3 1 35340854,
    decodeIntegerRow 16 3 1 6643038,
    decodeIntegerRow 16 3 1 18334702,
    decodeIntegerRow 16 3 1 21709174,
    decodeIntegerRow 16 3 1 21484966,
    decodeIntegerRow 16 3 1 21602578,
    decodeIntegerRow 16 3 1 21691678,
    decodeIntegerRow 16 3 1 36403734,
    decodeIntegerRow 16 3 1 18334726,
    decodeIntegerRow 16 3 1 27900658,
    decodeIntegerRow 16 3 1 35340798]

def inverseACB : Matrix (LeftIndex 5 7 1) (RightIndex 5 7 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 7 1 r) []).getD (rightPosition 5 7 1 s) 0

theorem inverseACB_eq : associatorInverseZ 5 7 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 5 1) (LeftIndex 5 7 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 7 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21601606,
    decodeIntegerRow 16 3 1 21350506,
    decodeIntegerRow 16 3 1 21704962,
    decodeIntegerRow 16 3 1 21563698,
    decodeIntegerRow 16 3 1 27900646,
    decodeIntegerRow 16 3 1 7705866,
    decodeIntegerRow 16 3 1 36403682,
    decodeIntegerRow 16 3 1 24712018,
    decodeIntegerRow 16 3 1 21337546,
    decodeIntegerRow 16 3 1 21561754,
    decodeIntegerRow 16 3 1 21444142,
    decodeIntegerRow 16 3 1 21355042,
    decodeIntegerRow 16 3 1 6642986,
    decodeIntegerRow 16 3 1 24711994,
    decodeIntegerRow 16 3 1 15146062,
    decodeIntegerRow 16 3 1 7705922]

def assocBCA : Matrix (RightIndex 1 7 5) (LeftIndex 1 7 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 7 5 r) []).getD (leftPosition 1 7 5 s) 0

theorem assocBCA_eq : associatorZ 1 7 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 7 5) (RightIndex 1 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 5 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18153124,
    decodeIntegerRow 16 3 1 6683324,
    decodeIntegerRow 16 3 1 7627676,
    decodeIntegerRow 16 3 1 27727804,
    decodeIntegerRow 16 3 1 6604644,
    decodeIntegerRow 16 3 1 24526204,
    decodeIntegerRow 16 3 1 14977756,
    decodeIntegerRow 16 3 1 7785084,
    decodeIntegerRow 16 3 1 35262552,
    decodeIntegerRow 16 3 1 28073512,
    decodeIntegerRow 16 3 1 24530392,
    decodeIntegerRow 16 3 1 6602648,
    decodeIntegerRow 16 3 1 15314392,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 6681432,
    decodeIntegerRow 16 3 1 18148888]

def assocCAB : Matrix (RightIndex 7 5 1) (LeftIndex 7 5 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 5 1 r) []).getD (leftPosition 7 5 1 s) 0

theorem assocCAB_eq : associatorZ 7 5 1 = assocCAB := by
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

def outerLeftABC : Matrix (RightIndex 7 5 1) (LeftIndex 5 1 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 5 1 r) []).getD (leftPosition 5 1 7 s) 0

theorem outerLeftABC_eq : outerLeftZ 5 1 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517
