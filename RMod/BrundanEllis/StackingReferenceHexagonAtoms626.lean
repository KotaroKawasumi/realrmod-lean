import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23058580,
    decodeIntegerRow 16 3 1 22231696,
    decodeIntegerRow 16 3 1 35864980,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 26328200,
    decodeIntegerRow 16 3 1 7180288,
    decodeIntegerRow 16 3 1 22232200,
    decodeIntegerRow 16 3 1 19988032,
    decodeIntegerRow 16 3 1 21168832,
    decodeIntegerRow 16 3 1 19869880,
    decodeIntegerRow 16 3 1 16757888,
    decodeIntegerRow 16 3 1 7167160,
    decodeIntegerRow 16 3 1 35878096,
    decodeIntegerRow 16 3 1 16762260,
    decodeIntegerRow 16 3 1 23176624,
    decodeIntegerRow 16 3 1 21169300]

def assocABC : Matrix (RightIndex 6 2 6) (LeftIndex 6 2 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 6 2 6 r) []).getD (leftPosition 6 2 6 s) 0

theorem assocABC_eq : associatorZ 6 2 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 6 6) (RightIndex 6 2 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 2 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523414,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21524086,
    decodeIntegerRow 16 3 1 16760074,
    decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 16720708,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 21523126]

def assocBAC : Matrix (RightIndex 2 6 6) (LeftIndex 2 6 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 6 6 r) []).getD (leftPosition 2 6 6 s) 0

theorem assocBAC_eq : associatorZ 2 6 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 6 6) (LeftIndex 6 2 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 2 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 6 2) (RightIndex 6 2 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 2 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 16760074,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 23058634,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 35865706]

def inverseACB : Matrix (LeftIndex 6 6 2) (RightIndex 6 6 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 6 2 r) []).getD (rightPosition 6 6 2 s) 0

theorem inverseACB_eq : associatorInverseZ 6 6 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409]

def innerACB : Matrix (LeftIndex 6 6 2) (LeftIndex 6 6 2) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 6 6 2 r) []).getD (leftPosition 6 6 2 s) 0

theorem innerACB_eq : innerLeftZ 6 6 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 2 6 6) (LeftIndex 2 6 6) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 2 6 6 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409]

def innerRightBAC : Matrix (RightIndex 2 6 6) (RightIndex 2 6 6) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 2 6 6 r) []).getD (rightPosition 2 6 6 s) 0

theorem innerRightBAC_eq : innerRightZ 2 6 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21516802,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35871538]

def assocCAB : Matrix (RightIndex 6 6 2) (LeftIndex 6 6 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 6 2 r) []).getD (leftPosition 6 6 2 s) 0

theorem assocCAB_eq : associatorZ 6 6 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 6 6 2) (LeftIndex 6 2 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 2 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626
