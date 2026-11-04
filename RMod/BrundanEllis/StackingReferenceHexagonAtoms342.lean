import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19988032,
    decodeIntegerRow 16 3 1 22231696,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 35879560,
    decodeIntegerRow 16 3 1 16762260,
    decodeIntegerRow 16 3 1 21169300,
    decodeIntegerRow 16 3 1 19869880,
    decodeIntegerRow 16 3 1 7168624,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 21168832,
    decodeIntegerRow 16 3 1 19870096,
    decodeIntegerRow 16 3 1 19988140,
    decodeIntegerRow 16 3 1 22232200,
    decodeIntegerRow 16 3 1 16718520,
    decodeIntegerRow 16 3 1 7181740]

def assocABC : Matrix (RightIndex 3 4 2) (LeftIndex 3 4 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 4 2 r) []).getD (leftPosition 3 4 2 s) 0

theorem assocABC_eq : associatorZ 3 4 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 4 2 3) (RightIndex 3 4 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 4 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7175182,
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

def assocBAC : Matrix (RightIndex 4 3 2) (LeftIndex 4 3 2) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 4 3 2 r) []).getD (leftPosition 4 3 2 s) 0

theorem assocBAC_eq : associatorZ 4 3 2 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 4 3 2) (LeftIndex 3 4 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 4 2 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 2 4) (RightIndex 3 4 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 4 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 26286646,
    decodeIntegerRow 16 3 1 21522628,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21523594,
    decodeIntegerRow 16 3 1 21523252,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21521172]

def inverseACB : Matrix (LeftIndex 3 2 4) (RightIndex 3 2 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 2 4 r) []).getD (rightPosition 3 2 4 s) 0

theorem inverseACB_eq : associatorInverseZ 3 2 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 3 4) (LeftIndex 3 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 2 4 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 26286646,
    decodeIntegerRow 16 3 1 21522628,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21523594,
    decodeIntegerRow 16 3 1 21523252,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21521172]

def assocBCA : Matrix (RightIndex 4 2 3) (LeftIndex 4 2 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 4 2 3 r) []).getD (leftPosition 4 2 3 s) 0

theorem assocBCA_eq : associatorZ 4 2 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 4 2 3) (RightIndex 4 3 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 4 3 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23118412,
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

def assocCAB : Matrix (RightIndex 2 3 4) (LeftIndex 2 3 4) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 2 3 4 r) []).getD (leftPosition 2 3 4 s) 0

theorem assocCAB_eq : associatorZ 2 3 4 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 2 3 4) (LeftIndex 3 4 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 4 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms342
