import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16799522,
    decodeIntegerRow 16 3 1 35695366,
    decodeIntegerRow 16 3 1 20999218,
    decodeIntegerRow 16 3 1 23100214,
    decodeIntegerRow 16 3 1 22062082,
    decodeIntegerRow 16 3 1 23135206,
    decodeIntegerRow 16 3 1 26365458,
    decodeIntegerRow 16 3 1 36049174,
    decodeIntegerRow 16 3 1 22048978,
    decodeIntegerRow 16 3 1 23095786,
    decodeIntegerRow 16 3 1 26247362,
    decodeIntegerRow 16 3 1 35694874,
    decodeIntegerRow 16 3 1 16681422,
    decodeIntegerRow 16 3 1 36049654,
    decodeIntegerRow 16 3 1 20986078,
    decodeIntegerRow 16 3 1 23139526]

def assocABC : Matrix (RightIndex 5 2 7) (LeftIndex 5 2 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 2 7 r) []).getD (leftPosition 5 2 7 s) 0

theorem assocABC_eq : associatorZ 5 2 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

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

def outerABC : Matrix (LeftIndex 2 7 5) (RightIndex 5 2 7) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 7 5 r) []).getD (rightPosition 5 2 7 s) 0

theorem outerABC_eq : outerRightZ 5 2 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36232648,
    decodeIntegerRow 16 3 1 18415688,
    decodeIntegerRow 16 3 1 27942152,
    decodeIntegerRow 16 3 1 35525512,
    decodeIntegerRow 16 3 1 15108836,
    decodeIntegerRow 16 3 1 35523556,
    decodeIntegerRow 16 3 1 6813124,
    decodeIntegerRow 16 3 1 18411204,
    decodeIntegerRow 16 3 1 15183356,
    decodeIntegerRow 16 3 1 35158084,
    decodeIntegerRow 16 3 1 6472924,
    decodeIntegerRow 16 3 1 18258276,
    decodeIntegerRow 16 3 1 36574792,
    decodeIntegerRow 16 3 1 18253688,
    decodeIntegerRow 16 3 1 27859208,
    decodeIntegerRow 16 3 1 35156152]

def assocBAC : Matrix (RightIndex 2 5 7) (LeftIndex 2 5 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 5 7 r) []).getD (leftPosition 2 5 7 s) 0

theorem assocBAC_eq : associatorZ 2 5 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 5 7) (LeftIndex 5 2 7) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 2 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 7 2) (RightIndex 5 2 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 2 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21700426]

def inverseACB : Matrix (LeftIndex 5 7 2) (RightIndex 5 7 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 7 2 r) []).getD (rightPosition 5 7 2 s) 0

theorem inverseACB_eq : associatorInverseZ 5 7 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 5 2) (LeftIndex 5 7 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 7 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21700426,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21346132]

def assocBCA : Matrix (RightIndex 2 7 5) (LeftIndex 2 7 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 7 5 r) []).getD (leftPosition 2 7 5 s) 0

theorem assocBCA_eq : associatorZ 2 7 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 7 5) (RightIndex 2 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 5 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35852368,
    decodeIntegerRow 16 3 1 16733740,
    decodeIntegerRow 16 3 1 22938352,
    decodeIntegerRow 16 3 1 20932140,
    decodeIntegerRow 16 3 1 22113120,
    decodeIntegerRow 16 3 1 22942720,
    decodeIntegerRow 16 3 1 26312800,
    decodeIntegerRow 16 3 1 35852800,
    decodeIntegerRow 16 3 1 26299840,
    decodeIntegerRow 16 3 1 7155040,
    decodeIntegerRow 16 3 1 21996480,
    decodeIntegerRow 16 3 1 19754080,
    decodeIntegerRow 16 3 1 23297020,
    decodeIntegerRow 16 3 1 21995024,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 26299696]

def assocCAB : Matrix (RightIndex 7 5 2) (LeftIndex 7 5 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 5 2 r) []).getD (leftPosition 7 5 2 s) 0

theorem assocCAB_eq : associatorZ 7 5 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 6643012,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 15146068]

def outerLeftABC : Matrix (RightIndex 7 5 2) (LeftIndex 5 2 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 5 2 r) []).getD (leftPosition 5 2 7 s) 0

theorem outerLeftABC_eq : outerLeftZ 5 2 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527
