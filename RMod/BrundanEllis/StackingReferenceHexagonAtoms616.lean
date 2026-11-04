import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21051698,
    decodeIntegerRow 16 3 1 22942726,
    decodeIntegerRow 16 3 1 26312818,
    decodeIntegerRow 16 3 1 7154554,
    decodeIntegerRow 16 3 1 26299858,
    decodeIntegerRow 16 3 1 7194406,
    decodeIntegerRow 16 3 1 22114578,
    decodeIntegerRow 16 3 1 19754074,
    decodeIntegerRow 16 3 1 26312962,
    decodeIntegerRow 16 3 1 35891734,
    decodeIntegerRow 16 3 1 21050238,
    decodeIntegerRow 16 3 1 20108374,
    decodeIntegerRow 16 3 1 22113122,
    decodeIntegerRow 16 3 1 23297014,
    decodeIntegerRow 16 3 1 26299678,
    decodeIntegerRow 16 3 1 35852854]

def assocABC : Matrix (RightIndex 6 1 6) (LeftIndex 6 1 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 6 1 6 r) []).getD (leftPosition 6 1 6 s) 0

theorem assocABC_eq : associatorZ 6 1 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523874,
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

def outerABC : Matrix (LeftIndex 1 6 6) (RightIndex 6 1 6) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 1 6 6 r) []).getD (rightPosition 6 1 6 s) 0

theorem outerABC_eq : outerRightZ 6 1 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 23122048,
    decodeIntegerRow 16 3 1 26483560,
    decodeIntegerRow 16 3 1 7233744,
    decodeIntegerRow 16 3 1 23113300,
    decodeIntegerRow 16 3 1 22073728,
    decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 23108944,
    decodeIntegerRow 16 3 1 20971480,
    decodeIntegerRow 16 3 1 7115648,
    decodeIntegerRow 16 3 1 26129260,
    decodeIntegerRow 16 3 1 21012304,
    decodeIntegerRow 16 3 1 19920280,
    decodeIntegerRow 16 3 1 16563328,
    decodeIntegerRow 16 3 1 7233260]

def assocBAC : Matrix (RightIndex 1 6 6) (LeftIndex 1 6 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 6 6 r) []).getD (leftPosition 1 6 6 s) 0

theorem assocBAC_eq : associatorZ 1 6 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 6 6) (LeftIndex 6 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 1 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 6 1) (RightIndex 6 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 1 6 = innerRightABC := by
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

def inverseACB : Matrix (LeftIndex 6 6 1) (RightIndex 6 6 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 6 1 r) []).getD (rightPosition 6 6 1 s) 0

theorem inverseACB_eq : associatorInverseZ 6 6 1 = inverseACB := by
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
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409]

def innerACB : Matrix (LeftIndex 6 6 1) (LeftIndex 6 6 1) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 6 6 1 r) []).getD (leftPosition 6 6 1 s) 0

theorem innerACB_eq : innerLeftZ 6 6 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 1 6 6) (LeftIndex 1 6 6) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 1 6 6 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409]

def innerRightBAC : Matrix (RightIndex 1 6 6) (RightIndex 1 6 6) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 1 6 6 r) []).getD (rightPosition 1 6 6 s) 0

theorem innerRightBAC_eq : innerRightZ 1 6 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21352762,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 36403222]

def assocCAB : Matrix (RightIndex 6 6 1) (LeftIndex 6 6 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 6 1 r) []).getD (leftPosition 6 6 1 s) 0

theorem assocCAB_eq : associatorZ 6 6 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522848,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21521260,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21521248,
    decodeIntegerRow 16 3 1 21524304,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 6721744,
    decodeIntegerRow 16 3 1 7745260,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 36482440]

def outerLeftABC : Matrix (RightIndex 6 6 1) (LeftIndex 6 1 6) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 6 6 1 r) []).getD (leftPosition 6 1 6 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 1 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616
