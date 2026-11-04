import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms722
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 14977744,
    decodeIntegerRow 16 3 1 6602700,
    decodeIntegerRow 16 3 1 35419100,
    decodeIntegerRow 16 3 1 24897808,
    decodeIntegerRow 16 3 1 7784112,
    decodeIntegerRow 16 3 1 18520540,
    decodeIntegerRow 16 3 1 27732340,
    decodeIntegerRow 16 3 1 36363344,
    decodeIntegerRow 16 3 1 35420016,
    decodeIntegerRow 16 3 1 18153100,
    decodeIntegerRow 16 3 1 28073500,
    decodeIntegerRow 16 3 1 6604592,
    decodeIntegerRow 16 3 1 27727792,
    decodeIntegerRow 16 3 1 6681380,
    decodeIntegerRow 16 3 1 35261580,
    decodeIntegerRow 16 3 1 18516304]

def assocABC : Matrix (RightIndex 7 2 2) (LeftIndex 7 2 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 7 2 2 r) []).getD (leftPosition 7 2 2 s) 0

theorem assocABC_eq : associatorZ 7 2 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 2 7) (RightIndex 7 2 2) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 2 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21995024,
    decodeIntegerRow 16 3 1 20104000,
    decodeIntegerRow 16 3 1 16746880,
    decodeIntegerRow 16 3 1 35852368,
    decodeIntegerRow 16 3 1 16733920,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 22114580,
    decodeIntegerRow 16 3 1 19754080,
    decodeIntegerRow 16 3 1 16747024,
    decodeIntegerRow 16 3 1 7193920,
    decodeIntegerRow 16 3 1 21050240,
    decodeIntegerRow 16 3 1 20108368,
    decodeIntegerRow 16 3 1 22113120,
    decodeIntegerRow 16 3 1 23297020,
    decodeIntegerRow 16 3 1 26312980,
    decodeIntegerRow 16 3 1 35891680]

def assocBAC : Matrix (RightIndex 2 7 2) (LeftIndex 2 7 2) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 7 2 r) []).getD (leftPosition 2 7 2 s) 0

theorem assocBAC_eq : associatorZ 2 7 2 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 7 2) (LeftIndex 7 2 2) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 2 2 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677]

def innerRightABC : Matrix (RightIndex 7 2 2) (RightIndex 7 2 2) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 7 2 2 r) []).getD (rightPosition 7 2 2 s) 0

theorem innerRightABC_eq : innerRightZ 7 2 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18507412,
    decodeIntegerRow 16 3 1 7744748,
    decodeIntegerRow 16 3 1 6565224,
    decodeIntegerRow 16 3 1 14960104,
    decodeIntegerRow 16 3 1 35380652,
    decodeIntegerRow 16 3 1 24880492,
    decodeIntegerRow 16 3 1 15327496,
    decodeIntegerRow 16 3 1 6722744,
    decodeIntegerRow 16 3 1 36325976,
    decodeIntegerRow 16 3 1 15332056,
    decodeIntegerRow 16 3 1 18162028,
    decodeIntegerRow 16 3 1 35379732,
    decodeIntegerRow 16 3 1 14964616,
    decodeIntegerRow 16 3 1 36483384,
    decodeIntegerRow 16 3 1 7745772,
    decodeIntegerRow 16 3 1 24543532]

def inverseACB : Matrix (LeftIndex 7 2 2) (RightIndex 7 2 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 2 2 r) []).getD (rightPosition 7 2 2 s) 0

theorem inverseACB_eq : associatorInverseZ 7 2 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 7 2) (LeftIndex 7 2 2) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 7 2 2 = innerACB := innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21518986,
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

def assocBCA : Matrix (RightIndex 2 2 7) (LeftIndex 2 2 7) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 2 7 r) []).getD (leftPosition 2 2 7 s) 0

theorem assocBCA_eq : associatorZ 2 2 7 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 2 7) (RightIndex 2 7 2) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 7 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 2 7 2) (LeftIndex 2 7 2) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 2 7 2 = assocCAB := assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523874,
    decodeIntegerRow 16 3 1 21525478,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21524306,
    decodeIntegerRow 16 3 1 21523818,
    decodeIntegerRow 16 3 1 21525454,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 35419558,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 36364342,
    decodeIntegerRow 16 3 1 27730066,
    decodeIntegerRow 16 3 1 24528298,
    decodeIntegerRow 16 3 1 35262094]

def outerLeftABC : Matrix (RightIndex 2 7 2) (LeftIndex 7 2 2) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 2 7 2 r) []).getD (leftPosition 7 2 2 s) 0

theorem outerLeftABC_eq : outerLeftZ 7 2 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms722
