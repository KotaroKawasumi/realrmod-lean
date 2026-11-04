import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 24897832,
    decodeIntegerRow 16 3 1 7785084,
    decodeIntegerRow 16 3 1 6681432,
    decodeIntegerRow 16 3 1 28068964,
    decodeIntegerRow 16 3 1 7627676,
    decodeIntegerRow 16 3 1 18516328,
    decodeIntegerRow 16 3 1 27727804,
    decodeIntegerRow 16 3 1 36444072,
    decodeIntegerRow 16 3 1 36442076,
    decodeIntegerRow 16 3 1 27732328,
    decodeIntegerRow 16 3 1 24526204,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 14973208,
    decodeIntegerRow 16 3 1 36363396,
    decodeIntegerRow 16 3 1 7784168,
    decodeIntegerRow 16 3 1 24893596]

def assocABC : Matrix (RightIndex 3 1 6) (LeftIndex 3 1 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 1 6 r) []).getD (leftPosition 3 1 6 s) 0

theorem assocABC_eq : associatorZ 3 1 6 = assocABC := by
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

def outerABC : Matrix (LeftIndex 1 6 3) (RightIndex 3 1 6) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 1 6 3 r) []).getD (rightPosition 3 1 6 s) 0

theorem outerABC_eq : outerRightZ 3 1 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 7705920,
    decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 27900664,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 21484480,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21337384,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21483508,
    decodeIntegerRow 16 3 1 21350668]

def assocBAC : Matrix (RightIndex 1 3 6) (LeftIndex 1 3 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 3 6 r) []).getD (leftPosition 1 3 6 s) 0

theorem assocBAC_eq : associatorZ 1 3 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 3 6) (LeftIndex 3 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 1 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 6 1) (RightIndex 3 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 1 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 22113122,
    decodeIntegerRow 16 3 1 22942726,
    decodeIntegerRow 16 3 1 26299858,
    decodeIntegerRow 16 3 1 35891734,
    decodeIntegerRow 16 3 1 21995022,
    decodeIntegerRow 16 3 1 23297014,
    decodeIntegerRow 16 3 1 26312962,
    decodeIntegerRow 16 3 1 35852314,
    decodeIntegerRow 16 3 1 26312818,
    decodeIntegerRow 16 3 1 7193866,
    decodeIntegerRow 16 3 1 21050238,
    decodeIntegerRow 16 3 1 23292646,
    decodeIntegerRow 16 3 1 26299678,
    decodeIntegerRow 16 3 1 7154554,
    decodeIntegerRow 16 3 1 20932142,
    decodeIntegerRow 16 3 1 22938346]

def inverseACB : Matrix (LeftIndex 3 6 1) (RightIndex 3 6 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 6 1 r) []).getD (rightPosition 3 6 1 s) 0

theorem inverseACB_eq : associatorInverseZ 3 6 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 3 1) (LeftIndex 3 6 1) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 6 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 24884692,
    decodeIntegerRow 16 3 1 7745772,
    decodeIntegerRow 16 3 1 6563336,
    decodeIntegerRow 16 3 1 27714664,
    decodeIntegerRow 16 3 1 24543532,
    decodeIntegerRow 16 3 1 7666988,
    decodeIntegerRow 16 3 1 6720744,
    decodeIntegerRow 16 3 1 28082104,
    decodeIntegerRow 16 3 1 7666068,
    decodeIntegerRow 16 3 1 18507412,
    decodeIntegerRow 16 3 1 28086616,
    decodeIntegerRow 16 3 1 36323976,
    decodeIntegerRow 16 3 1 7744748,
    decodeIntegerRow 16 3 1 18166228,
    decodeIntegerRow 16 3 1 27719224,
    decodeIntegerRow 16 3 1 36481496]

def assocBCA : Matrix (RightIndex 1 6 3) (LeftIndex 1 6 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 6 3 r) []).getD (leftPosition 1 6 3 s) 0

theorem assocBCA_eq : associatorZ 1 6 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 6 3) (RightIndex 1 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 3 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21525546,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 21523108,
    decodeIntegerRow 16 3 1 23058634,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 16720708,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 35865706,
    decodeIntegerRow 16 3 1 16760074,
    decodeIntegerRow 16 3 1 21522628,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21523414,
    decodeIntegerRow 16 3 1 21523126]

def assocCAB : Matrix (RightIndex 6 3 1) (LeftIndex 6 3 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 3 1 r) []).getD (leftPosition 6 3 1 s) 0

theorem assocCAB_eq : associatorZ 6 3 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 6 3 1) (LeftIndex 3 1 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 1 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316
