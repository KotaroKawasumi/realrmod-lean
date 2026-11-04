import RMod.BrundanEllis.StackingReferenceHexagonAtoms316
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26247200,
    decodeIntegerRow 16 3 1 7351360,
    decodeIntegerRow 16 3 1 20997760,
    decodeIntegerRow 16 3 1 23095840,
    decodeIntegerRow 16 3 1 20986096,
    decodeIntegerRow 16 3 1 19907140,
    decodeIntegerRow 16 3 1 16681260,
    decodeIntegerRow 16 3 1 6997552,
    decodeIntegerRow 16 3 1 20999200,
    decodeIntegerRow 16 3 1 19946560,
    decodeIntegerRow 16 3 1 16799360,
    decodeIntegerRow 16 3 1 7351840,
    decodeIntegerRow 16 3 1 16681424,
    decodeIntegerRow 16 3 1 36049660,
    decodeIntegerRow 16 3 1 22062100,
    decodeIntegerRow 16 3 1 19911568]

def assocABC : Matrix (RightIndex 3 6 1) (LeftIndex 3 6 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 6 1 r) []).getD (leftPosition 3 6 1 s) 0

theorem assocABC_eq : associatorZ 3 6 1 = assocABC := by
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

def outerABC : Matrix (LeftIndex 6 1 3) (RightIndex 3 6 1) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 6 1 3 r) []).getD (rightPosition 3 6 1 s) 0

theorem outerABC_eq : outerRightZ 3 6 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 3 1) (LeftIndex 6 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocCAB

theorem assocBAC_eq : associatorZ 6 3 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 3 1) (LeftIndex 3 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.innerACB

theorem innerABC_eq : innerLeftZ 3 6 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 1 6) (RightIndex 3 6 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 6 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 24893596,
    decodeIntegerRow 16 3 1 7784168,
    decodeIntegerRow 16 3 1 6683324,
    decodeIntegerRow 16 3 1 28073512,
    decodeIntegerRow 16 3 1 35419044,
    decodeIntegerRow 16 3 1 24530392,
    decodeIntegerRow 16 3 1 15318916,
    decodeIntegerRow 16 3 1 6602648,
    decodeIntegerRow 16 3 1 36365288,
    decodeIntegerRow 16 3 1 28068964,
    decodeIntegerRow 16 3 1 24897832,
    decodeIntegerRow 16 3 1 35261636,
    decodeIntegerRow 16 3 1 27732328,
    decodeIntegerRow 16 3 1 6604644,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 18520516]

def inverseACB : Matrix (LeftIndex 3 1 6) (RightIndex 3 1 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 1 6 r) []).getD (rightPosition 3 1 6 s) 0

theorem inverseACB_eq : associatorInverseZ 3 1 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 3 6) (LeftIndex 3 1 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.innerABC

theorem innerACB_eq : innerLeftZ 3 1 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 24897832,
    decodeIntegerRow 16 3 1 7785084,
    decodeIntegerRow 16 3 1 6681432,
    decodeIntegerRow 16 3 1 28068964,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 24526204,
    decodeIntegerRow 16 3 1 15314392,
    decodeIntegerRow 16 3 1 6604644,
    decodeIntegerRow 16 3 1 36363396,
    decodeIntegerRow 16 3 1 28073512,
    decodeIntegerRow 16 3 1 24893596,
    decodeIntegerRow 16 3 1 35262552,
    decodeIntegerRow 16 3 1 27727804,
    decodeIntegerRow 16 3 1 6602648,
    decodeIntegerRow 16 3 1 35419044,
    decodeIntegerRow 16 3 1 18516328]

def assocBCA : Matrix (RightIndex 6 1 3) (LeftIndex 6 1 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 1 3 r) []).getD (leftPosition 6 1 3 s) 0

theorem assocBCA_eq : associatorZ 6 1 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 1 3) (RightIndex 6 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 3 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 1 3 6) (LeftIndex 1 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocBAC

theorem assocCAB_eq : associatorZ 1 3 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523366,
    decodeIntegerRow 16 3 1 21523334,
    decodeIntegerRow 16 3 1 21523332,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21523846,
    decodeIntegerRow 16 3 1 21521254,
    decodeIntegerRow 16 3 1 21521092,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21483994,
    decodeIntegerRow 16 3 1 21693946,
    decodeIntegerRow 16 3 1 21707068,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 18334714,
    decodeIntegerRow 16 3 1 35340826,
    decodeIntegerRow 16 3 1 36403708,
    decodeIntegerRow 16 3 1 15146068]

def outerLeftABC : Matrix (RightIndex 1 3 6) (LeftIndex 3 6 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 3 6 r) []).getD (leftPosition 3 6 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 3 6 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361
