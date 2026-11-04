import RMod.BrundanEllis.StackingReferenceHexagonAtoms527
import RMod.BrundanEllis.StackingReferenceHexagonAtoms572
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms725
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 2 5) (LeftIndex 7 2 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.assocBCA

theorem assocABC_eq : associatorZ 7 2 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
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

def outerABC : Matrix (LeftIndex 2 5 7) (RightIndex 7 2 5) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 5 7 r) []).getD (rightPosition 7 2 5 s) 0

theorem outerABC_eq : outerRightZ 7 2 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 2 7 5) (LeftIndex 2 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocBCA

theorem assocBAC_eq : associatorZ 2 7 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocBCA_eq

def innerABC : Matrix (LeftIndex 2 7 5) (LeftIndex 7 2 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 2 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 5 2) (RightIndex 7 2 5) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 7 2 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23058526,
    decodeIntegerRow 16 3 1 22231714,
    decodeIntegerRow 16 3 1 35864974,
    decodeIntegerRow 16 3 1 26323826,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 26328198,
    decodeIntegerRow 16 3 1 19987978,
    decodeIntegerRow 16 3 1 22232182,
    decodeIntegerRow 16 3 1 7168618,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 19870042,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 23176786,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 35879554,
    decodeIntegerRow 16 3 1 26288834]

def inverseACB : Matrix (LeftIndex 7 5 2) (RightIndex 7 5 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 5 2 r) []).getD (rightPosition 7 5 2 s) 0

theorem inverseACB_eq : associatorInverseZ 7 5 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 7 2) (LeftIndex 7 5 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 7 5 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 2 5 7) (LeftIndex 2 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocBAC

theorem assocBCA_eq : associatorZ 2 5 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 2 5 7) (RightIndex 2 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 7 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 7 2) (LeftIndex 5 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.assocABC

theorem assocCAB_eq : associatorZ 5 7 2 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def outerLeftABC : Matrix (RightIndex 5 7 2) (LeftIndex 7 2 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 7 2 r) []).getD (leftPosition 7 2 5 s) 0

theorem outerLeftABC_eq : outerLeftZ 7 2 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms725
