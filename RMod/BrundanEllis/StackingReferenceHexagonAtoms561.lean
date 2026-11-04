import RMod.BrundanEllis.StackingReferenceHexagonAtoms516
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21523846,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 36403708,
    decodeIntegerRow 16 3 1 27900652,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 35340826,
    decodeIntegerRow 16 3 1 21523348,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523334,
    decodeIntegerRow 16 3 1 21523366,
    decodeIntegerRow 16 3 1 21602092,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21693946,
    decodeIntegerRow 16 3 1 21483994]

def assocABC : Matrix (RightIndex 5 6 1) (LeftIndex 5 6 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 6 1 r) []).getD (leftPosition 5 6 1 s) 0

theorem assocABC_eq : associatorZ 5 6 1 = assocABC := by
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

def outerABC : Matrix (LeftIndex 6 1 5) (RightIndex 5 6 1) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 6 1 5 r) []).getD (rightPosition 5 6 1 s) 0

theorem outerABC_eq : outerRightZ 5 6 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 5 1) (LeftIndex 6 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocCAB

theorem assocBAC_eq : associatorZ 6 5 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 5 1) (LeftIndex 5 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.innerACB

theorem innerABC_eq : innerLeftZ 5 6 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 1 6) (RightIndex 5 6 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 6 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 11957426,
    decodeIntegerRow 16 3 1 2391486,
    decodeIntegerRow 16 3 1 22586278,
    decodeIntegerRow 16 3 1 23649142,
    decodeIntegerRow 16 3 1 21641782,
    decodeIntegerRow 16 3 1 21759718,
    decodeIntegerRow 16 3 1 21513154,
    decodeIntegerRow 16 3 1 21498574,
    decodeIntegerRow 16 3 1 21551062,
    decodeIntegerRow 16 3 1 21539398,
    decodeIntegerRow 16 3 1 21759394,
    decodeIntegerRow 16 3 1 21641134,
    decodeIntegerRow 16 3 1 23649106,
    decodeIntegerRow 16 3 1 22586206,
    decodeIntegerRow 16 3 1 40655238,
    decodeIntegerRow 16 3 1 31089302]

def inverseACB : Matrix (LeftIndex 5 1 6) (RightIndex 5 1 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 1 6 r) []).getD (rightPosition 5 1 6 s) 0

theorem inverseACB_eq : associatorInverseZ 5 1 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 5 6) (LeftIndex 5 1 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.innerABC

theorem innerACB_eq : innerLeftZ 5 1 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 2391482,
    decodeIntegerRow 16 3 1 31089302,
    decodeIntegerRow 16 3 1 23649106,
    decodeIntegerRow 16 3 1 20460514,
    decodeIntegerRow 16 3 1 21495658,
    decodeIntegerRow 16 3 1 21507322,
    decodeIntegerRow 16 3 1 21287326,
    decodeIntegerRow 16 3 1 21405586,
    decodeIntegerRow 16 3 1 21533566,
    decodeIntegerRow 16 3 1 21498574,
    decodeIntegerRow 16 3 1 21641782,
    decodeIntegerRow 16 3 1 21287002,
    decodeIntegerRow 16 3 1 31089294,
    decodeIntegerRow 16 3 1 40655234,
    decodeIntegerRow 16 3 1 20460442,
    decodeIntegerRow 16 3 1 19397578]

def assocBCA : Matrix (RightIndex 6 1 5) (LeftIndex 6 1 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 1 5 r) []).getD (leftPosition 6 1 5 s) 0

theorem assocBCA_eq : associatorZ 6 1 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 1 5) (RightIndex 6 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 5 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 1 5 6) (LeftIndex 1 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocBAC

theorem assocCAB_eq : associatorZ 1 5 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms516.assocBAC_eq

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

def outerLeftABC : Matrix (RightIndex 1 5 6) (LeftIndex 5 6 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 5 6 r) []).getD (leftPosition 5 6 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 5 6 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms561
