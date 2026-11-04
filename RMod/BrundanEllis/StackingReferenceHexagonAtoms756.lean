import RMod.BrundanEllis.StackingReferenceHexagonAtoms567
import RMod.BrundanEllis.StackingReferenceHexagonAtoms576
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms756
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 5 6) (LeftIndex 7 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocCAB

theorem assocABC_eq : associatorZ 7 5 6 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocCAB_eq

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

def outerABC : Matrix (LeftIndex 5 6 7) (RightIndex 7 5 6) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 5 6 7 r) []).getD (rightPosition 7 5 6 s) 0

theorem outerABC_eq : outerRightZ 7 5 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 7 6) (LeftIndex 5 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocABC

theorem assocBAC_eq : associatorZ 5 7 6 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocABC_eq

def innerABC : Matrix (LeftIndex 5 7 6) (LeftIndex 7 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 5 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 6 5) (RightIndex 7 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 5 6 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 28082080,
    decodeIntegerRow 16 3 1 6720800,
    decodeIntegerRow 16 3 1 35379680,
    decodeIntegerRow 16 3 1 18503200,
    decodeIntegerRow 16 3 1 27719200,
    decodeIntegerRow 16 3 1 6565280,
    decodeIntegerRow 16 3 1 35301920,
    decodeIntegerRow 16 3 1 18166240,
    decodeIntegerRow 16 3 1 6722688,
    decodeIntegerRow 16 3 1 14960080,
    decodeIntegerRow 16 3 1 18507400,
    decodeIntegerRow 16 3 1 7666016,
    decodeIntegerRow 16 3 1 36483440,
    decodeIntegerRow 16 3 1 27714688,
    decodeIntegerRow 16 3 1 24884704,
    decodeIntegerRow 16 3 1 35301000]

def inverseACB : Matrix (LeftIndex 7 6 5) (RightIndex 7 6 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 6 5 r) []).getD (rightPosition 7 6 5 s) 0

theorem inverseACB_eq : associatorInverseZ 7 6 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21562752,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 7705408,
    decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 21602120,
    decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 36404680]

def innerACB : Matrix (LeftIndex 6 7 5) (LeftIndex 7 6 5) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 6 7 5 r) []).getD (leftPosition 7 6 5 s) 0

theorem innerACB_eq : innerLeftZ 7 6 5 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 5 6 7) (LeftIndex 5 6 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocABC

theorem assocBCA_eq : associatorZ 5 6 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 6 7) (RightIndex 5 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 7 6 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.innerRightABC_eq

def assocCAB : Matrix (RightIndex 6 7 5) (LeftIndex 6 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBCA

theorem assocCAB_eq : associatorZ 6 7 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 6 7 5) (LeftIndex 7 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 5 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms756
