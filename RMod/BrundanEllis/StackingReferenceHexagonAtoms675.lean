import RMod.BrundanEllis.StackingReferenceHexagonAtoms567
import RMod.BrundanEllis.StackingReferenceHexagonAtoms576
import RMod.BrundanEllis.StackingReferenceHexagonAtoms657
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms675
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 7 5) (LeftIndex 6 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBCA

theorem assocABC_eq : associatorZ 6 7 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBCA_eq

def outerABC : Matrix (LeftIndex 7 5 6) (RightIndex 6 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 7 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 6 5) (LeftIndex 7 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocBCA

theorem assocBAC_eq : associatorZ 7 6 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocBCA_eq

def innerABC : Matrix (LeftIndex 7 6 5) (LeftIndex 6 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms657.innerACB

theorem innerABC_eq : innerLeftZ 6 7 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms657.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 5 7) (RightIndex 6 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 7 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 21352768,
    decodeIntegerRow 16 3 1 21484020,
    decodeIntegerRow 16 3 1 21602120,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 36404680,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 24714112,
    decodeIntegerRow 16 3 1 35340340]

def inverseACB : Matrix (LeftIndex 6 5 7) (RightIndex 6 5 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 5 7 r) []).getD (rightPosition 6 5 7 s) 0

theorem inverseACB_eq : associatorInverseZ 6 5 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 6 7) (LeftIndex 6 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms657.innerABC

theorem innerACB_eq : innerLeftZ 6 5 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms657.innerABC_eq

def assocBCA : Matrix (RightIndex 7 5 6) (LeftIndex 7 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocCAB

theorem assocBCA_eq : associatorZ 7 5 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocCAB_eq

def innerRightBAC : Matrix (RightIndex 7 5 6) (RightIndex 7 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 6 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 6 7) (LeftIndex 5 6 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocABC

theorem assocCAB_eq : associatorZ 5 6 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36575260,
    decodeIntegerRow 16 3 1 27937776,
    decodeIntegerRow 16 3 1 24635408,
    decodeIntegerRow 16 3 1 35156620,
    decodeIntegerRow 16 3 1 35157616,
    decodeIntegerRow 16 3 1 24631140,
    decodeIntegerRow 16 3 1 15104460,
    decodeIntegerRow 16 3 1 6473392,
    decodeIntegerRow 16 3 1 18253904,
    decodeIntegerRow 16 3 1 35524060,
    decodeIntegerRow 16 3 1 36234100,
    decodeIntegerRow 16 3 1 15187728,
    decodeIntegerRow 16 3 1 27863580,
    decodeIntegerRow 16 3 1 6814576,
    decodeIntegerRow 16 3 1 35525008,
    decodeIntegerRow 16 3 1 18258060]

def outerLeftABC : Matrix (RightIndex 5 6 7) (LeftIndex 6 7 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 6 7 r) []).getD (leftPosition 6 7 5 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 7 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms675
