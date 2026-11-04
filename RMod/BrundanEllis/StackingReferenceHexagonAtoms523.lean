import RMod.BrundanEllis.StackingReferenceHexagonAtoms325
import RMod.BrundanEllis.StackingReferenceHexagonAtoms352
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms523
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 2 3) (LeftIndex 5 2 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.assocBCA

theorem assocABC_eq : associatorZ 5 2 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510079374020,
    decodeIntegerRow 32 3 1 926510088011504,
    decodeIntegerRow 32 3 1 926510091313872,
    decodeIntegerRow 32 3 1 926510080792660,
    decodeIntegerRow 32 3 1 926510080791664,
    decodeIntegerRow 32 3 1 926510091318140,
    decodeIntegerRow 32 3 1 926510100844820,
    decodeIntegerRow 32 3 1 926510109475888,
    decodeIntegerRow 32 3 1 926510097695376,
    decodeIntegerRow 32 3 1 926510080425220,
    decodeIntegerRow 32 3 1 926510079715180,
    decodeIntegerRow 32 3 1 926510100761552,
    decodeIntegerRow 32 3 1 926510088085700,
    decodeIntegerRow 32 3 1 926510109134704,
    decodeIntegerRow 32 3 1 926510080424272,
    decodeIntegerRow 32 3 1 926510097691220,
    decodeIntegerRow 32 3 1 1574445034245820,
    decodeIntegerRow 32 3 1 1202629670355856,
    decodeIntegerRow 32 3 1 1060473556420528,
    decodeIntegerRow 32 3 1 1513377233966380,
    decodeIntegerRow 32 3 1 1513420108500496,
    decodeIntegerRow 32 3 1 1060289833015300,
    decodeIntegerRow 32 3 1 650197496999020,
    decodeIntegerRow 32 3 1 278658320870992,
    decodeIntegerRow 32 3 1 785770734172144,
    decodeIntegerRow 32 3 1 1529194321130620,
    decodeIntegerRow 32 3 1 1559759214909460,
    decodeIntegerRow 32 3 1 653781911363248,
    decodeIntegerRow 32 3 1 1199435775844540,
    decodeIntegerRow 32 3 1 293345173328656,
    decodeIntegerRow 32 3 1 1529235129422128,
    decodeIntegerRow 32 3 1 785949636344620]

def outerABC : Matrix (LeftIndex 2 3 5) (RightIndex 5 2 3) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 3 5 r) []).getD (rightPosition 5 2 3 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_0 : (outerRightZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_1 : (outerRightZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_2 : (outerRightZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_3 : (outerRightZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_0 : (outerRightZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_1 : (outerRightZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_2 : (outerRightZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_3 : (outerRightZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_0 : (outerRightZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_1 : (outerRightZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_2 : (outerRightZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_3 : (outerRightZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_0 : (outerRightZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_1 : (outerRightZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_2 : (outerRightZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_3 : (outerRightZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 2 3 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_1_2
  · exact outerABC_row_0_1_3
  · exact outerABC_row_0_2_0
  · exact outerABC_row_0_2_1
  · exact outerABC_row_0_2_2
  · exact outerABC_row_0_2_3
  · exact outerABC_row_0_3_0
  · exact outerABC_row_0_3_1
  · exact outerABC_row_0_3_2
  · exact outerABC_row_0_3_3
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_1_2_0
  · exact outerABC_row_1_2_1
  · exact outerABC_row_1_2_2
  · exact outerABC_row_1_2_3
  · exact outerABC_row_1_3_0
  · exact outerABC_row_1_3_1
  · exact outerABC_row_1_3_2
  · exact outerABC_row_1_3_3

def assocBAC : Matrix (RightIndex 2 5 3) (LeftIndex 2 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocBCA

theorem assocBAC_eq : associatorZ 2 5 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocBCA_eq

def innerABC : Matrix (LeftIndex 2 5 3) (LeftIndex 5 2 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_0 : (innerLeftZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_1 : (innerLeftZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_2 : (innerLeftZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_3 : (innerLeftZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_0 : (innerLeftZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_1 : (innerLeftZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_2 : (innerLeftZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_3 : (innerLeftZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 5 2 3 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_1_2
  · exact innerABC_row_0_1_3
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_1_2
  · exact innerABC_row_1_1_3
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_2_1_0
  · exact innerABC_row_2_1_1
  · exact innerABC_row_2_1_2
  · exact innerABC_row_2_1_3
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_3_1_0
  · exact innerABC_row_3_1_1
  · exact innerABC_row_3_1_2
  · exact innerABC_row_3_1_3

def innerRightABC : Matrix (RightIndex 5 3 2) (RightIndex 5 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 4) (Fin 2 × Fin 4 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_0 : (innerRightZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_1 : (innerRightZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_2 : (innerRightZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_3 : (innerRightZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_0 : (innerRightZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_1 : (innerRightZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_2 : (innerRightZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_3 : (innerRightZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_0 : (innerRightZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_1 : (innerRightZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_2 : (innerRightZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_3 : (innerRightZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_0 : (innerRightZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_1 : (innerRightZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_2 : (innerRightZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_3 : (innerRightZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 5 2 3 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_0_2
  · exact innerRightABC_row_0_0_3
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_1_2
  · exact innerRightABC_row_0_1_3
  · exact innerRightABC_row_0_2_0
  · exact innerRightABC_row_0_2_1
  · exact innerRightABC_row_0_2_2
  · exact innerRightABC_row_0_2_3
  · exact innerRightABC_row_0_3_0
  · exact innerRightABC_row_0_3_1
  · exact innerRightABC_row_0_3_2
  · exact innerRightABC_row_0_3_3
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_1_2
  · exact innerRightABC_row_1_1_3
  · exact innerRightABC_row_1_2_0
  · exact innerRightABC_row_1_2_1
  · exact innerRightABC_row_1_2_2
  · exact innerRightABC_row_1_2_3
  · exact innerRightABC_row_1_3_0
  · exact innerRightABC_row_1_3_1
  · exact innerRightABC_row_1_3_2
  · exact innerRightABC_row_1_3_3

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926802984258742,
    decodeIntegerRow 32 3 1 927353896428838,
    decodeIntegerRow 32 3 1 929146103439394,
    decodeIntegerRow 32 3 1 934104310831534,
    decodeIntegerRow 32 3 1 934104310871062,
    decodeIntegerRow 32 3 1 929146103426758,
    decodeIntegerRow 32 3 1 925666292778754,
    decodeIntegerRow 32 3 1 926217204479374,
    decodeIntegerRow 32 3 1 1544183876536034,
    decodeIntegerRow 32 3 1 1132400064790546,
    decodeIntegerRow 32 3 1 857879659665418,
    decodeIntegerRow 32 3 1 903633435894118,
    decodeIntegerRow 32 3 1 949386762523714,
    decodeIntegerRow 32 3 1 995140500488626,
    decodeIntegerRow 32 3 1 1132400063727658,
    decodeIntegerRow 32 3 1 1544183879724678,
    decodeIntegerRow 32 3 1 925659319208494,
    decodeIntegerRow 32 3 1 926782063670434,
    decodeIntegerRow 32 3 1 918853115861722,
    decodeIntegerRow 32 3 1 928957817068618,
    decodeIntegerRow 32 3 1 924062371769614,
    decodeIntegerRow 32 3 1 934167072950914,
    decodeIntegerRow 32 3 1 926782063547962,
    decodeIntegerRow 32 3 1 925659318855658,
    decodeIntegerRow 32 3 1 1132402388250598,
    decodeIntegerRow 32 3 1 308837083968138,
    decodeIntegerRow 32 3 1 903633168047854,
    decodeIntegerRow 32 3 1 995140414395166,
    decodeIntegerRow 32 3 1 995140443092998,
    decodeIntegerRow 32 3 1 903633177613738,
    decodeIntegerRow 32 3 1 1544183101695054,
    decodeIntegerRow 32 3 1 720617799538366]

def inverseACB : Matrix (LeftIndex 5 3 2) (RightIndex 5 3 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 3 2 r) []).getD (rightPosition 5 3 2 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 3 2 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_4_0_0
  · exact inverseACB_row_4_0_1
  · exact inverseACB_row_4_0_2
  · exact inverseACB_row_4_0_3
  · exact inverseACB_row_5_0_0
  · exact inverseACB_row_5_0_1
  · exact inverseACB_row_5_0_2
  · exact inverseACB_row_5_0_3
  · exact inverseACB_row_6_0_0
  · exact inverseACB_row_6_0_1
  · exact inverseACB_row_6_0_2
  · exact inverseACB_row_6_0_3
  · exact inverseACB_row_7_0_0
  · exact inverseACB_row_7_0_1
  · exact inverseACB_row_7_0_2
  · exact inverseACB_row_7_0_3

def innerACB : Matrix (LeftIndex 3 5 2) (LeftIndex 5 3 2) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_0 : (innerLeftZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_1 : (innerLeftZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_2 : (innerLeftZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_3 : (innerLeftZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_0 : (innerLeftZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_1 : (innerLeftZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_2 : (innerLeftZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_3 : (innerLeftZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_0 : (innerLeftZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_1 : (innerLeftZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_2 : (innerLeftZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_3 : (innerLeftZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_0 : (innerLeftZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_1 : (innerLeftZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_2 : (innerLeftZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_3 : (innerLeftZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 5 3 2 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_0_2
  · exact innerACB_row_2_0_3
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_0_2
  · exact innerACB_row_3_0_3
  · exact innerACB_row_4_0_0
  · exact innerACB_row_4_0_1
  · exact innerACB_row_4_0_2
  · exact innerACB_row_4_0_3
  · exact innerACB_row_5_0_0
  · exact innerACB_row_5_0_1
  · exact innerACB_row_5_0_2
  · exact innerACB_row_5_0_3
  · exact innerACB_row_6_0_0
  · exact innerACB_row_6_0_1
  · exact innerACB_row_6_0_2
  · exact innerACB_row_6_0_3
  · exact innerACB_row_7_0_0
  · exact innerACB_row_7_0_1
  · exact innerACB_row_7_0_2
  · exact innerACB_row_7_0_3

def assocBCA : Matrix (RightIndex 2 3 5) (LeftIndex 2 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocBAC

theorem assocBCA_eq : associatorZ 2 3 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 2 3 5) (RightIndex 2 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 2 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 2 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 2 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 2 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 2 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 2 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 2 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 2 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 2 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 2 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 2 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 2 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 2 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 2 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 2 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 2 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_0 : (innerRightZ 2 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_1 : (innerRightZ 2 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_2 : (innerRightZ 2 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_3 : (innerRightZ 2 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_0 : (innerRightZ 2 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_1 : (innerRightZ 2 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_2 : (innerRightZ 2 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_3 : (innerRightZ 2 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_0 : (innerRightZ 2 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_1 : (innerRightZ 2 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_2 : (innerRightZ 2 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_3 : (innerRightZ 2 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_0 : (innerRightZ 2 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_1 : (innerRightZ 2 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_2 : (innerRightZ 2 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_3 : (innerRightZ 2 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 2 5 3 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_0_2
  · exact innerRightBAC_row_0_0_3
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_0_2
  · exact innerRightBAC_row_2_0_3
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_0_2
  · exact innerRightBAC_row_3_0_3
  · exact innerRightBAC_row_4_0_0
  · exact innerRightBAC_row_4_0_1
  · exact innerRightBAC_row_4_0_2
  · exact innerRightBAC_row_4_0_3
  · exact innerRightBAC_row_5_0_0
  · exact innerRightBAC_row_5_0_1
  · exact innerRightBAC_row_5_0_2
  · exact innerRightBAC_row_5_0_3
  · exact innerRightBAC_row_6_0_0
  · exact innerRightBAC_row_6_0_1
  · exact innerRightBAC_row_6_0_2
  · exact innerRightBAC_row_6_0_3
  · exact innerRightBAC_row_7_0_0
  · exact innerRightBAC_row_7_0_1
  · exact innerRightBAC_row_7_0_2
  · exact innerRightBAC_row_7_0_3

def assocCAB : Matrix (RightIndex 3 5 2) (LeftIndex 3 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.assocABC

theorem assocCAB_eq : associatorZ 3 5 2 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425921,
    decodeIntegerRow 32 3 1 926510094425923,
    decodeIntegerRow 32 3 1 926510094425929,
    decodeIntegerRow 32 3 1 926510094425947,
    decodeIntegerRow 32 3 1 926510094426001,
    decodeIntegerRow 32 3 1 926510094426163,
    decodeIntegerRow 32 3 1 926510094426649,
    decodeIntegerRow 32 3 1 926510094428107,
    decodeIntegerRow 32 3 1 926510094432481,
    decodeIntegerRow 32 3 1 926510094445603,
    decodeIntegerRow 32 3 1 926510094484969,
    decodeIntegerRow 32 3 1 926510094603067,
    decodeIntegerRow 32 3 1 926510094957361,
    decodeIntegerRow 32 3 1 926510096020243,
    decodeIntegerRow 32 3 1 926510099208889,
    decodeIntegerRow 32 3 1 926510108774827,
    decodeIntegerRow 32 3 1 926510051379199,
    decodeIntegerRow 32 3 1 926509965285757,
    decodeIntegerRow 32 3 1 926509707005431,
    decodeIntegerRow 32 3 1 926508932164453,
    decodeIntegerRow 32 3 1 926506607641519,
    decodeIntegerRow 32 3 1 926499634072717,
    decodeIntegerRow 32 3 1 926478713366311,
    decodeIntegerRow 32 3 1 926415951247093,
    decodeIntegerRow 32 3 1 926227664889439,
    decodeIntegerRow 32 3 1 925662805816477,
    decodeIntegerRow 32 3 1 923968228597591,
    decodeIntegerRow 32 3 1 918884496940933,
    decodeIntegerRow 32 3 1 903633301970959,
    decodeIntegerRow 32 3 1 857879717061037,
    decodeIntegerRow 32 3 1 720618962331271,
    decodeIntegerRow 32 3 1 308836698141973]

def outerLeftABC : Matrix (RightIndex 3 5 2) (LeftIndex 5 2 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 5 2 r) []).getD (leftPosition 5 2 3 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 2 3 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_1_2
  · exact outerLeftABC_row_0_1_3
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_1_2
  · exact outerLeftABC_row_1_1_3
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_1_0
  · exact outerLeftABC_row_2_1_1
  · exact outerLeftABC_row_2_1_2
  · exact outerLeftABC_row_2_1_3
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_1_0
  · exact outerLeftABC_row_3_1_1
  · exact outerLeftABC_row_3_1_2
  · exact outerLeftABC_row_3_1_3

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms523
