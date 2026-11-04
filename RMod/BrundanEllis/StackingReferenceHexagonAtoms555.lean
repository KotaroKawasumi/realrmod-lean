import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms555
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 706186115764736,
    decodeIntegerRow 32 3 1 242946584532736,
    decodeIntegerRow 32 3 1 750310238914320,
    decodeIntegerRow 32 3 1 379831551308560,
    decodeIntegerRow 32 3 1 1477916717583400,
    decodeIntegerRow 32 3 1 1116336303503960,
    decodeIntegerRow 32 3 1 1615554829080928,
    decodeIntegerRow 32 3 1 1163724056615712,
    decodeIntegerRow 32 3 1 1102782300446480,
    decodeIntegerRow 32 3 1 1473398716564240,
    decodeIntegerRow 32 3 1 1146776192679936,
    decodeIntegerRow 32 3 1 1609905541102336,
    decodeIntegerRow 32 3 1 1615721497796512,
    decodeIntegerRow 32 3 1 1163777753519328,
    decodeIntegerRow 32 3 1 1477708381688920,
    decodeIntegerRow 32 3 1 1116269182374440,
    decodeIntegerRow 32 3 1 242946593352280,
    decodeIntegerRow 32 3 1 706186141383720,
    decodeIntegerRow 32 3 1 1473188648564512,
    decodeIntegerRow 32 3 1 1102709981951328,
    decodeIntegerRow 32 3 1 1116336335263104,
    decodeIntegerRow 32 3 1 1477916727819904,
    decodeIntegerRow 32 3 1 689296157635440,
    decodeIntegerRow 32 3 1 237465367957360,
    decodeIntegerRow 32 3 1 1473398705540512,
    decodeIntegerRow 32 3 1 1102782268424928,
    decodeIntegerRow 32 3 1 243114638933080,
    decodeIntegerRow 32 3 1 706243970562600,
    decodeIntegerRow 32 3 1 1163777778928400,
    decodeIntegerRow 32 3 1 1615721505986320,
    decodeIntegerRow 32 3 1 736751038228736,
    decodeIntegerRow 32 3 1 375311817396736]

def assocABC : Matrix (RightIndex 5 5 5) (LeftIndex 5 5 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 5 5 r) []).getD (leftPosition 5 5 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_0 : (associatorZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_1 : (associatorZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_0 : (associatorZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_1 : (associatorZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_0 : (associatorZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_1 : (associatorZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_0 : (associatorZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_1 : (associatorZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_0 : (associatorZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_1 : (associatorZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_2_0 : (associatorZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_2_1 : (associatorZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_3_0 : (associatorZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_3_1 : (associatorZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_0 : (associatorZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_1 : (associatorZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_2_0 : (associatorZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_2_1 : (associatorZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_3_0 : (associatorZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_3_1 : (associatorZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 5 5 5 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_2_0
  · exact assocABC_row_0_2_1
  · exact assocABC_row_0_3_0
  · exact assocABC_row_0_3_1
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_2_0
  · exact assocABC_row_1_2_1
  · exact assocABC_row_1_3_0
  · exact assocABC_row_1_3_1
  · exact assocABC_row_2_0_0
  · exact assocABC_row_2_0_1
  · exact assocABC_row_2_1_0
  · exact assocABC_row_2_1_1
  · exact assocABC_row_2_2_0
  · exact assocABC_row_2_2_1
  · exact assocABC_row_2_3_0
  · exact assocABC_row_2_3_1
  · exact assocABC_row_3_0_0
  · exact assocABC_row_3_0_1
  · exact assocABC_row_3_1_0
  · exact assocABC_row_3_1_1
  · exact assocABC_row_3_2_0
  · exact assocABC_row_3_2_1
  · exact assocABC_row_3_3_0
  · exact assocABC_row_3_3_1

def outerABC : Matrix (LeftIndex 5 5 5) (RightIndex 5 5 5) ℤ :=
  (show Matrix (Fin 4 × Fin 4 × Fin 2) (Fin 4 × Fin 4 × Fin 2) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_0 : (outerRightZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_1 : (outerRightZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_0 : (outerRightZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_1 : (outerRightZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_0 : (outerRightZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_1 : (outerRightZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_0 : (outerRightZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_1 : (outerRightZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_2_0 : (outerRightZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_2_1 : (outerRightZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_3_0 : (outerRightZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_3_1 : (outerRightZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_2_0 : (outerRightZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_2_1 : (outerRightZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_3_0 : (outerRightZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_3_1 : (outerRightZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 5 5 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_2_0
  · exact outerABC_row_0_2_1
  · exact outerABC_row_0_3_0
  · exact outerABC_row_0_3_1
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_2_0
  · exact outerABC_row_1_2_1
  · exact outerABC_row_1_3_0
  · exact outerABC_row_1_3_1
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_1_0
  · exact outerABC_row_2_1_1
  · exact outerABC_row_2_2_0
  · exact outerABC_row_2_2_1
  · exact outerABC_row_2_3_0
  · exact outerABC_row_2_3_1
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_1_0
  · exact outerABC_row_3_1_1
  · exact outerABC_row_3_2_0
  · exact outerABC_row_3_2_1
  · exact outerABC_row_3_3_0
  · exact outerABC_row_3_3_1

def assocBAC : Matrix (RightIndex 5 5 5) (LeftIndex 5 5 5) ℤ := assocABC

theorem assocBAC_eq : associatorZ 5 5 5 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 924250222353100,
    decodeIntegerRow 32 3 1 919730478207460,
    decodeIntegerRow 32 3 1 929334041164624,
    decodeIntegerRow 32 3 1 934981934642032,
    decodeIntegerRow 32 3 1 1155305913198260,
    decodeIntegerRow 32 3 1 1612897550742940,
    decodeIntegerRow 32 3 1 1109489566287216,
    decodeIntegerRow 32 3 1 1475448510009808,
    decodeIntegerRow 32 3 1 923686139182540,
    decodeIntegerRow 32 3 1 918038228695780,
    decodeIntegerRow 32 3 1 924250232980624,
    decodeIntegerRow 32 3 1 919730510090032,
    decodeIntegerRow 32 3 1 1109489566155980,
    decodeIntegerRow 32 3 1 1475448509616100,
    decodeIntegerRow 32 3 1 697714275548624,
    decodeIntegerRow 32 3 1 240122637794032,
    decodeIntegerRow 32 3 1 1109559301975220,
    decodeIntegerRow 32 3 1 1475657717073820,
    decodeIntegerRow 32 3 1 697770064204016,
    decodeIntegerRow 32 3 1 240290003760208,
    decodeIntegerRow 32 3 1 929334729913780,
    decodeIntegerRow 32 3 1 934984000889500,
    decodeIntegerRow 32 3 1 928769105565616,
    decodeIntegerRow 32 3 1 933287127845008,
    decodeIntegerRow 32 3 1 697770064099020,
    decodeIntegerRow 32 3 1 240290003445220,
    decodeIntegerRow 32 3 1 743460887007824,
    decodeIntegerRow 32 3 1 377362472171632,
    decodeIntegerRow 32 3 1 924251093916340,
    decodeIntegerRow 32 3 1 919733092897180,
    decodeIntegerRow 32 3 1 929334738415216,
    decodeIntegerRow 32 3 1 934984026393808]

def innerABC : Matrix (LeftIndex 5 5 5) (LeftIndex 5 5 5) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 5 5 5 r) []).getD (leftPosition 5 5 5 s) 0

private theorem innerABC_row_0_0_0 : (innerLeftZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_2_0 : (innerLeftZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_2_1 : (innerLeftZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_3_0 : (innerLeftZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_3_1 : (innerLeftZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_2_0 : (innerLeftZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_2_1 : (innerLeftZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_3_0 : (innerLeftZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_3_1 : (innerLeftZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_0 : (innerLeftZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_1 : (innerLeftZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_2_0 : (innerLeftZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_2_1 : (innerLeftZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_3_0 : (innerLeftZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_3_1 : (innerLeftZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_0 : (innerLeftZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_1 : (innerLeftZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_2_0 : (innerLeftZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_2_1 : (innerLeftZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_3_0 : (innerLeftZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_3_1 : (innerLeftZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 5 5 5 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_2_0
  · exact innerABC_row_0_2_1
  · exact innerABC_row_0_3_0
  · exact innerABC_row_0_3_1
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_2_0
  · exact innerABC_row_1_2_1
  · exact innerABC_row_1_3_0
  · exact innerABC_row_1_3_1
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_1_0
  · exact innerABC_row_2_1_1
  · exact innerABC_row_2_2_0
  · exact innerABC_row_2_2_1
  · exact innerABC_row_2_3_0
  · exact innerABC_row_2_3_1
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_1_0
  · exact innerABC_row_3_1_1
  · exact innerABC_row_3_2_0
  · exact innerABC_row_3_2_1
  · exact innerABC_row_3_3_0
  · exact innerABC_row_3_3_1

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 924250222353100,
    decodeIntegerRow 32 3 1 919730478207460,
    decodeIntegerRow 32 3 1 929334041164624,
    decodeIntegerRow 32 3 1 934981934642032,
    decodeIntegerRow 32 3 1 1155305913198260,
    decodeIntegerRow 32 3 1 1612897550742940,
    decodeIntegerRow 32 3 1 1109489566287216,
    decodeIntegerRow 32 3 1 1475448510009808,
    decodeIntegerRow 32 3 1 923686139182540,
    decodeIntegerRow 32 3 1 918038228695780,
    decodeIntegerRow 32 3 1 924250232980624,
    decodeIntegerRow 32 3 1 919730510090032,
    decodeIntegerRow 32 3 1 1109489566155980,
    decodeIntegerRow 32 3 1 1475448509616100,
    decodeIntegerRow 32 3 1 697714275548624,
    decodeIntegerRow 32 3 1 240122637794032,
    decodeIntegerRow 32 3 1 1109559301975220,
    decodeIntegerRow 32 3 1 1475657717073820,
    decodeIntegerRow 32 3 1 697770064204016,
    decodeIntegerRow 32 3 1 240290003760208,
    decodeIntegerRow 32 3 1 929334729913780,
    decodeIntegerRow 32 3 1 934984000889500,
    decodeIntegerRow 32 3 1 928769105565616,
    decodeIntegerRow 32 3 1 933287127845008,
    decodeIntegerRow 32 3 1 697770064099020,
    decodeIntegerRow 32 3 1 240290003445220,
    decodeIntegerRow 32 3 1 743460887007824,
    decodeIntegerRow 32 3 1 377362472171632,
    decodeIntegerRow 32 3 1 924251093916340,
    decodeIntegerRow 32 3 1 919733092897180,
    decodeIntegerRow 32 3 1 929334738415216,
    decodeIntegerRow 32 3 1 934984026393808]

def innerRightABC : Matrix (RightIndex 5 5 5) (RightIndex 5 5 5) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 5 5 5 r) []).getD (rightPosition 5 5 5 s) 0

private theorem innerRightABC_row_0_0_0 : (innerRightZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_0 : (innerRightZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_1 : (innerRightZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_0 : (innerRightZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_1 : (innerRightZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_0 : (innerRightZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_1 : (innerRightZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_0 : (innerRightZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_1 : (innerRightZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_2_0 : (innerRightZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_2_1 : (innerRightZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_3_0 : (innerRightZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_3_1 : (innerRightZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_2_0 : (innerRightZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_2_1 : (innerRightZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_3_0 : (innerRightZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_3_1 : (innerRightZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 5 5 5 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_2_0
  · exact innerRightABC_row_0_2_1
  · exact innerRightABC_row_0_3_0
  · exact innerRightABC_row_0_3_1
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_2_0
  · exact innerRightABC_row_1_2_1
  · exact innerRightABC_row_1_3_0
  · exact innerRightABC_row_1_3_1
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_1_0
  · exact innerRightABC_row_2_1_1
  · exact innerRightABC_row_2_2_0
  · exact innerRightABC_row_2_2_1
  · exact innerRightABC_row_2_3_0
  · exact innerRightABC_row_2_3_1
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_1_0
  · exact innerRightABC_row_3_1_1
  · exact innerRightABC_row_3_2_0
  · exact innerRightABC_row_3_2_1
  · exact innerRightABC_row_3_3_0
  · exact innerRightABC_row_3_3_1

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768986335604,
    decodeIntegerRow 32 3 1 1609884542804092,
    decodeIntegerRow 32 3 1 736690568745524,
    decodeIntegerRow 32 3 1 375124295251132,
    decodeIntegerRow 32 3 1 1615533994783108,
    decodeIntegerRow 32 3 1 1163717341432716,
    decodeIntegerRow 32 3 1 379642479480892,
    decodeIntegerRow 32 3 1 750245120385204,
    decodeIntegerRow 32 3 1 750302975183108,
    decodeIntegerRow 32 3 1 379810533881356,
    decodeIntegerRow 32 3 1 689235694530492,
    decodeIntegerRow 32 3 1 237277847937844,
    decodeIntegerRow 32 3 1 1477729216695436,
    decodeIntegerRow 32 3 1 1116275897793668,
    decodeIntegerRow 32 3 1 1610094610803916,
    decodeIntegerRow 32 3 1 1146841304830788,
    decodeIntegerRow 32 3 1 375290983177324,
    decodeIntegerRow 32 3 1 736744323071012,
    decodeIntegerRow 32 3 1 242925586237396,
    decodeIntegerRow 32 3 1 706178909429148,
    decodeIntegerRow 32 3 1 1102717181918372,
    decodeIntegerRow 32 3 1 1473209644737004,
    decodeIntegerRow 32 3 1 1163784468703332,
    decodeIntegerRow 32 3 1 1615742332094764,
    decodeIntegerRow 32 3 1 1615533985966372,
    decodeIntegerRow 32 3 1 1163717315822444,
    decodeIntegerRow 32 3 1 379642489717732,
    decodeIntegerRow 32 3 1 750245152145324,
    decodeIntegerRow 32 3 1 1146768960935316,
    decodeIntegerRow 32 3 1 1609884534617308,
    decodeIntegerRow 32 3 1 736690600768044,
    decodeIntegerRow 32 3 1 375124306275172]

def inverseACB : Matrix (LeftIndex 5 5 5) (RightIndex 5 5 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 5 5 r) []).getD (rightPosition 5 5 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = inverseACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = inverseACB ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = inverseACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = inverseACB ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_0 : (associatorInverseZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = inverseACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_1 : (associatorInverseZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = inverseACB ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_0 : (associatorInverseZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = inverseACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_1 : (associatorInverseZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = inverseACB ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = inverseACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = inverseACB ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = inverseACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = inverseACB ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_0 : (associatorInverseZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = inverseACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_1 : (associatorInverseZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = inverseACB ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_0 : (associatorInverseZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = inverseACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_1 : (associatorInverseZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = inverseACB ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = inverseACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = inverseACB ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = inverseACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = inverseACB ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_2_0 : (associatorInverseZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = inverseACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_2_1 : (associatorInverseZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = inverseACB ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_3_0 : (associatorInverseZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = inverseACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_3_1 : (associatorInverseZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = inverseACB ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = inverseACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = inverseACB ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = inverseACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = inverseACB ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_2_0 : (associatorInverseZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = inverseACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_2_1 : (associatorInverseZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = inverseACB ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_3_0 : (associatorInverseZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = inverseACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_3_1 : (associatorInverseZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = inverseACB ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 5 5 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_1_0
  · exact inverseACB_row_0_1_1
  · exact inverseACB_row_0_2_0
  · exact inverseACB_row_0_2_1
  · exact inverseACB_row_0_3_0
  · exact inverseACB_row_0_3_1
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_2_0
  · exact inverseACB_row_1_2_1
  · exact inverseACB_row_1_3_0
  · exact inverseACB_row_1_3_1
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_1_0
  · exact inverseACB_row_2_1_1
  · exact inverseACB_row_2_2_0
  · exact inverseACB_row_2_2_1
  · exact inverseACB_row_2_3_0
  · exact inverseACB_row_2_3_1
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_1_0
  · exact inverseACB_row_3_1_1
  · exact inverseACB_row_3_2_0
  · exact inverseACB_row_3_2_1
  · exact inverseACB_row_3_3_0
  · exact inverseACB_row_3_3_1

def innerACB : Matrix (LeftIndex 5 5 5) (LeftIndex 5 5 5) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 5 5 5 = innerACB := innerABC_eq

def assocBCA : Matrix (RightIndex 5 5 5) (LeftIndex 5 5 5) ℤ := assocABC

theorem assocBCA_eq : associatorZ 5 5 5 = assocBCA := assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 5 5) (RightIndex 5 5 5) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 5 5 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 5 5) (LeftIndex 5 5 5) ℤ := assocABC

theorem assocCAB_eq : associatorZ 5 5 5 = assocCAB := assocABC_eq

def outerLeftABC : Matrix (RightIndex 5 5 5) (LeftIndex 5 5 5) ℤ :=
  (show Matrix (Fin 4 × Fin 4 × Fin 2) (Fin 4 × Fin 4 × Fin 2) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerLeftABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerLeftABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerLeftABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerLeftABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_0 : (outerLeftZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerLeftABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_1 : (outerLeftZ 5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerLeftABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_0 : (outerLeftZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerLeftABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_1 : (outerLeftZ 5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerLeftABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerLeftABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerLeftABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerLeftABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerLeftABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_0 : (outerLeftZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerLeftABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_1 : (outerLeftZ 5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerLeftABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_0 : (outerLeftZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerLeftABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_1 : (outerLeftZ 5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerLeftABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerLeftABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerLeftABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerLeftABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerLeftABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_2_0 : (outerLeftZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerLeftABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_2_1 : (outerLeftZ 5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerLeftABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_3_0 : (outerLeftZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerLeftABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_3_1 : (outerLeftZ 5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerLeftABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerLeftABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerLeftABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerLeftABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerLeftABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_2_0 : (outerLeftZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerLeftABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_2_1 : (outerLeftZ 5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerLeftABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_3_0 : (outerLeftZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerLeftABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_3_1 : (outerLeftZ 5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerLeftABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 5 5 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_2_0
  · exact outerLeftABC_row_0_2_1
  · exact outerLeftABC_row_0_3_0
  · exact outerLeftABC_row_0_3_1
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_2_0
  · exact outerLeftABC_row_1_2_1
  · exact outerLeftABC_row_1_3_0
  · exact outerLeftABC_row_1_3_1
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_1_0
  · exact outerLeftABC_row_2_1_1
  · exact outerLeftABC_row_2_2_0
  · exact outerLeftABC_row_2_2_1
  · exact outerLeftABC_row_2_3_0
  · exact outerLeftABC_row_2_3_1
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_1_0
  · exact outerLeftABC_row_3_1_1
  · exact outerLeftABC_row_3_2_0
  · exact outerLeftABC_row_3_2_1
  · exact outerLeftABC_row_3_3_0
  · exact outerLeftABC_row_3_3_1

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms555
