import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms326
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 929898129819544,
    decodeIntegerRow 32 3 1 918601809163464,
    decodeIntegerRow 32 3 1 933853778856372,
    decodeIntegerRow 32 3 1 924816722331508,
    decodeIntegerRow 32 3 1 1200940961309464,
    decodeIntegerRow 32 3 1 285938988166984,
    decodeIntegerRow 32 3 1 1521348533292532,
    decodeIntegerRow 32 3 1 789346954778548,
    decodeIntegerRow 32 3 1 924816722698936,
    decodeIntegerRow 32 3 1 933853779013784,
    decodeIntegerRow 32 3 1 934418379767052,
    decodeIntegerRow 32 3 1 923122059373492,
    decodeIntegerRow 32 3 1 789346984540216,
    decodeIntegerRow 32 3 1 1521348546042904,
    decodeIntegerRow 32 3 1 1567081207057612,
    decodeIntegerRow 32 3 1 652079255179252,
    decodeIntegerRow 32 3 1 1201122274096372,
    decodeIntegerRow 32 3 1 1567039359267508,
    decodeIntegerRow 32 3 1 331755338389144,
    decodeIntegerRow 32 3 1 789151694853064,
    decodeIntegerRow 32 3 1 923119820602828,
    decodeIntegerRow 32 3 1 918602325724172,
    decodeIntegerRow 32 3 1 933852745735016,
    decodeIntegerRow 32 3 1 928205877136696,
    decodeIntegerRow 32 3 1 1063868464239052,
    decodeIntegerRow 32 3 1 1521264863221492,
    decodeIntegerRow 32 3 1 1567039365649336,
    decodeIntegerRow 32 3 1 1201122246463384,
    decodeIntegerRow 32 3 1 924814312082548,
    decodeIntegerRow 32 3 1 919167442959308,
    decodeIntegerRow 32 3 1 918602325645384,
    decodeIntegerRow 32 3 1 923119820943976]

def assocABC : Matrix (RightIndex 3 2 6) (LeftIndex 3 2 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 2 6 r) []).getD (leftPosition 3 2 6 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_4 : (associatorZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_5 : (associatorZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_6 : (associatorZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_7 : (associatorZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_4 : (associatorZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_5 : (associatorZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_6 : (associatorZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_7 : (associatorZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 2 6 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_0_2
  · exact assocABC_row_0_0_3
  · exact assocABC_row_0_0_4
  · exact assocABC_row_0_0_5
  · exact assocABC_row_0_0_6
  · exact assocABC_row_0_0_7
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_0_4
  · exact assocABC_row_1_0_5
  · exact assocABC_row_1_0_6
  · exact assocABC_row_1_0_7
  · exact assocABC_row_2_0_0
  · exact assocABC_row_2_0_1
  · exact assocABC_row_2_0_2
  · exact assocABC_row_2_0_3
  · exact assocABC_row_2_0_4
  · exact assocABC_row_2_0_5
  · exact assocABC_row_2_0_6
  · exact assocABC_row_2_0_7
  · exact assocABC_row_3_0_0
  · exact assocABC_row_3_0_1
  · exact assocABC_row_3_0_2
  · exact assocABC_row_3_0_3
  · exact assocABC_row_3_0_4
  · exact assocABC_row_3_0_5
  · exact assocABC_row_3_0_6
  · exact assocABC_row_3_0_7

def outerABC : Matrix (LeftIndex 2 6 3) (RightIndex 3 2 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 2 6 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_0_0_4
  · exact outerABC_row_0_0_5
  · exact outerABC_row_0_0_6
  · exact outerABC_row_0_0_7
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_0_4
  · exact outerABC_row_1_0_5
  · exact outerABC_row_1_0_6
  · exact outerABC_row_1_0_7
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_0_4
  · exact outerABC_row_2_0_5
  · exact outerABC_row_2_0_6
  · exact outerABC_row_2_0_7
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_0_4
  · exact outerABC_row_3_0_5
  · exact outerABC_row_3_0_6
  · exact outerABC_row_3_0_7

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 286001746929232,
    decodeIntegerRow 32 3 1 1201129233809340,
    decodeIntegerRow 32 3 1 1063680192840020,
    decodeIntegerRow 32 3 1 331692570074224,
    decodeIntegerRow 32 3 1 934417591068784,
    decodeIntegerRow 32 3 1 923119731493420,
    decodeIntegerRow 32 3 1 924816642801340,
    decodeIntegerRow 32 3 1 933853535534128,
    decodeIntegerRow 32 3 1 1567102124748220,
    decodeIntegerRow 32 3 1 652086214969008,
    decodeIntegerRow 32 3 1 789158683223024,
    decodeIntegerRow 32 3 1 1521285777364780,
    decodeIntegerRow 32 3 1 918601564660780,
    decodeIntegerRow 32 3 1 929898046746256,
    decodeIntegerRow 32 3 1 928205784484528,
    decodeIntegerRow 32 3 1 919167169876420,
    decodeIntegerRow 32 3 1 919166683076464,
    decodeIntegerRow 32 3 1 924816630042220,
    decodeIntegerRow 32 3 1 929900450985340,
    decodeIntegerRow 32 3 1 934417618704688,
    decodeIntegerRow 32 3 1 331692569706832,
    decodeIntegerRow 32 3 1 789339996169340,
    decodeIntegerRow 32 3 1 1201129233888020,
    decodeIntegerRow 32 3 1 1567018441581424,
    decodeIntegerRow 32 3 1 933852989212780,
    decodeIntegerRow 32 3 1 928205797234576,
    decodeIntegerRow 32 3 1 923122148487088,
    decodeIntegerRow 32 3 1 918601537026820,
    decodeIntegerRow 32 3 1 1521285777732220,
    decodeIntegerRow 32 3 1 1063861505471408,
    decodeIntegerRow 32 3 1 652086214890224,
    decodeIntegerRow 32 3 1 285918064444780]

def assocBAC : Matrix (RightIndex 2 3 6) (LeftIndex 2 3 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 3 6 r) []).getD (leftPosition 2 3 6 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_4 : (associatorZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_5 : (associatorZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_6 : (associatorZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_7 : (associatorZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_4 : (associatorZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_5 : (associatorZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_6 : (associatorZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_7 : (associatorZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_4 : (associatorZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_5 : (associatorZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_6 : (associatorZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_7 : (associatorZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_4 : (associatorZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_5 : (associatorZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_6 : (associatorZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_7 : (associatorZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 2 3 6 = assocBAC := by
  funext r
  fin_cases r
  · exact assocBAC_row_0_0_0
  · exact assocBAC_row_0_0_1
  · exact assocBAC_row_0_0_2
  · exact assocBAC_row_0_0_3
  · exact assocBAC_row_0_0_4
  · exact assocBAC_row_0_0_5
  · exact assocBAC_row_0_0_6
  · exact assocBAC_row_0_0_7
  · exact assocBAC_row_1_0_0
  · exact assocBAC_row_1_0_1
  · exact assocBAC_row_1_0_2
  · exact assocBAC_row_1_0_3
  · exact assocBAC_row_1_0_4
  · exact assocBAC_row_1_0_5
  · exact assocBAC_row_1_0_6
  · exact assocBAC_row_1_0_7
  · exact assocBAC_row_2_0_0
  · exact assocBAC_row_2_0_1
  · exact assocBAC_row_2_0_2
  · exact assocBAC_row_2_0_3
  · exact assocBAC_row_2_0_4
  · exact assocBAC_row_2_0_5
  · exact assocBAC_row_2_0_6
  · exact assocBAC_row_2_0_7
  · exact assocBAC_row_3_0_0
  · exact assocBAC_row_3_0_1
  · exact assocBAC_row_3_0_2
  · exact assocBAC_row_3_0_3
  · exact assocBAC_row_3_0_4
  · exact assocBAC_row_3_0_5
  · exact assocBAC_row_3_0_6
  · exact assocBAC_row_3_0_7

def innerABC : Matrix (LeftIndex 2 3 6) (LeftIndex 3 2 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_4 : (innerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_5 : (innerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_6 : (innerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_7 : (innerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_4 : (innerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_5 : (innerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_6 : (innerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_7 : (innerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 2 6 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_0_0_4
  · exact innerABC_row_0_0_5
  · exact innerABC_row_0_0_6
  · exact innerABC_row_0_0_7
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_1_2
  · exact innerABC_row_0_1_3
  · exact innerABC_row_0_1_4
  · exact innerABC_row_0_1_5
  · exact innerABC_row_0_1_6
  · exact innerABC_row_0_1_7
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_0_4
  · exact innerABC_row_1_0_5
  · exact innerABC_row_1_0_6
  · exact innerABC_row_1_0_7
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_1_2
  · exact innerABC_row_1_1_3
  · exact innerABC_row_1_1_4
  · exact innerABC_row_1_1_5
  · exact innerABC_row_1_1_6
  · exact innerABC_row_1_1_7

def innerRightABC : Matrix (RightIndex 3 6 2) (RightIndex 3 2 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 3 2 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 3 2 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_4 : (innerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_5 : (innerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_6 : (innerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_7 : (innerRightZ 3 2 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_4 : (innerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_5 : (innerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_6 : (innerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_7 : (innerRightZ 3 2 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 2 6 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_0_2
  · exact innerRightABC_row_0_0_3
  · exact innerRightABC_row_0_0_4
  · exact innerRightABC_row_0_0_5
  · exact innerRightABC_row_0_0_6
  · exact innerRightABC_row_0_0_7
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_0_4
  · exact innerRightABC_row_1_0_5
  · exact innerRightABC_row_1_0_6
  · exact innerRightABC_row_1_0_7
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_0_2
  · exact innerRightABC_row_2_0_3
  · exact innerRightABC_row_2_0_4
  · exact innerRightABC_row_2_0_5
  · exact innerRightABC_row_2_0_6
  · exact innerRightABC_row_2_0_7
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_0_2
  · exact innerRightABC_row_3_0_3
  · exact innerRightABC_row_3_0_4
  · exact innerRightABC_row_3_0_5
  · exact innerRightABC_row_3_0_6
  · exact innerRightABC_row_3_0_7

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 929048473475680,
    decodeIntegerRow 32 3 1 918894957311632,
    decodeIntegerRow 32 3 1 926259046008016,
    decodeIntegerRow 32 3 1 927263240033440,
    decodeIntegerRow 32 3 1 1132401270098740,
    decodeIntegerRow 32 3 1 308836570596160,
    decodeIntegerRow 32 3 1 903632919333440,
    decodeIntegerRow 32 3 1 995141648401180,
    decodeIntegerRow 32 3 1 903632909767500,
    decodeIntegerRow 32 3 1 995141619703360,
    decodeIntegerRow 32 3 1 1132401269035840,
    decodeIntegerRow 32 3 1 308836567407460,
    decodeIntegerRow 32 3 1 926761142961760,
    decodeIntegerRow 32 3 1 925756949172208,
    decodeIntegerRow 32 3 1 923971715387824,
    decodeIntegerRow 32 3 1 934125231575200,
    decodeIntegerRow 32 3 1 926823905081140,
    decodeIntegerRow 32 3 1 927451526036800,
    decodeIntegerRow 32 3 1 929055447031360,
    decodeIntegerRow 32 3 1 934146152285980,
    decodeIntegerRow 32 3 1 949386504243360,
    decodeIntegerRow 32 3 1 995139295180432,
    decodeIntegerRow 32 3 1 1132401182942416,
    decodeIntegerRow 32 3 1 1544183363164000,
    decodeIntegerRow 32 3 1 1132401184005280,
    decodeIntegerRow 32 3 1 1544183359975408,
    decodeIntegerRow 32 3 1 949386494677424,
    decodeIntegerRow 32 3 1 995139323878240,
    decodeIntegerRow 32 3 1 923964741805900,
    decodeIntegerRow 32 3 1 918874036609600,
    decodeIntegerRow 32 3 1 926196283888960,
    decodeIntegerRow 32 3 1 925568662460260]

def inverseACB : Matrix (LeftIndex 3 6 2) (RightIndex 3 6 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 6 2 r) []).getD (rightPosition 3 6 2 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 6 2 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_0_0_4
  · exact inverseACB_row_0_0_5
  · exact inverseACB_row_0_0_6
  · exact inverseACB_row_0_0_7
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_0_4
  · exact inverseACB_row_1_0_5
  · exact inverseACB_row_1_0_6
  · exact inverseACB_row_1_0_7
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_2_0_4
  · exact inverseACB_row_2_0_5
  · exact inverseACB_row_2_0_6
  · exact inverseACB_row_2_0_7
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_3_0_4
  · exact inverseACB_row_3_0_5
  · exact inverseACB_row_3_0_6
  · exact inverseACB_row_3_0_7

def innerACB : Matrix (LeftIndex 6 3 2) (LeftIndex 3 6 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 3 6 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 3 6 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_4 : (innerLeftZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_5 : (innerLeftZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_6 : (innerLeftZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_7 : (innerLeftZ 3 6 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_4 : (innerLeftZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_5 : (innerLeftZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_6 : (innerLeftZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_7 : (innerLeftZ 3 6 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 6 2 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_0_0_4
  · exact innerACB_row_0_0_5
  · exact innerACB_row_0_0_6
  · exact innerACB_row_0_0_7
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_1_0_4
  · exact innerACB_row_1_0_5
  · exact innerACB_row_1_0_6
  · exact innerACB_row_1_0_7
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_0_2
  · exact innerACB_row_2_0_3
  · exact innerACB_row_2_0_4
  · exact innerACB_row_2_0_5
  · exact innerACB_row_2_0_6
  · exact innerACB_row_2_0_7
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_0_2
  · exact innerACB_row_3_0_3
  · exact innerACB_row_3_0_4
  · exact innerACB_row_3_0_5
  · exact innerACB_row_3_0_6
  · exact innerACB_row_3_0_7

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 1524597967820480,
    decodeIntegerRow 32 3 1 781384287196168,
    decodeIntegerRow 32 3 1 1208396912770384,
    decodeIntegerRow 32 3 1 284174162061440,
    decodeIntegerRow 32 3 1 1193668735377616,
    decodeIntegerRow 32 3 1 287744628945920,
    decodeIntegerRow 32 3 1 1518014918505920,
    decodeIntegerRow 32 3 1 797116658260552,
    decodeIntegerRow 32 3 1 284174148964656,
    decodeIntegerRow 32 3 1 1208396882926720,
    decodeIntegerRow 32 3 1 1071635929443520,
    decodeIntegerRow 32 3 1 328422227774072,
    decodeIntegerRow 32 3 1 797116630778560,
    decodeIntegerRow 32 3 1 1518014912494152,
    decodeIntegerRow 32 3 1 1565275572318416,
    decodeIntegerRow 32 3 1 659351483152000,
    decodeIntegerRow 32 3 1 1071721850703184,
    decodeIntegerRow 32 3 1 1524793737562880,
    decodeIntegerRow 32 3 1 1568663693976000,
    decodeIntegerRow 32 3 1 1208352630901768,
    decodeIntegerRow 32 3 1 1565455851986880,
    decodeIntegerRow 32 3 1 1193708136492088,
    decodeIntegerRow 32 3 1 1055822113672624,
    decodeIntegerRow 32 3 1 1517820169130240,
    decodeIntegerRow 32 3 1 1208352660736960,
    decodeIntegerRow 32 3 1 1568663680881272,
    decodeIntegerRow 32 3 1 328226444542256,
    decodeIntegerRow 32 3 1 781298365945600,
    decodeIntegerRow 32 3 1 1517820175138224,
    decodeIntegerRow 32 3 1 1055822086199680,
    decodeIntegerRow 32 3 1 659312022673600,
    decodeIntegerRow 32 3 1 287564349279288]

def assocBCA : Matrix (RightIndex 2 6 3) (LeftIndex 2 6 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 6 3 r) []).getD (leftPosition 2 6 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 2 6 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 2 6 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 2 6 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 2 6 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_4 : (associatorZ 2 6 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_5 : (associatorZ 2 6 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_6 : (associatorZ 2 6 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_7 : (associatorZ 2 6 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 2 6 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 2 6 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 2 6 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 2 6 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_4 : (associatorZ 2 6 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_5 : (associatorZ 2 6 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_6 : (associatorZ 2 6 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_7 : (associatorZ 2 6 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 2 6 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 2 6 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 2 6 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 2 6 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_4 : (associatorZ 2 6 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_5 : (associatorZ 2 6 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_6 : (associatorZ 2 6 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_7 : (associatorZ 2 6 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 2 6 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 2 6 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 2 6 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 2 6 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_4 : (associatorZ 2 6 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_5 : (associatorZ 2 6 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_6 : (associatorZ 2 6 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_7 : (associatorZ 2 6 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 2 6 3 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_0_0_4
  · exact assocBCA_row_0_0_5
  · exact assocBCA_row_0_0_6
  · exact assocBCA_row_0_0_7
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_0_4
  · exact assocBCA_row_1_0_5
  · exact assocBCA_row_1_0_6
  · exact assocBCA_row_1_0_7
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_0_2
  · exact assocBCA_row_2_0_3
  · exact assocBCA_row_2_0_4
  · exact assocBCA_row_2_0_5
  · exact assocBCA_row_2_0_6
  · exact assocBCA_row_2_0_7
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_0_2
  · exact assocBCA_row_3_0_3
  · exact assocBCA_row_3_0_4
  · exact assocBCA_row_3_0_5
  · exact assocBCA_row_3_0_6
  · exact assocBCA_row_3_0_7

def innerRightBAC : Matrix (RightIndex 2 6 3) (RightIndex 2 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 2 3 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 2 3 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_4 : (innerRightZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_5 : (innerRightZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_6 : (innerRightZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_7 : (innerRightZ 2 3 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_4 : (innerRightZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_5 : (innerRightZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_6 : (innerRightZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_7 : (innerRightZ 2 3 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 2 3 6 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_0_2
  · exact innerRightBAC_row_0_0_3
  · exact innerRightBAC_row_0_0_4
  · exact innerRightBAC_row_0_0_5
  · exact innerRightBAC_row_0_0_6
  · exact innerRightBAC_row_0_0_7
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_1_0_4
  · exact innerRightBAC_row_1_0_5
  · exact innerRightBAC_row_1_0_6
  · exact innerRightBAC_row_1_0_7
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_0_2
  · exact innerRightBAC_row_2_0_3
  · exact innerRightBAC_row_2_0_4
  · exact innerRightBAC_row_2_0_5
  · exact innerRightBAC_row_2_0_6
  · exact innerRightBAC_row_2_0_7
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_0_2
  · exact innerRightBAC_row_3_0_3
  · exact innerRightBAC_row_3_0_4
  · exact innerRightBAC_row_3_0_5
  · exact innerRightBAC_row_3_0_6
  · exact innerRightBAC_row_3_0_7

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 728214340506280,
    decodeIntegerRow 32 3 1 311284809799968,
    decodeIntegerRow 32 3 1 902782402397824,
    decodeIntegerRow 32 3 1 857586769714480,
    decodeIntegerRow 32 3 1 1546819888738640,
    decodeIntegerRow 32 3 1 1140059366775424,
    decodeIntegerRow 32 3 1 858151743583072,
    decodeIntegerRow 32 3 1 904477228329640,
    decodeIntegerRow 32 3 1 902789634245440,
    decodeIntegerRow 32 3 1 995412412333120,
    decodeIntegerRow 32 3 1 1124745410749120,
    decodeIntegerRow 32 3 1 311472321316160,
    decodeIntegerRow 32 3 1 858172578191680,
    decodeIntegerRow 32 3 1 948536245232320,
    decodeIntegerRow 32 3 1 306389361312320,
    decodeIntegerRow 32 3 1 1139994280133440,
    decodeIntegerRow 32 3 1 904477237542688,
    decodeIntegerRow 32 3 1 994868473852840,
    decodeIntegerRow 32 3 1 1140059367877840,
    decodeIntegerRow 32 3 1 306200303315456,
    decodeIntegerRow 32 3 1 995433390317056,
    decodeIntegerRow 32 3 1 902782392476080,
    decodeIntegerRow 32 3 1 1541735382227880,
    decodeIntegerRow 32 3 1 728214341529952,
    decodeIntegerRow 32 3 1 1139994281235520,
    decodeIntegerRow 32 3 1 1546630824338240,
    decodeIntegerRow 32 3 1 948536236022080,
    decodeIntegerRow 32 3 1 994847639235520,
    decodeIntegerRow 32 3 1 1541547870710720,
    decodeIntegerRow 32 3 1 1124745409725760,
    decodeIntegerRow 32 3 1 857607805330240,
    decodeIntegerRow 32 3 1 902789624326720]

def assocCAB : Matrix (RightIndex 6 3 2) (LeftIndex 6 3 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 3 2 r) []).getD (leftPosition 6 3 2 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 6 3 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 6 3 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 6 3 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 6 3 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_4 : (associatorZ 6 3 2) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_5 : (associatorZ 6 3 2) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_6 : (associatorZ 6 3 2) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_7 : (associatorZ 6 3 2) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_0 : (associatorZ 6 3 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_1 : (associatorZ 6 3 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_2 : (associatorZ 6 3 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_3 : (associatorZ 6 3 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_4 : (associatorZ 6 3 2) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_5 : (associatorZ 6 3 2) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_6 : (associatorZ 6 3 2) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_7 : (associatorZ 6 3 2) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 6 3 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 6 3 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 6 3 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 6 3 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_4 : (associatorZ 6 3 2) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_5 : (associatorZ 6 3 2) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_6 : (associatorZ 6 3 2) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_7 : (associatorZ 6 3 2) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_0 : (associatorZ 6 3 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_1 : (associatorZ 6 3 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_2 : (associatorZ 6 3 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_3 : (associatorZ 6 3 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_4 : (associatorZ 6 3 2) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_5 : (associatorZ 6 3 2) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_6 : (associatorZ 6 3 2) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_7 : (associatorZ 6 3 2) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 6 3 2 = assocCAB := by
  funext r
  fin_cases r
  · exact assocCAB_row_0_0_0
  · exact assocCAB_row_0_0_1
  · exact assocCAB_row_0_0_2
  · exact assocCAB_row_0_0_3
  · exact assocCAB_row_0_0_4
  · exact assocCAB_row_0_0_5
  · exact assocCAB_row_0_0_6
  · exact assocCAB_row_0_0_7
  · exact assocCAB_row_0_1_0
  · exact assocCAB_row_0_1_1
  · exact assocCAB_row_0_1_2
  · exact assocCAB_row_0_1_3
  · exact assocCAB_row_0_1_4
  · exact assocCAB_row_0_1_5
  · exact assocCAB_row_0_1_6
  · exact assocCAB_row_0_1_7
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_1_0_4
  · exact assocCAB_row_1_0_5
  · exact assocCAB_row_1_0_6
  · exact assocCAB_row_1_0_7
  · exact assocCAB_row_1_1_0
  · exact assocCAB_row_1_1_1
  · exact assocCAB_row_1_1_2
  · exact assocCAB_row_1_1_3
  · exact assocCAB_row_1_1_4
  · exact assocCAB_row_1_1_5
  · exact assocCAB_row_1_1_6
  · exact assocCAB_row_1_1_7

def outerLeftABC : Matrix (RightIndex 6 3 2) (LeftIndex 3 2 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 3 2 6) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_4 : (outerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_5 : (outerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_6 : (outerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_7 : (outerLeftZ 3 2 6) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 3 2 6) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_4 : (outerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_5 : (outerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_6 : (outerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_7 : (outerLeftZ 3 2 6) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 2 6 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_0_0_4
  · exact outerLeftABC_row_0_0_5
  · exact outerLeftABC_row_0_0_6
  · exact outerLeftABC_row_0_0_7
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_1_2
  · exact outerLeftABC_row_0_1_3
  · exact outerLeftABC_row_0_1_4
  · exact outerLeftABC_row_0_1_5
  · exact outerLeftABC_row_0_1_6
  · exact outerLeftABC_row_0_1_7
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_0_4
  · exact outerLeftABC_row_1_0_5
  · exact outerLeftABC_row_1_0_6
  · exact outerLeftABC_row_1_0_7
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_1_2
  · exact outerLeftABC_row_1_1_3
  · exact outerLeftABC_row_1_1_4
  · exact outerLeftABC_row_1_1_5
  · exact outerLeftABC_row_1_1_6
  · exact outerLeftABC_row_1_1_7

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms326
