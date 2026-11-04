import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1541611407684364,
    decodeIntegerRow 32 3 1 728150804608800,
    decodeIntegerRow 32 3 1 995419271112160,
    decodeIntegerRow 32 3 1 902775505357948,
    decodeIntegerRow 32 3 1 713087895957600,
    decodeIntegerRow 32 3 1 1546757901446956,
    decodeIntegerRow 32 3 1 948529185927268,
    decodeIntegerRow 32 3 1 858158803360480,
    decodeIntegerRow 32 3 1 712898833735452,
    decodeIntegerRow 32 3 1 306327377222560,
    decodeIntegerRow 32 3 1 904470178231840,
    decodeIntegerRow 32 3 1 858165489833044,
    decodeIntegerRow 32 3 1 311348346772960,
    decodeIntegerRow 32 3 1 728338315023228,
    decodeIntegerRow 32 3 1 995426531541004,
    decodeIntegerRow 32 3 1 950223667482400,
    decodeIntegerRow 32 3 1 857593685889148,
    decodeIntegerRow 32 3 1 902796512153440,
    decodeIntegerRow 32 3 1 1541671845280480,
    decodeIntegerRow 32 3 1 1124681872725876,
    decodeIntegerRow 32 3 1 904470168316000,
    decodeIntegerRow 32 3 1 858165518650468,
    decodeIntegerRow 32 3 1 712898834758484,
    decodeIntegerRow 32 3 1 306327374046880,
    decodeIntegerRow 32 3 1 948529176002644,
    decodeIntegerRow 32 3 1 858158774546080,
    decodeIntegerRow 32 3 1 713087894933600,
    decodeIntegerRow 32 3 1 1546757898271588,
    decodeIntegerRow 32 3 1 857600889158560,
    decodeIntegerRow 32 3 1 950244674286604,
    decodeIntegerRow 32 3 1 311408784369412,
    decodeIntegerRow 32 3 1 1124869385344800]

def assocABC : Matrix (RightIndex 5 1 5) (LeftIndex 5 1 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 1 5 r) []).getD (leftPosition 5 1 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_4 : (associatorZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_5 : (associatorZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_6 : (associatorZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_7 : (associatorZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_4 : (associatorZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_5 : (associatorZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_6 : (associatorZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_7 : (associatorZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 5 1 5 = assocABC := by
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
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_1_2
  · exact assocABC_row_0_1_3
  · exact assocABC_row_0_1_4
  · exact assocABC_row_0_1_5
  · exact assocABC_row_0_1_6
  · exact assocABC_row_0_1_7
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_0_4
  · exact assocABC_row_1_0_5
  · exact assocABC_row_1_0_6
  · exact assocABC_row_1_0_7
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_1_2
  · exact assocABC_row_1_1_3
  · exact assocABC_row_1_1_4
  · exact assocABC_row_1_1_5
  · exact assocABC_row_1_1_6
  · exact assocABC_row_1_1_7

def outerABC : Matrix (LeftIndex 1 5 5) (RightIndex 5 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_4 : (outerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_5 : (outerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_6 : (outerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_7 : (outerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_4 : (outerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_5 : (outerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_6 : (outerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_7 : (outerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 1 5 = outerABC := by
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
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_1_2
  · exact outerABC_row_0_1_3
  · exact outerABC_row_0_1_4
  · exact outerABC_row_0_1_5
  · exact outerABC_row_0_1_6
  · exact outerABC_row_0_1_7
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_0_4
  · exact outerABC_row_1_0_5
  · exact outerABC_row_1_0_6
  · exact outerABC_row_1_0_7
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_1_1_4
  · exact outerABC_row_1_1_5
  · exact outerABC_row_1_1_6
  · exact outerABC_row_1_1_7

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1193590532851412,
    decodeIntegerRow 32 3 1 1565408672777932,
    decodeIntegerRow 32 3 1 335124774056356,
    decodeIntegerRow 32 3 1 797066180024324,
    decodeIntegerRow 32 3 1 328304624131204,
    decodeIntegerRow 32 3 1 781431438611804,
    decodeIntegerRow 32 3 1 1208472128598092,
    decodeIntegerRow 32 3 1 1568714144735788,
    decodeIntegerRow 32 3 1 1071588722446724,
    decodeIntegerRow 32 3 1 1524715571461156,
    decodeIntegerRow 32 3 1 1568714131635508,
    decodeIntegerRow 32 3 1 1208472158435628,
    decodeIntegerRow 32 3 1 1565408660369068,
    decodeIntegerRow 32 3 1 1193590562535372,
    decodeIntegerRow 32 3 1 1055953981351076,
    decodeIntegerRow 32 3 1 1517895420809596,
    decodeIntegerRow 32 3 1 328344054931828,
    decodeIntegerRow 32 3 1 1071769029906668,
    decodeIntegerRow 32 3 1 644742803621444,
    decodeIntegerRow 32 3 1 1568795589127396,
    decodeIntegerRow 32 3 1 659233879511324,
    decodeIntegerRow 32 3 1 1565322751527364,
    decodeIntegerRow 32 3 1 335080522022932,
    decodeIntegerRow 32 3 1 1055771662918388,
    decodeIntegerRow 32 3 1 1565322739109404,
    decodeIntegerRow 32 3 1 659233849831356,
    decodeIntegerRow 32 3 1 797248553411948,
    decodeIntegerRow 32 3 1 1517939672834548,
    decodeIntegerRow 32 3 1 781251186736652,
    decodeIntegerRow 32 3 1 1524676140668908,
    decodeIntegerRow 32 3 1 1568795576036164,
    decodeIntegerRow 32 3 1 644742773780124]

def assocBAC : Matrix (RightIndex 1 5 5) (LeftIndex 1 5 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 5 5 r) []).getD (leftPosition 1 5 5 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_4 : (associatorZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_5 : (associatorZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_6 : (associatorZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_7 : (associatorZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_4 : (associatorZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_5 : (associatorZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_6 : (associatorZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_7 : (associatorZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_4 : (associatorZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_5 : (associatorZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_6 : (associatorZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_7 : (associatorZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_4 : (associatorZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_5 : (associatorZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_6 : (associatorZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_7 : (associatorZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 1 5 5 = assocBAC := by
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

def innerABC : Matrix (LeftIndex 1 5 5) (LeftIndex 5 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_4 : (innerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_5 : (innerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_6 : (innerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_7 : (innerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_4 : (innerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_5 : (innerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_6 : (innerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_7 : (innerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 5 1 5 = innerABC := by
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

def innerRightABC : Matrix (RightIndex 5 5 1) (RightIndex 5 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_4 : (innerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_5 : (innerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_6 : (innerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_7 : (innerRightZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_4 : (innerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_5 : (innerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_6 : (innerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_7 : (innerRightZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 5 1 5 = innerRightABC := by
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
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_1_2
  · exact innerRightABC_row_0_1_3
  · exact innerRightABC_row_0_1_4
  · exact innerRightABC_row_0_1_5
  · exact innerRightABC_row_0_1_6
  · exact innerRightABC_row_0_1_7
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_0_4
  · exact innerRightABC_row_1_0_5
  · exact innerRightABC_row_1_0_6
  · exact innerRightABC_row_1_0_7
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_1_2
  · exact innerRightABC_row_1_1_3
  · exact innerRightABC_row_1_1_4
  · exact innerRightABC_row_1_1_5
  · exact innerRightABC_row_1_1_6
  · exact innerRightABC_row_1_1_7

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510051379118,
    decodeIntegerRow 32 3 1 926509965286000,
    decodeIntegerRow 32 3 1 926509707006160,
    decodeIntegerRow 32 3 1 926508932162266,
    decodeIntegerRow 32 3 1 926506607641520,
    decodeIntegerRow 32 3 1 926499634072714,
    decodeIntegerRow 32 3 1 926478713366302,
    decodeIntegerRow 32 3 1 926415951247120,
    decodeIntegerRow 32 3 1 949386886874320,
    decodeIntegerRow 32 3 1 857879717041354,
    decodeIntegerRow 32 3 1 720618962272222,
    decodeIntegerRow 32 3 1 1544183490532720,
    decodeIntegerRow 32 3 1 926227664357998,
    decodeIntegerRow 32 3 1 927357381441040,
    decodeIntegerRow 32 3 1 929051955471280,
    decodeIntegerRow 32 3 1 918884482592026,
    decodeIntegerRow 32 3 1 926506607641518,
    decodeIntegerRow 32 3 1 926520554779120,
    decodeIntegerRow 32 3 1 926541475485520,
    decodeIntegerRow 32 3 1 926415951247066,
    decodeIntegerRow 32 3 1 926510137472560,
    decodeIntegerRow 32 3 1 926509965285514,
    decodeIntegerRow 32 3 1 926509707004702,
    decodeIntegerRow 32 3 1 926511256685200,
    decodeIntegerRow 32 3 1 926792523430960,
    decodeIntegerRow 32 3 1 927357384629686,
    decodeIntegerRow 32 3 1 929051965037218,
    decodeIntegerRow 32 3 1 934135677562000,
    decodeIntegerRow 32 3 1 949386886887442,
    decodeIntegerRow 32 3 1 995140471771120,
    decodeIntegerRow 32 3 1 1132401226461520,
    decodeIntegerRow 32 3 1 1544183490887014]

def inverseACB : Matrix (LeftIndex 5 5 1) (RightIndex 5 5 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 5 1 r) []).getD (rightPosition 5 5 1 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 5 1 = inverseACB := by
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

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 934419240583408,
    decodeIntegerRow 32 3 1 929899507327700,
    decodeIntegerRow 32 3 1 928204154913540,
    decodeIntegerRow 32 3 1 933852057105616,
    decodeIntegerRow 32 3 1 1567150933182448,
    decodeIntegerRow 32 3 1 1201052539470100,
    decodeIntegerRow 32 3 1 1063728993923140,
    decodeIntegerRow 32 3 1 1521209071481296,
    decodeIntegerRow 32 3 1 933852057026860,
    decodeIntegerRow 32 3 1 928204155254768,
    decodeIntegerRow 32 3 1 923120681891504,
    decodeIntegerRow 32 3 1 918600948110980,
    decodeIntegerRow 32 3 1 1521209065102060,
    decodeIntegerRow 32 3 1 1063729021562608,
    decodeIntegerRow 32 3 1 651967679138224,
    decodeIntegerRow 32 3 1 285869242915780,
    decodeIntegerRow 32 3 1 928205188034900,
    decodeIntegerRow 32 3 1 919165721129872,
    decodeIntegerRow 32 3 1 918603186697936,
    decodeIntegerRow 32 3 1 929898990767100,
    decodeIntegerRow 32 3 1 1063812676753300,
    decodeIntegerRow 32 3 1 331615857446032,
    decodeIntegerRow 32 3 1 286050568459216,
    decodeIntegerRow 32 3 1 1201010698061500,
    decodeIntegerRow 32 3 1 923121198452208,
    decodeIntegerRow 32 3 1 934417002311380,
    decodeIntegerRow 32 3 1 919165721208580,
    decodeIntegerRow 32 3 1 928205188376016,
    decodeIntegerRow 32 3 1 652009520555248,
    decodeIntegerRow 32 3 1 1566969633148180,
    decodeIntegerRow 32 3 1 331615863821380,
    decodeIntegerRow 32 3 1 1063812704383696]

def innerACB : Matrix (LeftIndex 5 5 1) (LeftIndex 5 5 1) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 5 5 1 r) []).getD (leftPosition 5 5 1 s) 0

private theorem innerACB_row_0_0_0 : (innerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_4 : (innerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_5 : (innerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_6 : (innerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_7 : (innerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_4 : (innerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_5 : (innerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_6 : (innerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_7 : (innerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 5 5 1 = innerACB := by
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

def assocBCA : Matrix (RightIndex 1 5 5) (LeftIndex 1 5 5) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 1 5 5 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1132714993479520,
    decodeIntegerRow 32 3 1 1545124795129228,
    decodeIntegerRow 32 3 1 951931856861924,
    decodeIntegerRow 32 3 1 1002775353001120,
    decodeIntegerRow 32 3 1 946841142070524,
    decodeIntegerRow 32 3 1 987503266022560,
    decodeIntegerRow 32 3 1 1132087373350240,
    decodeIntegerRow 32 3 1 1543241928363988,
    decodeIntegerRow 32 3 1 1132087372405276,
    decodeIntegerRow 32 3 1 1543241931198880,
    decodeIntegerRow 32 3 1 946841151624800,
    decodeIntegerRow 32 3 1 987503237359732,
    decodeIntegerRow 32 3 1 901088341567520,
    decodeIntegerRow 32 3 1 850244807117908,
    decodeIntegerRow 32 3 1 720305194191484,
    decodeIntegerRow 32 3 1 307895397265120,
    decodeIntegerRow 32 3 1 946848890481764,
    decodeIntegerRow 32 3 1 865493677604320,
    decodeIntegerRow 32 3 1 720869967289120,
    decodeIntegerRow 32 3 1 1543430473002508,
    decodeIntegerRow 32 3 1 720367871398240,
    decodeIntegerRow 32 3 1 1544936767052332,
    decodeIntegerRow 32 3 1 951925658135556,
    decodeIntegerRow 32 3 1 850263432038560,
    decodeIntegerRow 32 3 1 901094540296800,
    decodeIntegerRow 32 3 1 1002756785554828,
    decodeIntegerRow 32 3 1 1132652318634724,
    decodeIntegerRow 32 3 1 308083425342880,
    decodeIntegerRow 32 3 1 720869968233724,
    decodeIntegerRow 32 3 1 1543430475836320,
    decodeIntegerRow 32 3 1 946848900033120,
    decodeIntegerRow 32 3 1 865493706258388]

def innerRightBAC : Matrix (RightIndex 1 5 5) (RightIndex 1 5 5) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 1 5 5 r) []).getD (rightPosition 1 5 5 s) 0

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 1 5 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 1 5 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_4 : (innerRightZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_5 : (innerRightZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_6 : (innerRightZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_7 : (innerRightZ 1 5 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_4 : (innerRightZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_5 : (innerRightZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_6 : (innerRightZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_7 : (innerRightZ 1 5 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 1 5 5 = innerRightBAC := by
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

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510051379280,
    decodeIntegerRow 32 3 1 926509965285514,
    decodeIntegerRow 32 3 1 926509707004702,
    decodeIntegerRow 32 3 1 926508932166640,
    decodeIntegerRow 32 3 1 926506607641518,
    decodeIntegerRow 32 3 1 926499634072720,
    decodeIntegerRow 32 3 1 926478713366320,
    decodeIntegerRow 32 3 1 926415951247066,
    decodeIntegerRow 32 3 1 949386886874320,
    decodeIntegerRow 32 3 1 857879717041354,
    decodeIntegerRow 32 3 1 720618962272222,
    decodeIntegerRow 32 3 1 1544183490532720,
    decodeIntegerRow 32 3 1 926227664357998,
    decodeIntegerRow 32 3 1 927357381441040,
    decodeIntegerRow 32 3 1 929051955471280,
    decodeIntegerRow 32 3 1 918884482592026,
    decodeIntegerRow 32 3 1 926513581210320,
    decodeIntegerRow 32 3 1 926499634072714,
    decodeIntegerRow 32 3 1 926478713366302,
    decodeIntegerRow 32 3 1 926604237604720,
    decodeIntegerRow 32 3 1 926510051379118,
    decodeIntegerRow 32 3 1 926510223565840,
    decodeIntegerRow 32 3 1 926510481845680,
    decodeIntegerRow 32 3 1 926508932162266,
    decodeIntegerRow 32 3 1 926792523430960,
    decodeIntegerRow 32 3 1 927357384629686,
    decodeIntegerRow 32 3 1 929051965037218,
    decodeIntegerRow 32 3 1 934135677562000,
    decodeIntegerRow 32 3 1 949386886887442,
    decodeIntegerRow 32 3 1 995140471771120,
    decodeIntegerRow 32 3 1 1132401226461520,
    decodeIntegerRow 32 3 1 1544183490887014]

def assocCAB : Matrix (RightIndex 5 5 1) (LeftIndex 5 5 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 5 5 1 r) []).getD (leftPosition 5 5 1 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_4 : (associatorZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_5 : (associatorZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_6 : (associatorZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_7 : (associatorZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_0 : (associatorZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_1 : (associatorZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_2 : (associatorZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_3 : (associatorZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_4 : (associatorZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_5 : (associatorZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_6 : (associatorZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_7 : (associatorZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_4 : (associatorZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_5 : (associatorZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_6 : (associatorZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_7 : (associatorZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_0 : (associatorZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_1 : (associatorZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_2 : (associatorZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_3 : (associatorZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_4 : (associatorZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_5 : (associatorZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_6 : (associatorZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_7 : (associatorZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 5 5 1 = assocCAB := by
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

def outerLeftABC : Matrix (RightIndex 5 5 1) (LeftIndex 5 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_4 : (outerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_5 : (outerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_6 : (outerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_7 : (outerLeftZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_4 : (outerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_5 : (outerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_6 : (outerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_7 : (outerLeftZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 1 5 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515
