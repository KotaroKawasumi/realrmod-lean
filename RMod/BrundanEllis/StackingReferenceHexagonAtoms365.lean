import RMod.BrundanEllis.StackingReferenceHexagonAtoms356
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926415822107660,
    decodeIntegerRow 32 3 1 926541432436624,
    decodeIntegerRow 32 3 1 926498471811340,
    decodeIntegerRow 32 3 1 926513193789616,
    decodeIntegerRow 32 3 1 926416080386528,
    decodeIntegerRow 32 3 1 926541518534440,
    decodeIntegerRow 32 3 1 926500796334112,
    decodeIntegerRow 32 3 1 926513968631080,
    decodeIntegerRow 32 3 1 1002766069866280,
    decodeIntegerRow 32 3 1 946845022469728,
    decodeIntegerRow 32 3 1 1545030784108840,
    decodeIntegerRow 32 3 1 1132118811313312,
    decodeIntegerRow 32 3 1 865505315018416,
    decodeIntegerRow 32 3 1 901091437914100,
    decodeIntegerRow 32 3 1 309683991527824,
    decodeIntegerRow 32 3 1 720336547163380,
    decodeIntegerRow 32 3 1 926478756410848,
    decodeIntegerRow 32 3 1 926604366745640,
    decodeIntegerRow 32 3 1 926506995061792,
    decodeIntegerRow 32 3 1 926521717040680,
    decodeIntegerRow 32 3 1 926478670321780,
    decodeIntegerRow 32 3 1 926604108463856,
    decodeIntegerRow 32 3 1 926506220221300,
    decodeIntegerRow 32 3 1 926519392517584,
    decodeIntegerRow 32 3 1 946845019635376,
    decodeIntegerRow 32 3 1 1002766068685300,
    decodeIntegerRow 32 3 1 1132118782654864,
    decodeIntegerRow 32 3 1 1545030774529780,
    decodeIntegerRow 32 3 1 901091434371160,
    decodeIntegerRow 32 3 1 865505314073632,
    decodeIntegerRow 32 3 1 720336518426200,
    decodeIntegerRow 32 3 1 309683981975008]

def assocABC : Matrix (RightIndex 3 6 5) (LeftIndex 3 6 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 6 5 r) []).getD (leftPosition 3 6 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = assocABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = assocABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = assocABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = assocABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = assocABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = assocABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = assocABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = assocABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_0 : (associatorZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = assocABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_1 : (associatorZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = assocABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_2 : (associatorZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = assocABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_3 : (associatorZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = assocABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_0 : (associatorZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = assocABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_1 : (associatorZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = assocABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_2 : (associatorZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = assocABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_3 : (associatorZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = assocABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = assocABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = assocABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = assocABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = assocABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = assocABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = assocABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = assocABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = assocABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_0 : (associatorZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = assocABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_1 : (associatorZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = assocABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_2 : (associatorZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = assocABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_3 : (associatorZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = assocABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_0 : (associatorZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = assocABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_1 : (associatorZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = assocABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_2 : (associatorZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = assocABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_3 : (associatorZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = assocABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 6 5 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_0_2
  · exact assocABC_row_0_0_3
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_1_2
  · exact assocABC_row_0_1_3
  · exact assocABC_row_0_2_0
  · exact assocABC_row_0_2_1
  · exact assocABC_row_0_2_2
  · exact assocABC_row_0_2_3
  · exact assocABC_row_0_3_0
  · exact assocABC_row_0_3_1
  · exact assocABC_row_0_3_2
  · exact assocABC_row_0_3_3
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_1_2
  · exact assocABC_row_1_1_3
  · exact assocABC_row_1_2_0
  · exact assocABC_row_1_2_1
  · exact assocABC_row_1_2_2
  · exact assocABC_row_1_2_3
  · exact assocABC_row_1_3_0
  · exact assocABC_row_1_3_1
  · exact assocABC_row_1_3_2
  · exact assocABC_row_1_3_3

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510080778548,
    decodeIntegerRow 32 3 1 926510100726776,
    decodeIntegerRow 32 3 1 926510097577332,
    decodeIntegerRow 32 3 1 926510109123544,
    decodeIntegerRow 32 3 1 926510108072308,
    decodeIntegerRow 32 3 1 926510088129656,
    decodeIntegerRow 32 3 1 926510091278772,
    decodeIntegerRow 32 3 1 926510079730264,
    decodeIntegerRow 32 3 1 926510100884184,
    decodeIntegerRow 32 3 1 926510080437388,
    decodeIntegerRow 32 3 1 926510109490936,
    decodeIntegerRow 32 3 1 926510097656012,
    decodeIntegerRow 32 3 1 926510100879704,
    decodeIntegerRow 32 3 1 926510080438348,
    decodeIntegerRow 32 3 1 926510109489016,
    decodeIntegerRow 32 3 1 926510097651852,
    decodeIntegerRow 32 3 1 1513984709293132,
    decodeIntegerRow 32 3 1 655278904132744,
    decodeIntegerRow 32 3 1 790852141305868,
    decodeIntegerRow 32 3 1 293825574735016,
    decodeIntegerRow 32 3 1 339077837532172,
    decodeIntegerRow 32 3 1 1197543614176264,
    decodeIntegerRow 32 3 1 1061984496327628,
    decodeIntegerRow 32 3 1 1559109898169896,
    decodeIntegerRow 32 3 1 648503005873576,
    decodeIntegerRow 32 3 1 1528670528629492,
    decodeIntegerRow 32 3 1 278010553813384,
    decodeIntegerRow 32 3 1 787465225297588,
    decodeIntegerRow 32 3 1 648695855183656,
    decodeIntegerRow 32 3 1 1528629203777332,
    decodeIntegerRow 32 3 1 278093203517704,
    decodeIntegerRow 32 3 1 787644299656948]

def outerABC : Matrix (LeftIndex 6 5 3) (RightIndex 3 6 5) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 6 5 3 r) []).getD (rightPosition 3 6 5 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_0 : (outerRightZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_1 : (outerRightZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_2 : (outerRightZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_3 : (outerRightZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_0 : (outerRightZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_1 : (outerRightZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_2 : (outerRightZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_3 : (outerRightZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_0 : (outerRightZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_1 : (outerRightZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_2 : (outerRightZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_3 : (outerRightZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_0 : (outerRightZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_1 : (outerRightZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_2 : (outerRightZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_3 : (outerRightZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 6 5 = outerABC := by
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

def assocBAC : Matrix (RightIndex 6 3 5) (LeftIndex 6 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocCAB

theorem assocBAC_eq : associatorZ 6 3 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 3 5) (LeftIndex 3 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.innerACB

theorem innerABC_eq : innerLeftZ 3 6 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 5 6) (RightIndex 3 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 4) (Fin 2 × Fin 4 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 6 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 6 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_0 : (innerRightZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_1 : (innerRightZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_2 : (innerRightZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_3 : (innerRightZ 3 6 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_0 : (innerRightZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_1 : (innerRightZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_2 : (innerRightZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_3 : (innerRightZ 3 6 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 6 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 6 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_0 : (innerRightZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_1 : (innerRightZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_2 : (innerRightZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_3 : (innerRightZ 3 6 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_0 : (innerRightZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_1 : (innerRightZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_2 : (innerRightZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_3 : (innerRightZ 3 6 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 6 5 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 293847267056684,
    decodeIntegerRow 32 3 1 1062172711655404,
    decodeIntegerRow 32 3 1 655467290572876,
    decodeIntegerRow 32 3 1 339097989855756,
    decodeIntegerRow 32 3 1 1514004861612452,
    decodeIntegerRow 32 3 1 655288188237412,
    decodeIntegerRow 32 3 1 791040356634628,
    decodeIntegerRow 32 3 1 293888598364868,
    decodeIntegerRow 32 3 1 324412686922532,
    decodeIntegerRow 32 3 1 1204328969066212,
    decodeIntegerRow 32 3 1 1065564276342148,
    decodeIntegerRow 32 3 1 1574989492320068,
    decodeIntegerRow 32 3 1 1574947128048044,
    decodeIntegerRow 32 3 1 787653612445804,
    decodeIntegerRow 32 3 1 1204512547578316,
    decodeIntegerRow 32 3 1 1528692230473356,
    decodeIntegerRow 32 3 1 787653583051564,
    decodeIntegerRow 32 3 1 1574947134351084,
    decodeIntegerRow 32 3 1 1528692217880396,
    decodeIntegerRow 32 3 1 1204512520286476,
    decodeIntegerRow 32 3 1 648691192489948,
    decodeIntegerRow 32 3 1 1528607514530588,
    decodeIntegerRow 32 3 1 278030702825852,
    decodeIntegerRow 32 3 1 787455941902012,
    decodeIntegerRow 32 3 1 655288216211548,
    decodeIntegerRow 32 3 1 1514004848704668,
    decodeIntegerRow 32 3 1 293888591904252,
    decodeIntegerRow 32 3 1 791040326505532,
    decodeIntegerRow 32 3 1 790847507323564,
    decodeIntegerRow 32 3 1 1559172915343724,
    decodeIntegerRow 32 3 1 1513922211912396,
    decodeIntegerRow 32 3 1 1197552926257036]

def inverseACB : Matrix (LeftIndex 3 5 6) (RightIndex 3 5 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 5 6 r) []).getD (rightPosition 3 5 6 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 5 6 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 5 3 6) (LeftIndex 3 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.innerABC

theorem innerACB_eq : innerLeftZ 3 5 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 994200187738192,
    decodeIntegerRow 32 3 1 949135455825620,
    decodeIntegerRow 32 3 1 1536547560400048,
    decodeIntegerRow 32 3 1 1129862804968660,
    decodeIntegerRow 32 3 1 1129855917491824,
    decodeIntegerRow 32 3 1 316451966030140,
    decodeIntegerRow 32 3 1 949073468547216,
    decodeIntegerRow 32 3 1 858634039279420,
    decodeIntegerRow 32 3 1 856937108839300,
    decodeIntegerRow 32 3 1 903382645638416,
    decodeIntegerRow 32 3 1 301200509586820,
    decodeIntegerRow 32 3 1 718080626858224,
    decodeIntegerRow 32 3 1 718073567197420,
    decodeIntegerRow 32 3 1 1551798500273968,
    decodeIntegerRow 32 3 1 903319108678380,
    decodeIntegerRow 32 3 1 995892469131472,
    decodeIntegerRow 32 3 1 1551798497129008,
    decodeIntegerRow 32 3 1 718073566146220,
    decodeIntegerRow 32 3 1 995892440788432,
    decodeIntegerRow 32 3 1 903319099230380,
    decodeIntegerRow 32 3 1 949637552661104,
    decodeIntegerRow 32 3 1 996083051668540,
    decodeIntegerRow 32 3 1 1134939563041936,
    decodeIntegerRow 32 3 1 1551819676111420,
    decodeIntegerRow 32 3 1 316451962797700,
    decodeIntegerRow 32 3 1 1129855916417296,
    decodeIntegerRow 32 3 1 858634010226820,
    decodeIntegerRow 32 3 1 949073458863344,
    decodeIntegerRow 32 3 1 903884742710420,
    decodeIntegerRow 32 3 1 858819972062032,
    decodeIntegerRow 32 3 1 723157384960660,
    decodeIntegerRow 32 3 1 316472625228208]

def assocBCA : Matrix (RightIndex 6 5 3) (LeftIndex 6 5 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 5 3 r) []).getD (leftPosition 6 5 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_0 : (associatorZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_1 : (associatorZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_2 : (associatorZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_3 : (associatorZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_0 : (associatorZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_1 : (associatorZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_2 : (associatorZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_3 : (associatorZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_0 : (associatorZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_1 : (associatorZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_2 : (associatorZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_3 : (associatorZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_0 : (associatorZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_1 : (associatorZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_2 : (associatorZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_3 : (associatorZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 6 5 3 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_0_2
  · exact assocBCA_row_2_0_3
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_0_2
  · exact assocBCA_row_3_0_3
  · exact assocBCA_row_4_0_0
  · exact assocBCA_row_4_0_1
  · exact assocBCA_row_4_0_2
  · exact assocBCA_row_4_0_3
  · exact assocBCA_row_5_0_0
  · exact assocBCA_row_5_0_1
  · exact assocBCA_row_5_0_2
  · exact assocBCA_row_5_0_3
  · exact assocBCA_row_6_0_0
  · exact assocBCA_row_6_0_1
  · exact assocBCA_row_6_0_2
  · exact assocBCA_row_6_0_3
  · exact assocBCA_row_7_0_0
  · exact assocBCA_row_7_0_1
  · exact assocBCA_row_7_0_2
  · exact assocBCA_row_7_0_3

def innerRightBAC : Matrix (RightIndex 6 5 3) (RightIndex 6 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_0 : (innerRightZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_1 : (innerRightZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_2 : (innerRightZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_3 : (innerRightZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_0 : (innerRightZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_1 : (innerRightZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_2 : (innerRightZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_3 : (innerRightZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_0 : (innerRightZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_1 : (innerRightZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_2 : (innerRightZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_3 : (innerRightZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_0 : (innerRightZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_1 : (innerRightZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_2 : (innerRightZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_3 : (innerRightZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 6 3 5 = innerRightBAC := by
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

def assocCAB : Matrix (RightIndex 5 3 6) (LeftIndex 5 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBAC

theorem assocCAB_eq : associatorZ 5 3 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425919,
    decodeIntegerRow 32 3 1 926510094425917,
    decodeIntegerRow 32 3 1 926510094425911,
    decodeIntegerRow 32 3 1 926510094425893,
    decodeIntegerRow 32 3 1 926510094425839,
    decodeIntegerRow 32 3 1 926510094425677,
    decodeIntegerRow 32 3 1 926510094425191,
    decodeIntegerRow 32 3 1 926510094423733,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094406237,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510094248773,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510089642951,
    decodeIntegerRow 32 3 1 926510080077013,
    decodeIntegerRow 32 3 1 926510137472641,
    decodeIntegerRow 32 3 1 926510223566083,
    decodeIntegerRow 32 3 1 926510481846409,
    decodeIntegerRow 32 3 1 926511256687387,
    decodeIntegerRow 32 3 1 926513581210321,
    decodeIntegerRow 32 3 1 926520554779123,
    decodeIntegerRow 32 3 1 926541475485529,
    decodeIntegerRow 32 3 1 926604237604747,
    decodeIntegerRow 32 3 1 926792523962401,
    decodeIntegerRow 32 3 1 927357383035363,
    decodeIntegerRow 32 3 1 929051960254249,
    decodeIntegerRow 32 3 1 934135691910907,
    decodeIntegerRow 32 3 1 949386886880881,
    decodeIntegerRow 32 3 1 995140471790803,
    decodeIntegerRow 32 3 1 1132401226520569,
    decodeIntegerRow 32 3 1 1544183490709867]

def outerLeftABC : Matrix (RightIndex 5 3 6) (LeftIndex 3 6 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 3 6 r) []).getD (leftPosition 3 6 5 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 6 5 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365
