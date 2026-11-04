import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 785902271320004,
    decodeIntegerRow 32 3 1 1574311595748172,
    decodeIntegerRow 32 3 1 1513495185250276,
    decodeIntegerRow 32 3 1 1199357445865388,
    decodeIntegerRow 32 3 1 785818099201244,
    decodeIntegerRow 32 3 1 1574495306477548,
    decodeIntegerRow 32 3 1 1513302157218556,
    decodeIntegerRow 32 3 1 1199316607472012,
    decodeIntegerRow 32 3 1 323706717508372,
    decodeIntegerRow 32 3 1 1202747603659556,
    decodeIntegerRow 32 3 1 1060340097586548,
    decodeIntegerRow 32 3 1 1559627657713924,
    decodeIntegerRow 32 3 1 323904209644492,
    decodeIntegerRow 32 3 1 1202704758544964,
    decodeIntegerRow 32 3 1 1060423291853868,
    decodeIntegerRow 32 3 1 1559806572719716,
    decodeIntegerRow 32 3 1 323706711286612,
    decodeIntegerRow 32 3 1 1202747633083236,
    decodeIntegerRow 32 3 1 1060340125584308,
    decodeIntegerRow 32 3 1 1559627670546244,
    decodeIntegerRow 32 3 1 1529115972989452,
    decodeIntegerRow 32 3 1 650315459722244,
    decodeIntegerRow 32 3 1 792596925004908,
    decodeIntegerRow 32 3 1 293213628966436,
    decodeIntegerRow 32 3 1 1067117890268804,
    decodeIntegerRow 32 3 1 278708605778572,
    decodeIntegerRow 32 3 1 339525010138276,
    decodeIntegerRow 32 3 1 653662773092588,
    decodeIntegerRow 32 3 1 785818071929244,
    decodeIntegerRow 32 3 1 1574495319154348,
    decodeIntegerRow 32 3 1 1513302163751356,
    decodeIntegerRow 32 3 1 1199316637569612]

def assocABC : Matrix (RightIndex 3 5 6) (LeftIndex 3 5 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 5 6 r) []).getD (leftPosition 3 5 6 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = assocABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = assocABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = assocABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = assocABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = assocABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = assocABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = assocABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = assocABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_0 : (associatorZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = assocABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_1 : (associatorZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = assocABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_2 : (associatorZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = assocABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_3 : (associatorZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = assocABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_0 : (associatorZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = assocABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_1 : (associatorZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = assocABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_2 : (associatorZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = assocABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_3 : (associatorZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = assocABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = assocABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = assocABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = assocABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = assocABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = assocABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = assocABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = assocABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = assocABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_0 : (associatorZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = assocABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_1 : (associatorZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = assocABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_2 : (associatorZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = assocABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_3 : (associatorZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = assocABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_0 : (associatorZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = assocABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_1 : (associatorZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = assocABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_2 : (associatorZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = assocABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_3 : (associatorZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = assocABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 5 6 = assocABC := by
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

def outerABC : Matrix (LeftIndex 5 6 3) (RightIndex 3 5 6) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 5 6 3 r) []).getD (rightPosition 3 5 6 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_0 : (outerRightZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_1 : (outerRightZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_2 : (outerRightZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_3 : (outerRightZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_0 : (outerRightZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_1 : (outerRightZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_2 : (outerRightZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_3 : (outerRightZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_0 : (outerRightZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_1 : (outerRightZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_2 : (outerRightZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_3 : (outerRightZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_0 : (outerRightZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_1 : (outerRightZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_2 : (outerRightZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_3 : (outerRightZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 5 6 = outerABC := by
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

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 785881637237444,
    decodeIntegerRow 32 3 1 1574304698824972,
    decodeIntegerRow 32 3 1 1513309226564836,
    decodeIntegerRow 32 3 1 1199295457537388,
    decodeIntegerRow 32 3 1 1559813629231684,
    decodeIntegerRow 32 3 1 792618074939532,
    decodeIntegerRow 32 3 1 1202768267165796,
    decodeIntegerRow 32 3 1 1529306580642028,
    decodeIntegerRow 32 3 1 1199295429530772,
    decodeIntegerRow 32 3 1 339710975122276,
    decodeIntegerRow 32 3 1 1574304705045748,
    decodeIntegerRow 32 3 1 1067138581038404,
    decodeIntegerRow 32 3 1 323713595535892,
    decodeIntegerRow 32 3 1 1202768294429156,
    decodeIntegerRow 32 3 1 1060402083815028,
    decodeIntegerRow 32 3 1 1559813622697924,
    decodeIntegerRow 32 3 1 1529122869912652,
    decodeIntegerRow 32 3 1 650336093804804,
    decodeIntegerRow 32 3 1 792658913332908,
    decodeIntegerRow 32 3 1 293399587651876,
    decodeIntegerRow 32 3 1 653641593051828,
    decodeIntegerRow 32 3 1 1513488115903996,
    decodeIntegerRow 32 3 1 278517985451092,
    decodeIntegerRow 32 3 1 785838733283804,
    decodeIntegerRow 32 3 1 1559620607735716,
    decodeIntegerRow 32 3 1 792658883226452,
    decodeIntegerRow 32 3 1 1202684067775364,
    decodeIntegerRow 32 3 1 1529122857234868,
    decodeIntegerRow 32 3 1 785838762698844,
    decodeIntegerRow 32 3 1 1574502197181868,
    decodeIntegerRow 32 3 1 1513488128735356,
    decodeIntegerRow 32 3 1 1199378623798092]

def assocBAC : Matrix (RightIndex 5 3 6) (LeftIndex 5 3 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 5 3 6 r) []).getD (leftPosition 5 3 6 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 5 3 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 5 3 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 5 3 6) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 5 3 6) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_0 : (associatorZ 5 3 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_1 : (associatorZ 5 3 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_2 : (associatorZ 5 3 6) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_3 : (associatorZ 5 3 6) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 5 3 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 5 3 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 5 3 6) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 5 3 6) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_0 : (associatorZ 5 3 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_1 : (associatorZ 5 3 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_2 : (associatorZ 5 3 6) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_3 : (associatorZ 5 3 6) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 5 3 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 5 3 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 5 3 6) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 5 3 6) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_0 : (associatorZ 5 3 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_1 : (associatorZ 5 3 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_2 : (associatorZ 5 3 6) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_3 : (associatorZ 5 3 6) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 5 3 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 5 3 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 5 3 6) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 5 3 6) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_0 : (associatorZ 5 3 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_1 : (associatorZ 5 3 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_2 : (associatorZ 5 3 6) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_3 : (associatorZ 5 3 6) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 5 3 6 = assocBAC := by
  funext r
  fin_cases r
  · exact assocBAC_row_0_0_0
  · exact assocBAC_row_0_0_1
  · exact assocBAC_row_0_0_2
  · exact assocBAC_row_0_0_3
  · exact assocBAC_row_0_1_0
  · exact assocBAC_row_0_1_1
  · exact assocBAC_row_0_1_2
  · exact assocBAC_row_0_1_3
  · exact assocBAC_row_1_0_0
  · exact assocBAC_row_1_0_1
  · exact assocBAC_row_1_0_2
  · exact assocBAC_row_1_0_3
  · exact assocBAC_row_1_1_0
  · exact assocBAC_row_1_1_1
  · exact assocBAC_row_1_1_2
  · exact assocBAC_row_1_1_3
  · exact assocBAC_row_2_0_0
  · exact assocBAC_row_2_0_1
  · exact assocBAC_row_2_0_2
  · exact assocBAC_row_2_0_3
  · exact assocBAC_row_2_1_0
  · exact assocBAC_row_2_1_1
  · exact assocBAC_row_2_1_2
  · exact assocBAC_row_2_1_3
  · exact assocBAC_row_3_0_0
  · exact assocBAC_row_3_0_1
  · exact assocBAC_row_3_0_2
  · exact assocBAC_row_3_0_3
  · exact assocBAC_row_3_1_0
  · exact assocBAC_row_3_1_1
  · exact assocBAC_row_3_1_2
  · exact assocBAC_row_3_1_3

def innerABC : Matrix (LeftIndex 5 3 6) (LeftIndex 3 5 6) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_0 : (innerLeftZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_1 : (innerLeftZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_2 : (innerLeftZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_3 : (innerLeftZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_0 : (innerLeftZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_1 : (innerLeftZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_2 : (innerLeftZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_3 : (innerLeftZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_0 : (innerLeftZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_1 : (innerLeftZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_2 : (innerLeftZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_3 : (innerLeftZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_0 : (innerLeftZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_1 : (innerLeftZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_2 : (innerLeftZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_3 : (innerLeftZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 5 6 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_4_0_0
  · exact innerABC_row_4_0_1
  · exact innerABC_row_4_0_2
  · exact innerABC_row_4_0_3
  · exact innerABC_row_5_0_0
  · exact innerABC_row_5_0_1
  · exact innerABC_row_5_0_2
  · exact innerABC_row_5_0_3
  · exact innerABC_row_6_0_0
  · exact innerABC_row_6_0_1
  · exact innerABC_row_6_0_2
  · exact innerABC_row_6_0_3
  · exact innerABC_row_7_0_0
  · exact innerABC_row_7_0_1
  · exact innerABC_row_7_0_2
  · exact innerABC_row_7_0_3

def innerRightABC : Matrix (RightIndex 3 6 5) (RightIndex 3 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 4) (Fin 2 × Fin 4 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 5 6) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 5 6) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_0 : (innerRightZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_1 : (innerRightZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_2 : (innerRightZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_3 : (innerRightZ 3 5 6) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_0 : (innerRightZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_1 : (innerRightZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_2 : (innerRightZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_3 : (innerRightZ 3 5 6) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerRightABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 5 6) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 5 6) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_0 : (innerRightZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_1 : (innerRightZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_2 : (innerRightZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_3 : (innerRightZ 3 5 6) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_0 : (innerRightZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_1 : (innerRightZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_2 : (innerRightZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_3 : (innerRightZ 3 5 6) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerRightABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 5 6 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926520683919368,
    decodeIntegerRow 32 3 1 926513624257288,
    decodeIntegerRow 32 3 1 926605399866952,
    decodeIntegerRow 32 3 1 926541862908232,
    decodeIntegerRow 32 3 1 926417113507840,
    decodeIntegerRow 32 3 1 926541088067200,
    decodeIntegerRow 32 3 1 926499763212800,
    decodeIntegerRow 32 3 1 926513538163840,
    decodeIntegerRow 32 3 1 1536557888500960,
    decodeIntegerRow 32 3 1 723160842331360,
    decodeIntegerRow 32 3 1 994293182656480,
    decodeIntegerRow 32 3 1 903915733082080,
    decodeIntegerRow 32 3 1 857032428989596,
    decodeIntegerRow 32 3 1 903350874048484,
    decodeIntegerRow 32 3 1 301211105499004,
    decodeIntegerRow 32 3 1 718077111028996,
    decodeIntegerRow 32 3 1 926506650688480,
    decodeIntegerRow 32 3 1 926499763212960,
    decodeIntegerRow 32 3 1 926479100788960,
    decodeIntegerRow 32 3 1 926417113509280,
    decodeIntegerRow 32 3 1 926478325948036,
    decodeIntegerRow 32 3 1 926605399865476,
    decodeIntegerRow 32 3 1 926506564595044,
    decodeIntegerRow 32 3 1 926520683919204,
    decodeIntegerRow 32 3 1 718077081976888,
    decodeIntegerRow 32 3 1 1551809093036872,
    decodeIntegerRow 32 3 1 903350870820472,
    decodeIntegerRow 32 3 1 995987760938248,
    decodeIntegerRow 32 3 1 903915729932800,
    decodeIntegerRow 32 3 1 858727005145600,
    decodeIntegerRow 32 3 1 723160813987840,
    decodeIntegerRow 32 3 1 316462290903040]

def inverseACB : Matrix (LeftIndex 3 6 5) (RightIndex 3 6 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 6 5 r) []).getD (rightPosition 3 6 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_2 : (associatorInverseZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_3 : (associatorInverseZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_2 : (associatorInverseZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_3 : (associatorInverseZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 6 5 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_0_1_0
  · exact inverseACB_row_0_1_1
  · exact inverseACB_row_0_1_2
  · exact inverseACB_row_0_1_3
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_1_2
  · exact inverseACB_row_1_1_3
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_2_1_0
  · exact inverseACB_row_2_1_1
  · exact inverseACB_row_2_1_2
  · exact inverseACB_row_2_1_3
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_3_1_0
  · exact inverseACB_row_3_1_1
  · exact inverseACB_row_3_1_2
  · exact inverseACB_row_3_1_3

def innerACB : Matrix (LeftIndex 6 3 5) (LeftIndex 3 6 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 3 6 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_0 : (innerLeftZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_1 : (innerLeftZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_2 : (innerLeftZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_3 : (innerLeftZ 3 6 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 3 6 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_0 : (innerLeftZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_1 : (innerLeftZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_2 : (innerLeftZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_3 : (innerLeftZ 3 6 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 3 6 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_0 : (innerLeftZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_1 : (innerLeftZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_2 : (innerLeftZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_3 : (innerLeftZ 3 6 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 3 6 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_0 : (innerLeftZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_1 : (innerLeftZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_2 : (innerLeftZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_3 : (innerLeftZ 3 6 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 6 5 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_0_1_0
  · exact innerACB_row_0_1_1
  · exact innerACB_row_0_1_2
  · exact innerACB_row_0_1_3
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_1_1_0
  · exact innerACB_row_1_1_1
  · exact innerACB_row_1_1_2
  · exact innerACB_row_1_1_3
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_0_2
  · exact innerACB_row_2_0_3
  · exact innerACB_row_2_1_0
  · exact innerACB_row_2_1_1
  · exact innerACB_row_2_1_2
  · exact innerACB_row_2_1_3
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_0_2
  · exact innerACB_row_3_0_3
  · exact innerACB_row_3_1_0
  · exact innerACB_row_3_1_1
  · exact innerACB_row_3_1_2
  · exact innerACB_row_3_1_3

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 926411259154012,
    decodeIntegerRow 32 3 1 926531273414948,
    decodeIntegerRow 32 3 1 926467736454588,
    decodeIntegerRow 32 3 1 926418318817732,
    decodeIntegerRow 32 3 1 293867935857760,
    decodeIntegerRow 32 3 1 1062076257240160,
    decodeIntegerRow 32 3 1 655377725757280,
    decodeIntegerRow 32 3 1 339056652246880,
    decodeIntegerRow 32 3 1 926599631606560,
    decodeIntegerRow 32 3 1 926468769571680,
    decodeIntegerRow 32 3 1 926489432002080,
    decodeIntegerRow 32 3 1 926413669771360,
    decodeIntegerRow 32 3 1 324370329104452,
    decodeIntegerRow 32 3 1 1204420744335172,
    decodeIntegerRow 32 3 1 1065465441438628,
    decodeIntegerRow 32 3 1 1574968313414308,
    decodeIntegerRow 32 3 1 339056664844000,
    decodeIntegerRow 32 3 1 1197642435800800,
    decodeIntegerRow 32 3 1 1062076286633440,
    decodeIntegerRow 32 3 1 1559152259292640,
    decodeIntegerRow 32 3 1 926418318815764,
    decodeIntegerRow 32 3 1 926552452401516,
    decodeIntegerRow 32 3 1 926531273410356,
    decodeIntegerRow 32 3 1 926608929696844,
    decodeIntegerRow 32 3 1 278051881893556,
    decodeIntegerRow 32 3 1 1065465411310516,
    decodeIntegerRow 32 3 1 648599416540564,
    decodeIntegerRow 32 3 1 324370316192404,
    decodeIntegerRow 32 3 1 926606519081440,
    decodeIntegerRow 32 3 1 926489431997600,
    decodeIntegerRow 32 3 1 926551419276000,
    decodeIntegerRow 32 3 1 926599631604640]

def assocBCA : Matrix (RightIndex 5 6 3) (LeftIndex 5 6 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 6 3 r) []).getD (leftPosition 5 6 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_0 : (associatorZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_1 : (associatorZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_2 : (associatorZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_3 : (associatorZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_0 : (associatorZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_1 : (associatorZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_2 : (associatorZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_3 : (associatorZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_0 : (associatorZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_1 : (associatorZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_2 : (associatorZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_3 : (associatorZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_0 : (associatorZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_1 : (associatorZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_2 : (associatorZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_3 : (associatorZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 5 6 3 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_0_1_0
  · exact assocBCA_row_0_1_1
  · exact assocBCA_row_0_1_2
  · exact assocBCA_row_0_1_3
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_1_0
  · exact assocBCA_row_1_1_1
  · exact assocBCA_row_1_1_2
  · exact assocBCA_row_1_1_3
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_0_2
  · exact assocBCA_row_2_0_3
  · exact assocBCA_row_2_1_0
  · exact assocBCA_row_2_1_1
  · exact assocBCA_row_2_1_2
  · exact assocBCA_row_2_1_3
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_0_2
  · exact assocBCA_row_3_0_3
  · exact assocBCA_row_3_1_0
  · exact assocBCA_row_3_1_1
  · exact assocBCA_row_3_1_2
  · exact assocBCA_row_3_1_3

def innerRightBAC : Matrix (RightIndex 5 6 3) (RightIndex 5 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 5 3 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 5 3 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 5 3 6) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 5 3 6) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_0 : (innerRightZ 5 3 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_1 : (innerRightZ 5 3 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_2 : (innerRightZ 5 3 6) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_3 : (innerRightZ 5 3 6) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 5 3 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 5 3 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 5 3 6) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 5 3 6) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_0 : (innerRightZ 5 3 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_1 : (innerRightZ 5 3 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_2 : (innerRightZ 5 3 6) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_3 : (innerRightZ 5 3 6) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 5 3 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 5 3 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 5 3 6) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 5 3 6) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_0 : (innerRightZ 5 3 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_1 : (innerRightZ 5 3 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_2 : (innerRightZ 5 3 6) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_3 : (innerRightZ 5 3 6) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 5 3 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 5 3 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 5 3 6) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 5 3 6) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_0 : (innerRightZ 5 3 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_1 : (innerRightZ 5 3 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_2 : (innerRightZ 5 3 6) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_3 : (innerRightZ 5 3 6) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 5 3 6 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_0_2
  · exact innerRightBAC_row_0_0_3
  · exact innerRightBAC_row_0_1_0
  · exact innerRightBAC_row_0_1_1
  · exact innerRightBAC_row_0_1_2
  · exact innerRightBAC_row_0_1_3
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_1_1_0
  · exact innerRightBAC_row_1_1_1
  · exact innerRightBAC_row_1_1_2
  · exact innerRightBAC_row_1_1_3
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_0_2
  · exact innerRightBAC_row_2_0_3
  · exact innerRightBAC_row_2_1_0
  · exact innerRightBAC_row_2_1_1
  · exact innerRightBAC_row_2_1_2
  · exact innerRightBAC_row_2_1_3
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_0_2
  · exact innerRightBAC_row_3_0_3
  · exact innerRightBAC_row_3_1_0
  · exact innerRightBAC_row_3_1_1
  · exact innerRightBAC_row_3_1_2
  · exact innerRightBAC_row_3_1_3

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1563580727593952,
    decodeIntegerRow 32 3 1 796633158553000,
    decodeIntegerRow 32 3 1 1193143392131488,
    decodeIntegerRow 32 3 1 1519709240631720,
    decodeIntegerRow 32 3 1 329920773414656,
    decodeIntegerRow 32 3 1 1208961656973520,
    decodeIntegerRow 32 3 1 1071070985344384,
    decodeIntegerRow 32 3 1 1570358526288080,
    decodeIntegerRow 32 3 1 282661669284224,
    decodeIntegerRow 32 3 1 1071070955422000,
    decodeIntegerRow 32 3 1 644058504169216,
    decodeIntegerRow 32 3 1 329920760293680,
    decodeIntegerRow 32 3 1 1519709228245472,
    decodeIntegerRow 32 3 1 659876824272040,
    decodeIntegerRow 32 3 1 796633128945568,
    decodeIntegerRow 32 3 1 289439455219880,
    decodeIntegerRow 32 3 1 1208917604844880,
    decodeIntegerRow 32 3 1 330117053340416,
    decodeIntegerRow 32 3 1 1570540348919120,
    decodeIntegerRow 32 3 1 1071157048868224,
    decodeIntegerRow 32 3 1 1056468332111320,
    decodeIntegerRow 32 3 1 289258658993568,
    decodeIntegerRow 32 3 1 333505187412440,
    decodeIntegerRow 32 3 1 659916427259872,
    decodeIntegerRow 32 3 1 1193103789152680,
    decodeIntegerRow 32 3 1 333505175024352,
    decodeIntegerRow 32 3 1 1563761523824040,
    decodeIntegerRow 32 3 1 1056468302512288,
    decodeIntegerRow 32 3 1 1071157078782160,
    decodeIntegerRow 32 3 1 282479833216256,
    decodeIntegerRow 32 3 1 330117066463440,
    decodeIntegerRow 32 3 1 644102611725184]

def assocCAB : Matrix (RightIndex 6 3 5) (LeftIndex 6 3 5) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 3 5 r) []).getD (leftPosition 6 3 5 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocCAB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocCAB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocCAB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocCAB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_0 : (associatorZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_1 : (associatorZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_2 : (associatorZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocCAB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_3 : (associatorZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocCAB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_0 : (associatorZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_1 : (associatorZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_2 : (associatorZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocCAB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_3 : (associatorZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocCAB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_4_0_0 : (associatorZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_4_0_1 : (associatorZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_4_0_2 : (associatorZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocCAB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_4_0_3 : (associatorZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocCAB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_5_0_0 : (associatorZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_5_0_1 : (associatorZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_5_0_2 : (associatorZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocCAB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_5_0_3 : (associatorZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocCAB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_6_0_0 : (associatorZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_6_0_1 : (associatorZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_6_0_2 : (associatorZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocCAB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_6_0_3 : (associatorZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocCAB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_7_0_0 : (associatorZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_7_0_1 : (associatorZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_7_0_2 : (associatorZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocCAB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_7_0_3 : (associatorZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocCAB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 6 3 5 = assocCAB := by
  funext r
  fin_cases r
  · exact assocCAB_row_0_0_0
  · exact assocCAB_row_0_0_1
  · exact assocCAB_row_0_0_2
  · exact assocCAB_row_0_0_3
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_2_0_0
  · exact assocCAB_row_2_0_1
  · exact assocCAB_row_2_0_2
  · exact assocCAB_row_2_0_3
  · exact assocCAB_row_3_0_0
  · exact assocCAB_row_3_0_1
  · exact assocCAB_row_3_0_2
  · exact assocCAB_row_3_0_3
  · exact assocCAB_row_4_0_0
  · exact assocCAB_row_4_0_1
  · exact assocCAB_row_4_0_2
  · exact assocCAB_row_4_0_3
  · exact assocCAB_row_5_0_0
  · exact assocCAB_row_5_0_1
  · exact assocCAB_row_5_0_2
  · exact assocCAB_row_5_0_3
  · exact assocCAB_row_6_0_0
  · exact assocCAB_row_6_0_1
  · exact assocCAB_row_6_0_2
  · exact assocCAB_row_6_0_3
  · exact assocCAB_row_7_0_0
  · exact assocCAB_row_7_0_1
  · exact assocCAB_row_7_0_2
  · exact assocCAB_row_7_0_3

def outerLeftABC : Matrix (RightIndex 6 3 5) (LeftIndex 3 5 6) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 5 6) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 5 6) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 5 6) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 5 6) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_0 : (outerLeftZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_1 : (outerLeftZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_2 : (outerLeftZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_3 : (outerLeftZ 3 5 6) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_0 : (outerLeftZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_1 : (outerLeftZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_2 : (outerLeftZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_3 : (outerLeftZ 3 5 6) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_0 : (outerLeftZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_1 : (outerLeftZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_2 : (outerLeftZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_3 : (outerLeftZ 3 5 6) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_0 : (outerLeftZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_1 : (outerLeftZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_2 : (outerLeftZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_3 : (outerLeftZ 3 5 6) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 5 6 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_4_0_0
  · exact outerLeftABC_row_4_0_1
  · exact outerLeftABC_row_4_0_2
  · exact outerLeftABC_row_4_0_3
  · exact outerLeftABC_row_5_0_0
  · exact outerLeftABC_row_5_0_1
  · exact outerLeftABC_row_5_0_2
  · exact outerLeftABC_row_5_0_3
  · exact outerLeftABC_row_6_0_0
  · exact outerLeftABC_row_6_0_1
  · exact outerLeftABC_row_6_0_2
  · exact outerLeftABC_row_6_0_3
  · exact outerLeftABC_row_7_0_0
  · exact outerLeftABC_row_7_0_1
  · exact outerLeftABC_row_7_0_2
  · exact outerLeftABC_row_7_0_3

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356
