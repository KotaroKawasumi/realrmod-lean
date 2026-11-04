import RMod.BrundanEllis.StackingReferenceHexagonAtoms526
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms562
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 929900454001288,
    decodeIntegerRow 32 3 1 919166668275848,
    decodeIntegerRow 32 3 1 934418638047432,
    decodeIntegerRow 32 3 1 928205791043272,
    decodeIntegerRow 32 3 1 1201129220030728,
    decodeIntegerRow 32 3 1 331692576270088,
    decodeIntegerRow 32 3 1 1567102127768392,
    decodeIntegerRow 32 3 1 1063861520431432,
    decodeIntegerRow 32 3 1 928203552246364,
    decodeIntegerRow 32 3 1 918602584004444,
    decodeIntegerRow 32 3 1 919167184679036,
    decodeIntegerRow 32 3 1 923122145125756,
    decodeIntegerRow 32 3 1 1063680177881884,
    decodeIntegerRow 32 3 1 286001750286364,
    decodeIntegerRow 32 3 1 331734404928316,
    decodeIntegerRow 32 3 1 652086201112636,
    decodeIntegerRow 32 3 1 1063861490668792,
    decodeIntegerRow 32 3 1 1567102121386888,
    decodeIntegerRow 32 3 1 1521327625340872,
    decodeIntegerRow 32 3 1 651890941185208,
    decodeIntegerRow 32 3 1 928205790675832,
    decodeIntegerRow 32 3 1 934418637968648,
    decodeIntegerRow 32 3 1 933853520733512,
    decodeIntegerRow 32 3 1 923119734509368,
    decodeIntegerRow 32 3 1 1200933960105244,
    decodeIntegerRow 32 3 1 1521285771173476,
    decodeIntegerRow 32 3 1 286001743913284,
    decodeIntegerRow 32 3 1 1063680207640636,
    decodeIntegerRow 32 3 1 929898043384924,
    decodeIntegerRow 32 3 1 933853004015396,
    decodeIntegerRow 32 3 1 918602583925764,
    decodeIntegerRow 32 3 1 928203552613756]

def assocABC : Matrix (RightIndex 5 6 2) (LeftIndex 5 6 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 6 2 r) []).getD (leftPosition 5 6 2 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_4 : (associatorZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_5 : (associatorZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_6 : (associatorZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_7 : (associatorZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_4 : (associatorZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_5 : (associatorZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_6 : (associatorZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_7 : (associatorZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 5 6 2 = assocABC := by
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

def outerABC : Matrix (LeftIndex 6 2 5) (RightIndex 5 6 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 6 2 = outerABC := by
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

def assocBAC : Matrix (RightIndex 6 5 2) (LeftIndex 6 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms526.assocCAB

theorem assocBAC_eq : associatorZ 6 5 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms526.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 5 2) (LeftIndex 5 6 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms526.innerACB

theorem innerABC_eq : innerLeftZ 5 6 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms526.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 2 6) (RightIndex 5 6 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 5 6 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 5 6 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_4 : (innerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_5 : (innerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_6 : (innerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_7 : (innerRightZ 5 6 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_4 : (innerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_5 : (innerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_6 : (innerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_7 : (innerRightZ 5 6 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 5 6 2 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 923971715387824,
    decodeIntegerRow 32 3 1 934125231575200,
    decodeIntegerRow 32 3 1 926196283888960,
    decodeIntegerRow 32 3 1 927451526391580,
    decodeIntegerRow 32 3 1 720619005909424,
    decodeIntegerRow 32 3 1 1544183363164000,
    decodeIntegerRow 32 3 1 903632919333440,
    decodeIntegerRow 32 3 1 995141648401180,
    decodeIntegerRow 32 3 1 903632909767500,
    decodeIntegerRow 32 3 1 995141619703360,
    decodeIntegerRow 32 3 1 1132401184005280,
    decodeIntegerRow 32 3 1 308836828876432,
    decodeIntegerRow 32 3 1 926196283770700,
    decodeIntegerRow 32 3 1 927451526036800,
    decodeIntegerRow 32 3 1 929048473475680,
    decodeIntegerRow 32 3 1 918894957311632,
    decodeIntegerRow 32 3 1 926761142961760,
    decodeIntegerRow 32 3 1 927263239679632,
    decodeIntegerRow 32 3 1 929055447045940,
    decodeIntegerRow 32 3 1 934146152242240,
    decodeIntegerRow 32 3 1 949386504243360,
    decodeIntegerRow 32 3 1 995139295180432,
    decodeIntegerRow 32 3 1 1132401270098740,
    decodeIntegerRow 32 3 1 1544183618255680,
    decodeIntegerRow 32 3 1 720618919816000,
    decodeIntegerRow 32 3 1 308836567407460,
    decodeIntegerRow 32 3 1 949386494677424,
    decodeIntegerRow 32 3 1 995139323878240,
    decodeIntegerRow 32 3 1 923964741820480,
    decodeIntegerRow 32 3 1 918874036565860,
    decodeIntegerRow 32 3 1 926761142843824,
    decodeIntegerRow 32 3 1 927263240033440]

def inverseACB : Matrix (LeftIndex 5 2 6) (RightIndex 5 2 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 2 6 r) []).getD (rightPosition 5 2 6 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 2 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 2 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 2 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 2 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 5 2 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 5 2 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 5 2 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 5 2 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 2 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 2 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 2 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 2 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 5 2 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 5 2 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 5 2 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 5 2 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 2 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 2 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 2 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 2 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 5 2 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 5 2 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 5 2 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 5 2 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 2 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 2 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 2 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 2 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 5 2 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 5 2 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 5 2 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 5 2 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 2 6 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 2 5 6) (LeftIndex 5 2 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms526.innerABC

theorem innerACB_eq : innerLeftZ 5 2 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms526.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 289439461599116,
    decodeIntegerRow 32 3 1 781949233272364,
    decodeIntegerRow 32 3 1 1208961684603916,
    decodeIntegerRow 32 3 1 333310947852756,
    decodeIntegerRow 32 3 1 1193103789231436,
    decodeIntegerRow 32 3 1 330117053707884,
    decodeIntegerRow 32 3 1 1570540349260236,
    decodeIntegerRow 32 3 1 1056468302354836,
    decodeIntegerRow 32 3 1 333310960973732,
    decodeIntegerRow 32 3 1 644058531799612,
    decodeIntegerRow 32 3 1 781949203664932,
    decodeIntegerRow 32 3 1 1563580733973188,
    decodeIntegerRow 32 3 1 1056468332268772,
    decodeIntegerRow 32 3 1 282479833557372,
    decodeIntegerRow 32 3 1 330117066095972,
    decodeIntegerRow 32 3 1 659916427338628,
    decodeIntegerRow 32 3 1 1071157078624708,
    decodeIntegerRow 32 3 1 1563761530199388,
    decodeIntegerRow 32 3 1 1519515001071932,
    decodeIntegerRow 32 3 1 644102611646428,
    decodeIntegerRow 32 3 1 1523099415804548,
    decodeIntegerRow 32 3 1 659876824350748,
    decodeIntegerRow 32 3 1 796633128788092,
    decodeIntegerRow 32 3 1 282661662904988,
    decodeIntegerRow 32 3 1 1208917604766124,
    decodeIntegerRow 32 3 1 1519515014194956,
    decodeIntegerRow 32 3 1 289258665368916,
    decodeIntegerRow 32 3 1 1071157049025676,
    decodeIntegerRow 32 3 1 1570358519908844,
    decodeIntegerRow 32 3 1 796633158710476,
    decodeIntegerRow 32 3 1 1193143392210196,
    decodeIntegerRow 32 3 1 1523099428190796]

def assocBCA : Matrix (RightIndex 6 2 5) (LeftIndex 6 2 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 2 5 r) []).getD (leftPosition 6 2 5 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 6 2 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 6 2 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 6 2 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 6 2 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_4 : (associatorZ 6 2 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_5 : (associatorZ 6 2 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_6 : (associatorZ 6 2 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_7 : (associatorZ 6 2 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 6 2 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 6 2 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 6 2 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 6 2 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_4 : (associatorZ 6 2 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_5 : (associatorZ 6 2 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_6 : (associatorZ 6 2 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_7 : (associatorZ 6 2 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 6 2 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 6 2 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 6 2 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 6 2 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_4 : (associatorZ 6 2 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_5 : (associatorZ 6 2 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_6 : (associatorZ 6 2 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_7 : (associatorZ 6 2 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 6 2 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 6 2 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 6 2 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 6 2 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_4 : (associatorZ 6 2 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_5 : (associatorZ 6 2 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_6 : (associatorZ 6 2 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_7 : (associatorZ 6 2 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 6 2 5 = assocBCA := by
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

def innerRightBAC : Matrix (RightIndex 6 2 5) (RightIndex 6 5 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 6 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 6 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 6 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 6 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 6 5 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 6 5 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 6 5 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 6 5 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 6 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 6 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 6 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 6 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 6 5 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 6 5 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 6 5 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 6 5 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 6 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 6 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 6 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 6 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_4 : (innerRightZ 6 5 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_5 : (innerRightZ 6 5 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_6 : (innerRightZ 6 5 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_7 : (innerRightZ 6 5 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 6 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 6 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 6 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 6 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_4 : (innerRightZ 6 5 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_5 : (innerRightZ 6 5 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_6 : (innerRightZ 6 5 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_7 : (innerRightZ 6 5 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 6 5 2 = innerRightBAC := by
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

def assocCAB : Matrix (RightIndex 2 5 6) (LeftIndex 2 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms526.assocBAC

theorem assocCAB_eq : associatorZ 2 5 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms526.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 2 5 6) (LeftIndex 5 6 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 6 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 6 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 6 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 6 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 5 6 2) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 5 6 2) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 5 6 2) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 5 6 2) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 5 6 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 5 6 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 5 6 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 5 6 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_4 : (outerLeftZ 5 6 2) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_5 : (outerLeftZ 5 6 2) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_6 : (outerLeftZ 5 6 2) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_7 : (outerLeftZ 5 6 2) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 6 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 6 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 6 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 6 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 5 6 2) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 5 6 2) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 5 6 2) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 5 6 2) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 5 6 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 5 6 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 5 6 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 5 6 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_4 : (outerLeftZ 5 6 2) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_5 : (outerLeftZ 5 6 2) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_6 : (outerLeftZ 5 6 2) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_7 : (outerLeftZ 5 6 2) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 6 2 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms562
