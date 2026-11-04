import RMod.BrundanEllis.StackingReferenceHexagonAtoms455
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn455
open Superfusion

theorem innerACB_alias : HexagonAtoms455.innerACB = HexagonAtoms455.innerABC :=
  HexagonAtoms455.innerACB_eq.symm.trans HexagonAtoms455.innerABC_eq

theorem assocCAB_alias : HexagonAtoms455.assocCAB = HexagonAtoms455.assocBAC :=
  HexagonAtoms455.assocCAB_eq.symm.trans HexagonAtoms455.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 919165707349492,
    decodeIntegerRow 32 3 1 929899513521796,
    decodeIntegerRow 32 3 1 928204158271828,
    decodeIntegerRow 32 3 1 934417017110884,
    decodeIntegerRow 32 3 1 1567150939375520,
    decodeIntegerRow 32 3 1 789207498322720,
    decodeIntegerRow 32 3 1 1201010683100320,
    decodeIntegerRow 32 3 1 1521209068121120,
    decodeIntegerRow 32 3 1 918603201497440,
    decodeIntegerRow 32 3 1 928204151896480,
    decodeIntegerRow 32 3 1 923120688085600,
    decodeIntegerRow 32 3 1 919165734988960,
    decodeIntegerRow 32 3 1 1521209068462236,
    decodeIntegerRow 32 3 1 652009505594068,
    decodeIntegerRow 32 3 1 789207498243964,
    decodeIntegerRow 32 3 1 285869249108852,
    decodeIntegerRow 32 3 1 286050562265120,
    decodeIntegerRow 32 3 1 1063729007703520,
    decodeIntegerRow 32 3 1 651967664338720,
    decodeIntegerRow 32 3 1 331615860804320,
    decodeIntegerRow 32 3 1 919168117970404,
    decodeIntegerRow 32 3 1 929898996960172,
    decodeIntegerRow 32 3 1 928205191395076,
    decodeIntegerRow 32 3 1 934419255544588,
    decodeIntegerRow 32 3 1 331615860463092,
    decodeIntegerRow 32 3 1 1201052524670596,
    decodeIntegerRow 32 3 1 1063729007782228,
    decodeIntegerRow 32 3 1 1566969626954084,
    decodeIntegerRow 32 3 1 918600963072160,
    decodeIntegerRow 32 3 1 928205185015840,
    decodeIntegerRow 32 3 1 923121204645280,
    decodeIntegerRow 32 3 1 919168145600800]

def rows_innerRightABC (r : RightIndex 4 5 5) : List ℤ := rows_innerRightABCData.getD (rightPosition 4 5 5 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 4 5 5) : (tripleIndices 4 2 4).map ((HexagonAtoms455.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_1_2
  · exact rows_innerRightABC_eq_0_1_3
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_0_2
  · exact rows_innerRightABC_eq_1_0_3
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_1_1
  · exact rows_innerRightABC_eq_1_1_2
  · exact rows_innerRightABC_eq_1_1_3
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_0_1
  · exact rows_innerRightABC_eq_2_0_2
  · exact rows_innerRightABC_eq_2_0_3
  · exact rows_innerRightABC_eq_2_1_0
  · exact rows_innerRightABC_eq_2_1_1
  · exact rows_innerRightABC_eq_2_1_2
  · exact rows_innerRightABC_eq_2_1_3
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_0_1
  · exact rows_innerRightABC_eq_3_0_2
  · exact rows_innerRightABC_eq_3_0_3
  · exact rows_innerRightABC_eq_3_1_0
  · exact rows_innerRightABC_eq_3_1_1
  · exact rows_innerRightABC_eq_3_1_2
  · exact rows_innerRightABC_eq_3_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 903632916144766,
    decodeIntegerRow 32 3 1 857880879853954,
    decodeIntegerRow 32 3 1 720618933633454,
    decodeIntegerRow 32 3 1 308836832065106,
    decodeIntegerRow 32 3 1 995141633520838,
    decodeIntegerRow 32 3 1 949386497866042,
    decodeIntegerRow 32 3 1 1544183615067062,
    decodeIntegerRow 32 3 1 1132401169124938,
    decodeIntegerRow 32 3 1 929048473647238,
    decodeIntegerRow 32 3 1 918874036528762,
    decodeIntegerRow 32 3 1 926761142924662,
    decodeIntegerRow 32 3 1 925568662631818,
    decodeIntegerRow 32 3 1 934125231616834,
    decodeIntegerRow 32 3 1 923964741636286,
    decodeIntegerRow 32 3 1 927263239863826,
    decodeIntegerRow 32 3 1 926196283812334,
    decodeIntegerRow 32 3 1 1132401283916194,
    decodeIntegerRow 32 3 1 308836822499166,
    decodeIntegerRow 32 3 1 949387275895666,
    decodeIntegerRow 32 3 1 857880878791054,
    decodeIntegerRow 32 3 1 308836564218842,
    decodeIntegerRow 32 3 1 1132401197822758,
    decodeIntegerRow 32 3 1 857878554268138,
    decodeIntegerRow 32 3 1 949386501054742,
    decodeIntegerRow 32 3 1 926761142880922,
    decodeIntegerRow 32 3 1 927451526208358,
    decodeIntegerRow 32 3 1 929048473292458,
    decodeIntegerRow 32 3 1 934146152205142,
    decodeIntegerRow 32 3 1 927263239849246,
    decodeIntegerRow 32 3 1 926823905004514,
    decodeIntegerRow 32 3 1 934125231498574,
    decodeIntegerRow 32 3 1 929055446861746]

def rows_inverseACB (r : LeftIndex 4 5 5) : List ℤ := rows_inverseACBData.getD (leftPosition 4 5 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 5 5) : (tripleIndices 4 2 4).map ((HexagonAtoms455.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_1_2
  · exact rows_inverseACB_eq_2_1_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_1_2
  · exact rows_inverseACB_eq_3_1_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 926488069463848,
    decodeIntegerRow 32 3 1 926608237590568,
    decodeIntegerRow 32 3 1 926601015661672,
    decodeIntegerRow 32 3 1 926553155003752,
    decodeIntegerRow 32 3 1 1519612121036964,
    decodeIntegerRow 32 3 1 659896611985756,
    decodeIntegerRow 32 3 1 796592507646916,
    decodeIntegerRow 32 3 1 289349060125244,
    decodeIntegerRow 32 3 1 926553127290088,
    decodeIntegerRow 32 3 1 926419186312168,
    decodeIntegerRow 32 3 1 926608244309032,
    decodeIntegerRow 32 3 1 926532149306152,
    decodeIntegerRow 32 3 1 289349060124324,
    decodeIntegerRow 32 3 1 1056427681209436,
    decodeIntegerRow 32 3 1 659896611989956,
    decodeIntegerRow 32 3 1 333408067816764,
    decodeIntegerRow 32 3 1 282570751248728,
    decodeIntegerRow 32 3 1 1071114017106472,
    decodeIntegerRow 32 3 1 644080557947032,
    decodeIntegerRow 32 3 1 330018913379048,
    decodeIntegerRow 32 3 1 926550716752444,
    decodeIntegerRow 32 3 1 926419702505404,
    decodeIntegerRow 32 3 1 926607210846556,
    decodeIntegerRow 32 3 1 926529910719196,
    decodeIntegerRow 32 3 1 330018913377048,
    decodeIntegerRow 32 3 1 1208939630909032,
    decodeIntegerRow 32 3 1 1071114017101912,
    decodeIntegerRow 32 3 1 1570449437602088,
    decodeIntegerRow 32 3 1 926529881115964,
    decodeIntegerRow 32 3 1 926412984041404,
    decodeIntegerRow 32 3 1 926419690118236,
    decodeIntegerRow 32 3 1 926469444543196]

def rows_assocBCA (r : RightIndex 5 5 4) : List ℤ := rows_assocBCAData.getD (rightPosition 5 5 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 5 4) : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_1_0
  · exact rows_assocBCA_eq_2_1_1
  · exact rows_assocBCA_eq_2_1_2
  · exact rows_assocBCA_eq_2_1_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_1_0
  · exact rows_assocBCA_eq_3_1_1
  · exact rows_assocBCA_eq_3_1_2
  · exact rows_assocBCA_eq_3_1_3

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 1201032723063100,
    decodeIntegerRow 32 3 1 331712974219504,
    decodeIntegerRow 32 3 1 1567060025056060,
    decodeIntegerRow 32 3 1 1063769643928336,
    decodeIntegerRow 32 3 1 928302295230768,
    decodeIntegerRow 32 3 1 918581160515500,
    decodeIntegerRow 32 3 1 919208753009872,
    decodeIntegerRow 32 3 1 923211593193900,
    decodeIntegerRow 32 3 1 919208782770580,
    decodeIntegerRow 32 3 1 929808589280592,
    decodeIntegerRow 32 3 1 928302307985300,
    decodeIntegerRow 32 3 1 934439055971248,
    decodeIntegerRow 32 3 1 285960164138896,
    decodeIntegerRow 32 3 1 1063769643766660,
    decodeIntegerRow 32 3 1 651987465714544,
    decodeIntegerRow 32 3 1 331712973853060,
    decodeIntegerRow 32 3 1 929989908446736,
    decodeIntegerRow 32 3 1 919125070184260,
    decodeIntegerRow 32 3 1 934397186923504,
    decodeIntegerRow 32 3 1 928107035304260,
    decodeIntegerRow 32 3 1 1063772054540500,
    decodeIntegerRow 32 3 1 285959647237072,
    decodeIntegerRow 32 3 1 331714007341780,
    decodeIntegerRow 32 3 1 651989704222768,
    decodeIntegerRow 32 3 1 1521306181878448,
    decodeIntegerRow 32 3 1 651989704139500,
    decodeIntegerRow 32 3 1 789248134464592,
    decodeIntegerRow 32 3 1 285959647576300,
    decodeIntegerRow 32 3 1 934397214558460,
    decodeIntegerRow 32 3 1 924913140792944,
    decodeIntegerRow 32 3 1 929989902069500,
    decodeIntegerRow 32 3 1 933895088906896]

def rows_assocBAC (r : RightIndex 5 4 5) : List ℤ := rows_assocBACData.getD (rightPosition 5 4 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 5 4 5) : (tripleIndices 4 2 4).map ((HexagonAtoms455.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_1_2
  · exact rows_assocBAC_eq_1_1_3
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_1_1
  · exact rows_assocBAC_eq_2_1_2
  · exact rows_assocBAC_eq_2_1_3
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_1_1
  · exact rows_assocBAC_eq_3_1_2
  · exact rows_assocBAC_eq_3_1_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 903632916144766,
    decodeIntegerRow 32 3 1 857880879853954,
    decodeIntegerRow 32 3 1 720618933633454,
    decodeIntegerRow 32 3 1 308836832065106,
    decodeIntegerRow 32 3 1 995141633520838,
    decodeIntegerRow 32 3 1 949386497866042,
    decodeIntegerRow 32 3 1 1544183615067062,
    decodeIntegerRow 32 3 1 1132401169124938,
    decodeIntegerRow 32 3 1 929048473647238,
    decodeIntegerRow 32 3 1 918874036528762,
    decodeIntegerRow 32 3 1 926761142924662,
    decodeIntegerRow 32 3 1 925568662631818,
    decodeIntegerRow 32 3 1 934125231616834,
    decodeIntegerRow 32 3 1 923964741636286,
    decodeIntegerRow 32 3 1 927263239863826,
    decodeIntegerRow 32 3 1 926196283812334,
    decodeIntegerRow 32 3 1 1132401283916194,
    decodeIntegerRow 32 3 1 308836822499166,
    decodeIntegerRow 32 3 1 949387275895666,
    decodeIntegerRow 32 3 1 857880878791054,
    decodeIntegerRow 32 3 1 308836564218842,
    decodeIntegerRow 32 3 1 1132401197822758,
    decodeIntegerRow 32 3 1 857878554268138,
    decodeIntegerRow 32 3 1 949386501054742,
    decodeIntegerRow 32 3 1 926761142880922,
    decodeIntegerRow 32 3 1 927451526208358,
    decodeIntegerRow 32 3 1 929048473292458,
    decodeIntegerRow 32 3 1 934146152205142,
    decodeIntegerRow 32 3 1 927263239849246,
    decodeIntegerRow 32 3 1 926823905004514,
    decodeIntegerRow 32 3 1 934125231498574,
    decodeIntegerRow 32 3 1 929055446861746]

def cols_assocABC (r : LeftIndex 4 5 5) : List ℤ := cols_assocABCData.getD (leftPosition 4 5 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 4 5 5) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms455.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_1_1
  · exact cols_assocABC_eq_2_1_2
  · exact cols_assocABC_eq_2_1_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_1_1
  · exact cols_assocABC_eq_3_1_2
  · exact cols_assocABC_eq_3_1_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 5 2 11641528330215965820312,
    decodeIntegerRow 32 5 2 11641556224431665820312,
    decodeIntegerRow 32 5 2 11641555839934790820312,
    decodeIntegerRow 32 5 2 11641537943252090820312,
    decodeIntegerRow 32 5 2 20877867937088012732560,
    decodeIntegerRow 32 5 2 9421378374099731290352,
    decodeIntegerRow 32 5 2 10166198015213012852752,
    decodeIntegerRow 32 5 2 2257376909255981470064,
    decodeIntegerRow 32 5 2 11641537943130965820312,
    decodeIntegerRow 32 5 2 11641508525481665820312,
    decodeIntegerRow 32 5 2 11641556224451390820312,
    decodeIntegerRow 32 5 2 11641536035294090820312,
    decodeIntegerRow 32 5 2 2257376909255981420560,
    decodeIntegerRow 32 5 2 13116866350173950352752,
    decodeIntegerRow 32 5 2 9421378374099731600272,
    decodeIntegerRow 32 5 2 2405196428298950232560,
    decodeIntegerRow 32 5 2 21032840013504028345560,
    decodeIntegerRow 32 5 2 10136634111404418787752,
    decodeIntegerRow 32 5 2 13891726732254028165272,
    decodeIntegerRow 32 5 2 20882636308670043907560,
    decodeIntegerRow 32 5 2 11641526499160262695312,
    decodeIntegerRow 32 5 2 11641555827698462695312,
    decodeIntegerRow 32 5 2 11641508159246312695312,
    decodeIntegerRow 32 5 2 11641528405776512695312,
    decodeIntegerRow 32 5 2 20882636308670043983064,
    decodeIntegerRow 32 5 2 9391337633132934415272,
    decodeIntegerRow 32 5 2 10136634111404419102872,
    decodeIntegerRow 32 5 2 2250224351882934595560,
    decodeIntegerRow 32 5 2 11641528405899512695312,
    decodeIntegerRow 32 5 2 11641556206121312695312,
    decodeIntegerRow 32 5 2 11641555827727562695312,
    decodeIntegerRow 32 5 2 11641537866347762695312]

def cols_right0 (r : LeftIndex 4 5 5) : List ℤ := cols_right0Data.getD (leftPosition 4 5 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 5 5) : (tripleIndices 4 2 4).map (fun j => (right0Middle4 5 5) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_1_2
  · exact cols_right0_eq_2_1_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_1_2
  · exact cols_right0_eq_3_1_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 903632916144766,
    decodeIntegerRow 32 3 1 857880879853954,
    decodeIntegerRow 32 3 1 720618933633454,
    decodeIntegerRow 32 3 1 308836832065106,
    decodeIntegerRow 32 3 1 995141633520838,
    decodeIntegerRow 32 3 1 949386497866042,
    decodeIntegerRow 32 3 1 1544183615067062,
    decodeIntegerRow 32 3 1 1132401169124938,
    decodeIntegerRow 32 3 1 929048473647238,
    decodeIntegerRow 32 3 1 918874036528762,
    decodeIntegerRow 32 3 1 926761142924662,
    decodeIntegerRow 32 3 1 925568662631818,
    decodeIntegerRow 32 3 1 934125231616834,
    decodeIntegerRow 32 3 1 923964741636286,
    decodeIntegerRow 32 3 1 927263239863826,
    decodeIntegerRow 32 3 1 926196283812334,
    decodeIntegerRow 32 3 1 1132401283916194,
    decodeIntegerRow 32 3 1 308836822499166,
    decodeIntegerRow 32 3 1 949387275895666,
    decodeIntegerRow 32 3 1 857880878791054,
    decodeIntegerRow 32 3 1 308836564218842,
    decodeIntegerRow 32 3 1 1132401197822758,
    decodeIntegerRow 32 3 1 857878554268138,
    decodeIntegerRow 32 3 1 949386501054742,
    decodeIntegerRow 32 3 1 926761142880922,
    decodeIntegerRow 32 3 1 927451526208358,
    decodeIntegerRow 32 3 1 929048473292458,
    decodeIntegerRow 32 3 1 934146152205142,
    decodeIntegerRow 32 3 1 927263239849246,
    decodeIntegerRow 32 3 1 926823905004514,
    decodeIntegerRow 32 3 1 934125231498574,
    decodeIntegerRow 32 3 1 929055446861746]

def cols_left0 (r : LeftIndex 4 5 5) : List ℤ := cols_left0Data.getD (leftPosition 4 5 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 5 5) : (tripleIndices 4 2 4).map (fun j => (left0Middle4 5 5) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_1_2
  · exact cols_left0_eq_2_1_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_1_2
  · exact cols_left0_eq_3_1_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1528436762251010454154502133616,
    decodeIntegerRow 32 9 4 3240830217522597213836962220800,
    decodeIntegerRow 32 9 4 188666821706897143354505820016,
    decodeIntegerRow 32 9 4 1566117791839787226547364677120,
    decodeIntegerRow 32 9 4 1716818901910267064274484928000,
    decodeIntegerRow 32 9 4 1717074831661447539831310821136,
    decodeIntegerRow 32 9 4 1717074185651737354511398808320,
    decodeIntegerRow 32 9 4 1716870590662642180998405195536,
    decodeIntegerRow 32 9 4 1717074185651735705122905758704,
    decodeIntegerRow 32 9 4 1716813229629870466338856912640,
    decodeIntegerRow 32 9 4 1716818901910266860925218667504,
    decodeIntegerRow 32 9 4 1716608988631063299956917803520,
    decodeIntegerRow 32 9 4 3245016998585615341052634442240,
    decodeIntegerRow 32 9 4 1566117791839787226578396527504,
    decodeIntegerRow 32 9 4 1905247058041502030528103550720,
    decodeIntegerRow 32 9 4 3240830217522597214088351292304,
    decodeIntegerRow 32 9 4 1716870661468885814545958526720,
    decodeIntegerRow 32 9 4 1716609625887255999625461544816,
    decodeIntegerRow 32 9 4 1717074824658632235414519831040,
    decodeIntegerRow 32 9 4 1716864847381479139490899957616,
    decodeIntegerRow 32 9 4 1867566028463546896013340952336,
    decodeIntegerRow 32 9 4 188666821705829803725731883520,
    decodeIntegerRow 32 9 4 192853602771249445356863973136,
    decodeIntegerRow 32 9 4 1528436762261802443734413571840,
    decodeIntegerRow 32 9 4 3240830217521263039552381745920,
    decodeIntegerRow 32 9 4 1528436762261802443709580344304,
    decodeIntegerRow 32 9 4 1566117791828965588675463564800,
    decodeIntegerRow 32 9 4 188666821705829803976431262704,
    decodeIntegerRow 32 9 4 1717074824658633880284140297104,
    decodeIntegerRow 32 9 4 1716818972911033141817682859520,
    decodeIntegerRow 32 9 4 1716870661468885651866545519504,
    decodeIntegerRow 32 9 4 1717074194405254835643894496000]

def cols_right2 (r : LeftIndex 4 5 5) : List ℤ := cols_right2Data.getD (leftPosition 4 5 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 5 5) : (tripleIndices 4 2 4).map (fun j => (right2Middle4 5 5) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_1_2
  · exact cols_right2_eq_2_1_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_1_2
  · exact cols_right2_eq_3_1_3

theorem product0_eq : HexagonAtoms455.outerABC * HexagonAtoms455.assocABC = HexagonAtoms455.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product1_eq : HexagonAtoms455.assocBAC * HexagonAtoms455.innerABC = HexagonAtoms455.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms455.innerRightABC * HexagonAtoms455.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms455.inverseACB * right0Middle4 5 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms455.innerABC * right1Middle4 5 5 = right1Middle4 5 5 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms455.assocBCA * left0Middle4 5 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms455.innerRightBAC * left1Middle4 5 5 = left1Middle4 5 5 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms455.assocBAC * right2Middle4 5 5 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn455
