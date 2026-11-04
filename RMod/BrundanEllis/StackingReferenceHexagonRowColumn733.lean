import RMod.BrundanEllis.StackingReferenceHexagonAtoms733
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn733
open Superfusion

theorem innerACB_alias : HexagonAtoms733.innerACB = HexagonAtoms733.innerABC :=
  HexagonAtoms733.innerACB_eq.symm.trans HexagonAtoms733.innerABC_eq

theorem assocCAB_alias : HexagonAtoms733.assocCAB = HexagonAtoms733.assocBAC :=
  HexagonAtoms733.assocCAB_eq.symm.trans HexagonAtoms733.assocBAC_eq

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425408,
    decodeIntegerRow 32 3 1 926510094423664,
    decodeIntegerRow 32 3 1 926510094423820,
    decodeIntegerRow 32 3 1 926510094426920,
    decodeIntegerRow 32 3 1 926510094423808,
    decodeIntegerRow 32 3 1 926510094426864,
    decodeIntegerRow 32 3 1 926510094426380,
    decodeIntegerRow 32 3 1 926510094428200,
    decodeIntegerRow 32 3 1 926510091066688,
    decodeIntegerRow 32 3 1 926510079624304,
    decodeIntegerRow 32 3 1 926510080647820,
    decodeIntegerRow 32 3 1 926510100986920,
    decodeIntegerRow 32 3 1 926510080569088,
    decodeIntegerRow 32 3 1 926510100619504,
    decodeIntegerRow 32 3 1 926510097443980,
    decodeIntegerRow 32 3 1 926510109385000,
    decodeIntegerRow 32 3 1 926488054504768,
    decodeIntegerRow 32 3 1 926412981023344,
    decodeIntegerRow 32 3 1 926419696311820,
    decodeIntegerRow 32 3 1 926553141146920,
    decodeIntegerRow 32 3 1 926419179751168,
    decodeIntegerRow 32 3 1 926550730530544,
    decodeIntegerRow 32 3 1 926529895917580,
    decodeIntegerRow 32 3 1 926608240949800,
    decodeIntegerRow 32 3 1 781906171747648,
    decodeIntegerRow 32 3 1 289349060124784,
    decodeIntegerRow 32 3 1 333408067815820,
    decodeIntegerRow 32 3 1 1208939630906920,
    decodeIntegerRow 32 3 1 330018913378048,
    decodeIntegerRow 32 3 1 1193123576863984,
    decodeIntegerRow 32 3 1 1056427681207180,
    decodeIntegerRow 32 3 1 1570449437602600]

def rows_outerABC (r : LeftIndex 3 3 7) : List ℤ := rows_outerABCData.getD (leftPosition 3 3 7 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 3 3 7) : (tripleIndices 4 1 8).map ((HexagonAtoms733.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_0_4
  · exact rows_outerABC_eq_0_0_5
  · exact rows_outerABC_eq_0_0_6
  · exact rows_outerABC_eq_0_0_7
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_0_4
  · exact rows_outerABC_eq_1_0_5
  · exact rows_outerABC_eq_1_0_6
  · exact rows_outerABC_eq_1_0_7
  · exact rows_outerABC_eq_2_0_0
  · exact rows_outerABC_eq_2_0_1
  · exact rows_outerABC_eq_2_0_2
  · exact rows_outerABC_eq_2_0_3
  · exact rows_outerABC_eq_2_0_4
  · exact rows_outerABC_eq_2_0_5
  · exact rows_outerABC_eq_2_0_6
  · exact rows_outerABC_eq_2_0_7
  · exact rows_outerABC_eq_3_0_0
  · exact rows_outerABC_eq_3_0_1
  · exact rows_outerABC_eq_3_0_2
  · exact rows_outerABC_eq_3_0_3
  · exact rows_outerABC_eq_3_0_4
  · exact rows_outerABC_eq_3_0_5
  · exact rows_outerABC_eq_3_0_6
  · exact rows_outerABC_eq_3_0_7

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 720932729408176,
    decodeIntegerRow 32 3 1 309778002207472,
    decodeIntegerRow 32 3 1 951924883294580,
    decodeIntegerRow 32 3 1 1002754432290340,
    decodeIntegerRow 32 3 1 946841926465776,
    decodeIntegerRow 32 3 1 987505561882672,
    decodeIntegerRow 32 3 1 1132652232541300,
    decodeIntegerRow 32 3 1 1544936505228580,
    decodeIntegerRow 32 3 1 1132087458498736,
    decodeIntegerRow 32 3 1 1543242189479152,
    decodeIntegerRow 32 3 1 901095315137780,
    decodeIntegerRow 32 3 1 850265727819940,
    decodeIntegerRow 32 3 1 906178271940336,
    decodeIntegerRow 32 3 1 865514598306352,
    decodeIntegerRow 32 3 1 720367957491700,
    decodeIntegerRow 32 3 1 308083680079780,
    decodeIntegerRow 32 3 1 951932631702900,
    decodeIntegerRow 32 3 1 850242511327780,
    decodeIntegerRow 32 3 1 720870053382544,
    decodeIntegerRow 32 3 1 1543430214722128,
    decodeIntegerRow 32 3 1 1132715080753780,
    decodeIntegerRow 32 3 1 307895138984740,
    decodeIntegerRow 32 3 1 946848125192144,
    decodeIntegerRow 32 3 1 865496030781328,
    decodeIntegerRow 32 3 1 951932622125300,
    decodeIntegerRow 32 3 1 850242482594980,
    decodeIntegerRow 32 3 1 720870054327184,
    decodeIntegerRow 32 3 1 1543430217556048,
    decodeIntegerRow 32 3 1 1132715079572980,
    decodeIntegerRow 32 3 1 307895135442340,
    decodeIntegerRow 32 3 1 946848115640784,
    decodeIntegerRow 32 3 1 865496002127248]

def rows_innerRightABC (r : RightIndex 7 3 3) : List ℤ := rows_innerRightABCData.getD (rightPosition 7 3 3 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 7 3 3) : (tripleIndices 4 1 8).map ((HexagonAtoms733.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_0_4
  · exact rows_innerRightABC_eq_0_0_5
  · exact rows_innerRightABC_eq_0_0_6
  · exact rows_innerRightABC_eq_0_0_7
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_0_2
  · exact rows_innerRightABC_eq_1_0_3
  · exact rows_innerRightABC_eq_1_0_4
  · exact rows_innerRightABC_eq_1_0_5
  · exact rows_innerRightABC_eq_1_0_6
  · exact rows_innerRightABC_eq_1_0_7
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_0_1
  · exact rows_innerRightABC_eq_2_0_2
  · exact rows_innerRightABC_eq_2_0_3
  · exact rows_innerRightABC_eq_2_0_4
  · exact rows_innerRightABC_eq_2_0_5
  · exact rows_innerRightABC_eq_2_0_6
  · exact rows_innerRightABC_eq_2_0_7
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_0_1
  · exact rows_innerRightABC_eq_3_0_2
  · exact rows_innerRightABC_eq_3_0_3
  · exact rows_innerRightABC_eq_3_0_4
  · exact rows_innerRightABC_eq_3_0_5
  · exact rows_innerRightABC_eq_3_0_6
  · exact rows_innerRightABC_eq_3_0_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 282668901131840,
    decodeIntegerRow 32 3 1 796612323935680,
    decodeIntegerRow 32 3 1 1193082954535360,
    decodeIntegerRow 32 3 1 330109821492800,
    decodeIntegerRow 32 3 1 644123618520640,
    decodeIntegerRow 32 3 1 1519521716729280,
    decodeIntegerRow 32 3 1 289446170509760,
    decodeIntegerRow 32 3 1 781928196712000,
    decodeIntegerRow 32 3 1 644037497364976,
    decodeIntegerRow 32 3 1 333317663507192,
    decodeIntegerRow 32 3 1 1563768239111112,
    decodeIntegerRow 32 3 1 781884146787856,
    decodeIntegerRow 32 3 1 282472601365616,
    decodeIntegerRow 32 3 1 1056447497502712,
    decodeIntegerRow 32 3 1 659855989663432,
    decodeIntegerRow 32 3 1 329928005265296,
    decodeIntegerRow 32 3 1 644123590811200,
    decodeIntegerRow 32 3 1 333498459737280,
    decodeIntegerRow 32 3 1 1563574012306880,
    decodeIntegerRow 32 3 1 781928226625600,
    decodeIntegerRow 32 3 1 282668894414400,
    decodeIntegerRow 32 3 1 1056407894514880,
    decodeIntegerRow 32 3 1 659937261868480,
    decodeIntegerRow 32 3 1 330109834612800,
    decodeIntegerRow 32 3 1 282472608085104,
    decodeIntegerRow 32 3 1 796572720956872,
    decodeIntegerRow 32 3 1 1193164226748808,
    decodeIntegerRow 32 3 1 329927992141296,
    decodeIntegerRow 32 3 1 644037525082864,
    decodeIntegerRow 32 3 1 1519702512955592,
    decodeIntegerRow 32 3 1 289251943703688,
    decodeIntegerRow 32 3 1 781884116865136]

def rows_inverseACB (r : LeftIndex 7 3 3) : List ℤ := rows_inverseACBData.getD (leftPosition 7 3 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 3 3) : (tripleIndices 4 1 8).map ((HexagonAtoms733.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_1_4
  · exact rows_inverseACB_eq_0_1_5
  · exact rows_inverseACB_eq_0_1_6
  · exact rows_inverseACB_eq_0_1_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_1_1_4
  · exact rows_inverseACB_eq_1_1_5
  · exact rows_inverseACB_eq_1_1_6
  · exact rows_inverseACB_eq_1_1_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 919168059507520,
    decodeIntegerRow 32 3 1 929898738679360,
    decodeIntegerRow 32 3 1 928204416552640,
    decodeIntegerRow 32 3 1 934416901261120,
    decodeIntegerRow 32 3 1 331804147161920,
    decodeIntegerRow 32 3 1 1200989762551360,
    decodeIntegerRow 32 3 1 1063749928488640,
    decodeIntegerRow 32 3 1 1566962653017920,
    decodeIntegerRow 32 3 1 924815255737576,
    decodeIntegerRow 32 3 1 934419311872960,
    decodeIntegerRow 32 3 1 933854367769600,
    decodeIntegerRow 32 3 1 929899771802608,
    decodeIntegerRow 32 3 1 789228418950376,
    decodeIntegerRow 32 3 1 1567157912944320,
    decodeIntegerRow 32 3 1 1521397354478720,
    decodeIntegerRow 32 3 1 1201073445377008,
    decodeIntegerRow 32 3 1 1521216042031040,
    decodeIntegerRow 32 3 1 1200989762393920,
    decodeIntegerRow 32 3 1 1063749928409920,
    decodeIntegerRow 32 3 1 286057535466560,
    decodeIntegerRow 32 3 1 933852156975040,
    decodeIntegerRow 32 3 1 929898725926720,
    decodeIntegerRow 32 3 1 928204410176320,
    decodeIntegerRow 32 3 1 918603257834560,
    decodeIntegerRow 32 3 1 789228419029120,
    decodeIntegerRow 32 3 1 285862275540048,
    decodeIntegerRow 32 3 1 331622834031896,
    decodeIntegerRow 32 3 1 1201073445219520,
    decodeIntegerRow 32 3 1 924815262115840,
    decodeIntegerRow 32 3 1 918600847213648,
    decodeIntegerRow 32 3 1 919165793443096,
    decodeIntegerRow 32 3 1 929899759046080]

def rows_assocBCA (r : RightIndex 3 3 7) : List ℤ := rows_assocBCAData.getD (rightPosition 3 3 7 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 3 7) : (tripleIndices 4 1 8).map ((HexagonAtoms733.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_0_1_4
  · exact rows_assocBCA_eq_0_1_5
  · exact rows_assocBCA_eq_0_1_6
  · exact rows_assocBCA_eq_0_1_7
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3
  · exact rows_assocBCA_eq_1_1_4
  · exact rows_assocBCA_eq_1_1_5
  · exact rows_assocBCA_eq_1_1_6
  · exact rows_assocBCA_eq_1_1_7

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 926511256687468,
    decodeIntegerRow 32 3 1 926509707005188,
    decodeIntegerRow 32 3 1 926510223565354,
    decodeIntegerRow 32 3 1 926510051381386,
    decodeIntegerRow 32 3 1 926604237604748,
    decodeIntegerRow 32 3 1 926478713366308,
    decodeIntegerRow 32 3 1 926520554779114,
    decodeIntegerRow 32 3 1 926506607641546,
    decodeIntegerRow 32 3 1 1132401226500886,
    decodeIntegerRow 32 3 1 1544183490703306,
    decodeIntegerRow 32 3 1 903633301793812,
    decodeIntegerRow 32 3 1 857879717001988,
    decodeIntegerRow 32 3 1 929051958659926,
    decodeIntegerRow 32 3 1 934135691379466,
    decodeIntegerRow 32 3 1 926227650540532,
    decodeIntegerRow 32 3 1 925662801033508,
    decodeIntegerRow 32 3 1 926506607641492,
    decodeIntegerRow 32 3 1 926520554779132,
    decodeIntegerRow 32 3 1 926541475485526,
    decodeIntegerRow 32 3 1 926415951247094,
    decodeIntegerRow 32 3 1 926510051377012,
    decodeIntegerRow 32 3 1 926510223566812,
    decodeIntegerRow 32 3 1 926510481846166,
    decodeIntegerRow 32 3 1 926508932164534,
    decodeIntegerRow 32 3 1 927357378252394,
    decodeIntegerRow 32 3 1 926792509613494,
    decodeIntegerRow 32 3 1 934135692442348,
    decodeIntegerRow 32 3 1 929051961848572,
    decodeIntegerRow 32 3 1 995140471731754,
    decodeIntegerRow 32 3 1 949386886703734,
    decodeIntegerRow 32 3 1 1544183490716428,
    decodeIntegerRow 32 3 1 1132401226540252]

def rows_assocBAC (r : RightIndex 3 7 3) : List ℤ := rows_assocBACData.getD (rightPosition 3 7 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_4 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_5 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_6 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_7 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_4 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_5 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_6 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_7 : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 3 7 3) : (tripleIndices 2 2 8).map ((HexagonAtoms733.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_0_4
  · exact rows_assocBAC_eq_0_0_5
  · exact rows_assocBAC_eq_0_0_6
  · exact rows_assocBAC_eq_0_0_7
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_0_1_4
  · exact rows_assocBAC_eq_0_1_5
  · exact rows_assocBAC_eq_0_1_6
  · exact rows_assocBAC_eq_0_1_7
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_0_4
  · exact rows_assocBAC_eq_1_0_5
  · exact rows_assocBAC_eq_1_0_6
  · exact rows_assocBAC_eq_1_0_7
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_1_2
  · exact rows_assocBAC_eq_1_1_3
  · exact rows_assocBAC_eq_1_1_4
  · exact rows_assocBAC_eq_1_1_5
  · exact rows_assocBAC_eq_1_1_6
  · exact rows_assocBAC_eq_1_1_7

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 282668901131840,
    decodeIntegerRow 32 3 1 796612323935680,
    decodeIntegerRow 32 3 1 1193082954535360,
    decodeIntegerRow 32 3 1 330109821492800,
    decodeIntegerRow 32 3 1 644123618520640,
    decodeIntegerRow 32 3 1 1519521716729280,
    decodeIntegerRow 32 3 1 289446170509760,
    decodeIntegerRow 32 3 1 781928196712000,
    decodeIntegerRow 32 3 1 644037497364976,
    decodeIntegerRow 32 3 1 333317663507192,
    decodeIntegerRow 32 3 1 1563768239111112,
    decodeIntegerRow 32 3 1 781884146787856,
    decodeIntegerRow 32 3 1 282472601365616,
    decodeIntegerRow 32 3 1 1056447497502712,
    decodeIntegerRow 32 3 1 659855989663432,
    decodeIntegerRow 32 3 1 329928005265296,
    decodeIntegerRow 32 3 1 644123590811200,
    decodeIntegerRow 32 3 1 333498459737280,
    decodeIntegerRow 32 3 1 1563574012306880,
    decodeIntegerRow 32 3 1 781928226625600,
    decodeIntegerRow 32 3 1 282668894414400,
    decodeIntegerRow 32 3 1 1056407894514880,
    decodeIntegerRow 32 3 1 659937261868480,
    decodeIntegerRow 32 3 1 330109834612800,
    decodeIntegerRow 32 3 1 282472608085104,
    decodeIntegerRow 32 3 1 796572720956872,
    decodeIntegerRow 32 3 1 1193164226748808,
    decodeIntegerRow 32 3 1 329927992141296,
    decodeIntegerRow 32 3 1 644037525082864,
    decodeIntegerRow 32 3 1 1519702512955592,
    decodeIntegerRow 32 3 1 289251943703688,
    decodeIntegerRow 32 3 1 781884116865136]

def cols_assocABC (r : LeftIndex 7 3 3) : List ℤ := cols_assocABCData.getD (leftPosition 7 3 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 7 3 3) : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms733.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_0_4
  · exact cols_assocABC_eq_0_0_5
  · exact cols_assocABC_eq_0_0_6
  · exact cols_assocABC_eq_0_0_7
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_0_1_4
  · exact cols_assocABC_eq_0_1_5
  · exact cols_assocABC_eq_0_1_6
  · exact cols_assocABC_eq_0_1_7
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_0_4
  · exact cols_assocABC_eq_1_0_5
  · exact cols_assocABC_eq_1_0_6
  · exact cols_assocABC_eq_1_0_7
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3
  · exact cols_assocABC_eq_1_1_4
  · exact cols_assocABC_eq_1_1_5
  · exact cols_assocABC_eq_1_1_6
  · exact cols_assocABC_eq_1_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1547044682041867107216578535040,
    decodeIntegerRow 32 9 4 190786092017182013957980524160,
    decodeIntegerRow 32 9 4 1718932429037850953790703570560,
    decodeIntegerRow 32 9 4 1735682743563330159420577767040,
    decodeIntegerRow 32 9 4 190734403363268957905013530240,
    decodeIntegerRow 32 9 4 1886173940365427870733025644160,
    decodeIntegerRow 32 9 4 1698001714860712116052740050560,
    decodeIntegerRow 32 9 4 1718938172221619071157472026240,
    decodeIntegerRow 32 9 4 1714751391157533624648287893248,
    decodeIntegerRow 32 9 4 1735682744438696896634187402880,
    decodeIntegerRow 32 9 4 1886639146139619408651506089600,
    decodeIntegerRow 32 9 4 190786021114877813820351995392,
    decodeIntegerRow 32 9 4 1735682106307137457495697045248,
    decodeIntegerRow 32 9 4 1718938172319013812283524316800,
    decodeIntegerRow 32 9 4 3242949487833949241055216062080,
    decodeIntegerRow 32 9 4 1886173948232788274460493307392,
    decodeIntegerRow 32 9 4 3242949416929243710018219418240,
    decodeIntegerRow 32 9 4 1886173940365429517834149863040,
    decodeIntegerRow 32 9 4 1698001714860712113796403175040,
    decodeIntegerRow 32 9 4 1714745648070893393165106535040,
    decodeIntegerRow 32 9 4 1886639138250647024598183322240,
    decodeIntegerRow 32 9 4 190786092017181831194693607040,
    decodeIntegerRow 32 9 4 1718932429037850974125285351040,
    decodeIntegerRow 32 9 4 1698001076729182322974735719040,
    decodeIntegerRow 32 9 4 1735682106307137459752034025600,
    decodeIntegerRow 32 9 4 1714745647973498652039053299680,
    decodeIntegerRow 32 9 4 190734332458563060337240653280,
    decodeIntegerRow 32 9 4 1886173948232789921561694052480,
    decodeIntegerRow 32 9 4 1714751391157533604313705168000,
    decodeIntegerRow 32 9 4 1698001075853815585761125978080,
    decodeIntegerRow 32 9 4 1547044674152891428849353702880,
    decodeIntegerRow 32 9 4 190786021114877631057056586880]

def cols_right0 (r : LeftIndex 7 3 3) : List ℤ := cols_right0Data.getD (leftPosition 7 3 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 3 3) : (tripleIndices 4 1 8).map (fun j => (right0Middle7 3 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_0_1_4
  · exact cols_right0_eq_0_1_5
  · exact cols_right0_eq_0_1_6
  · exact cols_right0_eq_0_1_7
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_1_1_4
  · exact cols_right0_eq_1_1_5
  · exact cols_right0_eq_1_1_6
  · exact cols_right0_eq_1_1_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 9 4 190760247690225394424157146240,
    decodeIntegerRow 32 9 4 1547277280984475037004642061440,
    decodeIntegerRow 32 9 4 1735682424497565265128614385280,
    decodeIntegerRow 32 9 4 1718935300629735022516026640000,
    decodeIntegerRow 32 9 4 1716609311203647487831136832640,
    decodeIntegerRow 32 9 4 1716816065819299704009453735040,
    decodeIntegerRow 32 9 4 1716844781738140209505313265280,
    decodeIntegerRow 32 9 4 1716842229212020314173699344000,
    decodeIntegerRow 32 9 4 1716609311192840676349189187776,
    decodeIntegerRow 32 9 4 1716867754474413517395844720576,
    decodeIntegerRow 32 9 4 1716839038554238674684598851760,
    decodeIntegerRow 32 9 4 1716842229212036785464266915920,
    decodeIntegerRow 32 9 4 190760176786720437204492752576,
    decodeIntegerRow 32 9 4 1886406547186204665118997526976,
    decodeIntegerRow 32 9 4 1698001394919595306449241555120,
    decodeIntegerRow 32 9 4 1718935300726996346439530547280,
    decodeIntegerRow 32 9 4 1716609311203647490090573072000,
    decodeIntegerRow 32 9 4 1716867754473212760313469200000,
    decodeIntegerRow 32 9 4 1716839038554372092138200435840,
    decodeIntegerRow 32 9 4 1716842229212021961302717837440,
    decodeIntegerRow 32 9 4 190760247690225394424501520000,
    decodeIntegerRow 32 9 4 1886406539308037447650107664000,
    decodeIntegerRow 32 9 4 1698001395794947219501340429440,
    decodeIntegerRow 32 9 4 1718935300629735022767075111040,
    decodeIntegerRow 32 9 4 190760176786720437204148378800,
    decodeIntegerRow 32 9 4 1547277273106307819535752198320,
    decodeIntegerRow 32 9 4 1735682425372917178180713258304,
    decodeIntegerRow 32 9 4 1718935300726996346188482064576,
    decodeIntegerRow 32 9 4 1716609311192840674089752843440,
    decodeIntegerRow 32 9 4 1716816065818098946927077269680,
    decodeIntegerRow 32 9 4 1716844781738273626958906346304,
    decodeIntegerRow 32 9 4 1716842229212035138335171894976]

def cols_left0 (r : LeftIndex 7 3 3) : List ℤ := cols_left0Data.getD (leftPosition 7 3 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 3 3) : (tripleIndices 4 1 8).map (fun j => (left0Middle7 3 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_0_1_4
  · exact cols_left0_eq_0_1_5
  · exact cols_left0_eq_0_1_6
  · exact cols_left0_eq_0_1_7
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_1_1_4
  · exact cols_left0_eq_1_1_5
  · exact cols_left0_eq_1_1_6
  · exact cols_left0_eq_1_1_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 65 32 5154629049087417059396275306065861568658699541092490165312,
    decodeIntegerRow 32 65 32 5154629049087417059395369293265711521301947343789164645312,
    decodeIntegerRow 32 65 32 5154629049087417059395383231924175368184358913678514445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383017483275924386168125697586445312,
    decodeIntegerRow 32 65 32 5154629049087432987246263991922400849366980791091918945344,
    decodeIntegerRow 32 65 32 5154629049087416814351523313483303224675666093826293943232,
    decodeIntegerRow 32 65 32 5154629049087417063165288554690058572747840166091918810112,
    decodeIntegerRow 32 65 32 5154629049087417059337384474056108490469806718826302733312,
    decodeIntegerRow 32 65 32 5232711003913830004200425509093770366627060197381106445312,
    decodeIntegerRow 32 65 32 10229956112804258471723144764222724300343533094457906445312,
    decodeIntegerRow 32 65 32 5154610568151363470532707271030993147392993603143481445312,
    decodeIntegerRow 32 65 32 5153427788243933783321459290142205232059343127623481445312,
    decodeIntegerRow 32 65 32 5154629053461603107582096080081410378830590468709106445312,
    decodeIntegerRow 32 65 32 5154629333409510191531731878420093930338972021709106445312,
    decodeIntegerRow 32 65 32 5154629049086381749088119893331069020784952463943481445312,
    decodeIntegerRow 32 65 32 5154629049020121889423279742895472338765373263943481445312,
    decodeIntegerRow 32 65 32 5154629049087417059337384474056108490469806718826285157312,
    decodeIntegerRow 32 65 32 5154629049087417063165288554690058572747840166091919080512,
    decodeIntegerRow 32 65 32 5154629049087417304439242727981457698151160478591918943232,
    decodeIntegerRow 32 65 32 5154629049087401131544502049542360073459845781326293945344,
    decodeIntegerRow 32 65 32 5154629049087417059395383017483275924386167811955001445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383231924175368184358918505323445312,
    decodeIntegerRow 32 65 32 5154629049087417059395396748199049401524879228554789645312,
    decodeIntegerRow 32 65 32 5154629049087417059394490735398899354168127031326865165312,
    decodeIntegerRow 32 65 32 5154629049154712229367486298567750546410789523709106445312,
    decodeIntegerRow 32 65 32 5154629049088452369702646148033719454748728098709106445312,
    decodeIntegerRow 32 65 32 5154629333409510191531731878420094294371552060474731445312,
    decodeIntegerRow 32 65 32 5154629053461603107582096080081434040948292988474731445312,
    decodeIntegerRow 32 65 32 5155830309930900335469306751322555690681321887389106445312,
    decodeIntegerRow 32 65 32 5154647530023470648258058770433767769833331737909106445312,
    decodeIntegerRow 32 65 32 10229956112804258471723144764222724300343553487725931445312,
    decodeIntegerRow 32 65 32 5232711003913830004200425509093770366628385759802731445312]

def cols_right2 (r : LeftIndex 7 3 3) : List ℤ := cols_right2Data.getD (leftPosition 7 3 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 3 3) : (tripleIndices 2 2 8).map (fun j => (right2Middle7 3 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_0_1_4
  · exact cols_right2_eq_0_1_5
  · exact cols_right2_eq_0_1_6
  · exact cols_right2_eq_0_1_7
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_1_1_4
  · exact cols_right2_eq_1_1_5
  · exact cols_right2_eq_1_1_6
  · exact cols_right2_eq_1_1_7

theorem product0_eq : HexagonAtoms733.outerABC * HexagonAtoms733.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms733.assocBAC * HexagonAtoms733.innerABC = HexagonAtoms733.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms733.innerRightABC * HexagonAtoms733.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms733.inverseACB * right0Middle7 3 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms733.innerABC * right1Middle7 3 3 = right1Middle7 3 3 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms733.assocBCA * left0Middle7 3 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms733.innerRightBAC * left1Middle7 3 3 = left1Middle7 3 3 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms733.assocBAC * right2Middle7 3 3 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn733
