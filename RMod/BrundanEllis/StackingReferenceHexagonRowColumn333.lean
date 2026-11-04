import RMod.BrundanEllis.StackingReferenceHexagonAtoms333
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn333
open Superfusion

theorem assocBAC_alias : HexagonAtoms333.assocBAC = HexagonAtoms333.assocABC :=
  HexagonAtoms333.assocBAC_eq.symm.trans HexagonAtoms333.assocABC_eq

theorem innerACB_alias : HexagonAtoms333.innerACB = HexagonAtoms333.innerABC :=
  HexagonAtoms333.innerACB_eq.symm.trans HexagonAtoms333.innerABC_eq

theorem assocBCA_alias : HexagonAtoms333.assocBCA = HexagonAtoms333.assocABC :=
  HexagonAtoms333.assocBCA_eq.symm.trans HexagonAtoms333.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms333.innerRightBAC = HexagonAtoms333.innerRightABC :=
  HexagonAtoms333.innerRightBAC_eq.symm.trans HexagonAtoms333.innerRightABC_eq

theorem assocCAB_alias : HexagonAtoms333.assocCAB = HexagonAtoms333.assocABC :=
  HexagonAtoms333.assocCAB_eq.symm.trans HexagonAtoms333.assocABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768960830324,
    decodeIntegerRow 32 3 1 1615533994468132,
    decodeIntegerRow 32 3 1 1116275897662428,
    decodeIntegerRow 32 3 1 1473209644343284,
    decodeIntegerRow 32 3 1 1477729206068236,
    decodeIntegerRow 32 3 1 750302975051868,
    decodeIntegerRow 32 3 1 243135645732772,
    decodeIntegerRow 32 3 1 1163717315927436,
    decodeIntegerRow 32 3 1 1102775068597836,
    decodeIntegerRow 32 3 1 1477895882970268,
    decodeIntegerRow 32 3 1 1163784468808292,
    decodeIntegerRow 32 3 1 1610094611118796,
    decodeIntegerRow 32 3 1 237277848252724,
    decodeIntegerRow 32 3 1 1146841279317732,
    decodeIntegerRow 32 3 1 1473377698740508,
    decodeIntegerRow 32 3 1 736690568876724,
    decodeIntegerRow 32 3 1 379642479087292,
    decodeIntegerRow 32 3 1 1116329588214996,
    decodeIntegerRow 32 3 1 237277856442196,
    decodeIntegerRow 32 3 1 1146841304935748,
    decodeIntegerRow 32 3 1 689235694635452,
    decodeIntegerRow 32 3 1 242925586552276,
    decodeIntegerRow 32 3 1 1102775036575316,
    decodeIntegerRow 32 3 1 1477895893207108,
    decodeIntegerRow 32 3 1 1609884534302332,
    decodeIntegerRow 32 3 1 689302847524116,
    decodeIntegerRow 32 3 1 1477729216301716,
    decodeIntegerRow 32 3 1 750303007064708,
    decodeIntegerRow 32 3 1 736744322939772,
    decodeIntegerRow 32 3 1 379810533487636,
    decodeIntegerRow 32 3 1 1146768986440596,
    decodeIntegerRow 32 3 1 1615533986281348]

def rows_assocABC (r : RightIndex 3 3 3) : List ℤ := rows_assocABCData.getD (rightPosition 3 3 3 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 3 3 3) : (tripleIndices 4 4 2).map ((HexagonAtoms333.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_1_1
  · exact rows_assocABC_eq_0_2_0
  · exact rows_assocABC_eq_0_2_1
  · exact rows_assocABC_eq_0_3_0
  · exact rows_assocABC_eq_0_3_1
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_1_0
  · exact rows_assocABC_eq_1_1_1
  · exact rows_assocABC_eq_1_2_0
  · exact rows_assocABC_eq_1_2_1
  · exact rows_assocABC_eq_1_3_0
  · exact rows_assocABC_eq_1_3_1
  · exact rows_assocABC_eq_2_0_0
  · exact rows_assocABC_eq_2_0_1
  · exact rows_assocABC_eq_2_1_0
  · exact rows_assocABC_eq_2_1_1
  · exact rows_assocABC_eq_2_2_0
  · exact rows_assocABC_eq_2_2_1
  · exact rows_assocABC_eq_2_3_0
  · exact rows_assocABC_eq_2_3_1
  · exact rows_assocABC_eq_3_0_0
  · exact rows_assocABC_eq_3_0_1
  · exact rows_assocABC_eq_3_1_0
  · exact rows_assocABC_eq_3_1_1
  · exact rows_assocABC_eq_3_2_0
  · exact rows_assocABC_eq_3_2_1
  · exact rows_assocABC_eq_3_3_0
  · exact rows_assocABC_eq_3_3_1

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 929333963575696,
    decodeIntegerRow 32 3 1 934981701875248,
    decodeIntegerRow 32 3 1 928769191659220,
    decodeIntegerRow 32 3 1 933287386125820,
    decodeIntegerRow 32 3 1 1155243151184016,
    decodeIntegerRow 32 3 1 1612709264700208,
    decodeIntegerRow 32 3 1 1109496539856020,
    decodeIntegerRow 32 3 1 1475469430716220,
    decodeIntegerRow 32 3 1 923686233780496,
    decodeIntegerRow 32 3 1 918038512489648,
    decodeIntegerRow 32 3 1 924251007823060,
    decodeIntegerRow 32 3 1 919732834617340,
    decodeIntegerRow 32 3 1 697777037772816,
    decodeIntegerRow 32 3 1 240310924466608,
    decodeIntegerRow 32 3 1 743523649127060,
    decodeIntegerRow 32 3 1 377550758529340,
    decodeIntegerRow 32 3 1 697707301979820,
    decodeIntegerRow 32 3 1 240101717087620,
    decodeIntegerRow 32 3 1 1109552328406416,
    decodeIntegerRow 32 3 1 1475636796367408,
    decodeIntegerRow 32 3 1 923685364343020,
    decodeIntegerRow 32 3 1 918035904177220,
    decodeIntegerRow 32 3 1 928769880405136,
    decodeIntegerRow 32 3 1 933289452363568,
    decodeIntegerRow 32 3 1 697707302084780,
    decodeIntegerRow 32 3 1 240101717402500,
    decodeIntegerRow 32 3 1 1109552328275216,
    decodeIntegerRow 32 3 1 1475636795973808,
    decodeIntegerRow 32 3 1 923685372844780,
    decodeIntegerRow 32 3 1 918035929682500,
    decodeIntegerRow 32 3 1 928769869777936,
    decodeIntegerRow 32 3 1 933289420481968]

def rows_innerRightABC (r : RightIndex 3 3 3) : List ℤ := rows_innerRightABCData.getD (rightPosition 3 3 3 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 3 3 3) : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_2_0
  · exact rows_innerRightABC_eq_0_2_1
  · exact rows_innerRightABC_eq_0_3_0
  · exact rows_innerRightABC_eq_0_3_1
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_1_1
  · exact rows_innerRightABC_eq_1_2_0
  · exact rows_innerRightABC_eq_1_2_1
  · exact rows_innerRightABC_eq_1_3_0
  · exact rows_innerRightABC_eq_1_3_1
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_0_1
  · exact rows_innerRightABC_eq_2_1_0
  · exact rows_innerRightABC_eq_2_1_1
  · exact rows_innerRightABC_eq_2_2_0
  · exact rows_innerRightABC_eq_2_2_1
  · exact rows_innerRightABC_eq_2_3_0
  · exact rows_innerRightABC_eq_2_3_1
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_0_1
  · exact rows_innerRightABC_eq_3_1_0
  · exact rows_innerRightABC_eq_3_1_1
  · exact rows_innerRightABC_eq_3_2_0
  · exact rows_innerRightABC_eq_3_2_1
  · exact rows_innerRightABC_eq_3_3_0
  · exact rows_innerRightABC_eq_3_3_1

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 704556363823988,
    decodeIntegerRow 32 3 1 238051149116164,
    decodeIntegerRow 32 3 1 1118023910215356,
    decodeIntegerRow 32 3 1 1472812935327028,
    decodeIntegerRow 32 3 1 374726028051484,
    decodeIntegerRow 32 3 1 1101022349603412,
    decodeIntegerRow 32 3 1 1610659374532588,
    decodeIntegerRow 32 3 1 690930010284764,
    decodeIntegerRow 32 3 1 704484593674844,
    decodeIntegerRow 32 3 1 237842619855892,
    decodeIntegerRow 32 3 1 1117970730108588,
    decodeIntegerRow 32 3 1 1472644700631964,
    decodeIntegerRow 32 3 1 1478460656620468,
    decodeIntegerRow 32 3 1 751939442516804,
    decodeIntegerRow 32 3 1 242570699816956,
    decodeIntegerRow 32 3 1 1162022477130228,
    decodeIntegerRow 32 3 1 1472812927218988,
    decodeIntegerRow 32 3 1 734996252999964,
    decodeIntegerRow 32 3 1 1614969050680996,
    decodeIntegerRow 32 3 1 704556395610348,
    decodeIntegerRow 32 3 1 690930042271356,
    decodeIntegerRow 32 3 1 242360804007028,
    decodeIntegerRow 32 3 1 751997813866572,
    decodeIntegerRow 32 3 1 374726036949436,
    decodeIntegerRow 32 3 1 1472644708742716,
    decodeIntegerRow 32 3 1 735049484387508,
    decodeIntegerRow 32 3 1 1615177558053772,
    decodeIntegerRow 32 3 1 704484561898236,
    decodeIntegerRow 32 3 1 1162022509126508,
    decodeIntegerRow 32 3 1 1610449478719324,
    decodeIntegerRow 32 3 1 1101080720960996,
    decodeIntegerRow 32 3 1 1478460665515948]

def rows_inverseACB (r : LeftIndex 3 3 3) : List ℤ := rows_inverseACBData.getD (leftPosition 3 3 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map ((HexagonAtoms333.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_2_1
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_3_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_2_1
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_1_3_1
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_2_0
  · exact rows_inverseACB_eq_2_2_1
  · exact rows_inverseACB_eq_2_3_0
  · exact rows_inverseACB_eq_2_3_1
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_2_0
  · exact rows_inverseACB_eq_3_2_1
  · exact rows_inverseACB_eq_3_3_0
  · exact rows_inverseACB_eq_3_3_1

private def rows_innerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 929333963575696,
    decodeIntegerRow 32 3 1 934981701875248,
    decodeIntegerRow 32 3 1 928769191659220,
    decodeIntegerRow 32 3 1 933287386125820,
    decodeIntegerRow 32 3 1 1155243151184016,
    decodeIntegerRow 32 3 1 1612709264700208,
    decodeIntegerRow 32 3 1 1109496539856020,
    decodeIntegerRow 32 3 1 1475469430716220,
    decodeIntegerRow 32 3 1 923686233780496,
    decodeIntegerRow 32 3 1 918038512489648,
    decodeIntegerRow 32 3 1 924251007823060,
    decodeIntegerRow 32 3 1 919732834617340,
    decodeIntegerRow 32 3 1 697777037772816,
    decodeIntegerRow 32 3 1 240310924466608,
    decodeIntegerRow 32 3 1 743523649127060,
    decodeIntegerRow 32 3 1 377550758529340,
    decodeIntegerRow 32 3 1 697707301979820,
    decodeIntegerRow 32 3 1 240101717087620,
    decodeIntegerRow 32 3 1 1109552328406416,
    decodeIntegerRow 32 3 1 1475636796367408,
    decodeIntegerRow 32 3 1 923685364343020,
    decodeIntegerRow 32 3 1 918035904177220,
    decodeIntegerRow 32 3 1 928769880405136,
    decodeIntegerRow 32 3 1 933289452363568,
    decodeIntegerRow 32 3 1 697707302084780,
    decodeIntegerRow 32 3 1 240101717402500,
    decodeIntegerRow 32 3 1 1109552328275216,
    decodeIntegerRow 32 3 1 1475636795973808,
    decodeIntegerRow 32 3 1 923685372844780,
    decodeIntegerRow 32 3 1 918035929682500,
    decodeIntegerRow 32 3 1 928769869777936,
    decodeIntegerRow 32 3 1 933289420481968]

def rows_innerABC (r : LeftIndex 3 3 3) : List ℤ := rows_innerABCData.getD (leftPosition 3 3 3 r) []

private theorem rows_innerABC_eq_0_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerABC_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map ((HexagonAtoms333.innerABC) r) = rows_innerABC r := by
  fin_cases r
  · exact rows_innerABC_eq_0_0_0
  · exact rows_innerABC_eq_0_0_1
  · exact rows_innerABC_eq_0_1_0
  · exact rows_innerABC_eq_0_1_1
  · exact rows_innerABC_eq_0_2_0
  · exact rows_innerABC_eq_0_2_1
  · exact rows_innerABC_eq_0_3_0
  · exact rows_innerABC_eq_0_3_1
  · exact rows_innerABC_eq_1_0_0
  · exact rows_innerABC_eq_1_0_1
  · exact rows_innerABC_eq_1_1_0
  · exact rows_innerABC_eq_1_1_1
  · exact rows_innerABC_eq_1_2_0
  · exact rows_innerABC_eq_1_2_1
  · exact rows_innerABC_eq_1_3_0
  · exact rows_innerABC_eq_1_3_1
  · exact rows_innerABC_eq_2_0_0
  · exact rows_innerABC_eq_2_0_1
  · exact rows_innerABC_eq_2_1_0
  · exact rows_innerABC_eq_2_1_1
  · exact rows_innerABC_eq_2_2_0
  · exact rows_innerABC_eq_2_2_1
  · exact rows_innerABC_eq_2_3_0
  · exact rows_innerABC_eq_2_3_1
  · exact rows_innerABC_eq_3_0_0
  · exact rows_innerABC_eq_3_0_1
  · exact rows_innerABC_eq_3_1_0
  · exact rows_innerABC_eq_3_1_1
  · exact rows_innerABC_eq_3_2_0
  · exact rows_innerABC_eq_3_2_1
  · exact rows_innerABC_eq_3_3_0
  · exact rows_innerABC_eq_3_3_1

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 929333963575696,
    decodeIntegerRow 32 3 1 934981701875248,
    decodeIntegerRow 32 3 1 928769191659220,
    decodeIntegerRow 32 3 1 933287386125820,
    decodeIntegerRow 32 3 1 1155243151184016,
    decodeIntegerRow 32 3 1 1612709264700208,
    decodeIntegerRow 32 3 1 1109496539856020,
    decodeIntegerRow 32 3 1 1475469430716220,
    decodeIntegerRow 32 3 1 923686233780496,
    decodeIntegerRow 32 3 1 918038512489648,
    decodeIntegerRow 32 3 1 924251007823060,
    decodeIntegerRow 32 3 1 919732834617340,
    decodeIntegerRow 32 3 1 697777037772816,
    decodeIntegerRow 32 3 1 240310924466608,
    decodeIntegerRow 32 3 1 743523649127060,
    decodeIntegerRow 32 3 1 377550758529340,
    decodeIntegerRow 32 3 1 697707301979820,
    decodeIntegerRow 32 3 1 240101717087620,
    decodeIntegerRow 32 3 1 1109552328406416,
    decodeIntegerRow 32 3 1 1475636796367408,
    decodeIntegerRow 32 3 1 923685364343020,
    decodeIntegerRow 32 3 1 918035904177220,
    decodeIntegerRow 32 3 1 928769880405136,
    decodeIntegerRow 32 3 1 933289452363568,
    decodeIntegerRow 32 3 1 697707302084780,
    decodeIntegerRow 32 3 1 240101717402500,
    decodeIntegerRow 32 3 1 1109552328275216,
    decodeIntegerRow 32 3 1 1475636795973808,
    decodeIntegerRow 32 3 1 923685372844780,
    decodeIntegerRow 32 3 1 918035929682500,
    decodeIntegerRow 32 3 1 928769869777936,
    decodeIntegerRow 32 3 1 933289420481968]

def cols_innerABC (r : LeftIndex 3 3 3) : List ℤ := cols_innerABCData.getD (leftPosition 3 3 3 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_2_0
  · exact cols_innerABC_eq_0_2_1
  · exact cols_innerABC_eq_0_3_0
  · exact cols_innerABC_eq_0_3_1
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_1_1
  · exact cols_innerABC_eq_1_2_0
  · exact cols_innerABC_eq_1_2_1
  · exact cols_innerABC_eq_1_3_0
  · exact cols_innerABC_eq_1_3_1
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_0_1
  · exact cols_innerABC_eq_2_1_0
  · exact cols_innerABC_eq_2_1_1
  · exact cols_innerABC_eq_2_2_0
  · exact cols_innerABC_eq_2_2_1
  · exact cols_innerABC_eq_2_3_0
  · exact cols_innerABC_eq_2_3_1
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_0_1
  · exact cols_innerABC_eq_3_1_0
  · exact cols_innerABC_eq_3_1_1
  · exact cols_innerABC_eq_3_2_0
  · exact cols_innerABC_eq_3_2_1
  · exact cols_innerABC_eq_3_3_0
  · exact cols_innerABC_eq_3_3_1

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 704556363823988,
    decodeIntegerRow 32 3 1 238051149116164,
    decodeIntegerRow 32 3 1 1118023910215356,
    decodeIntegerRow 32 3 1 1472812935327028,
    decodeIntegerRow 32 3 1 374726028051484,
    decodeIntegerRow 32 3 1 1101022349603412,
    decodeIntegerRow 32 3 1 1610659374532588,
    decodeIntegerRow 32 3 1 690930010284764,
    decodeIntegerRow 32 3 1 704484593674844,
    decodeIntegerRow 32 3 1 237842619855892,
    decodeIntegerRow 32 3 1 1117970730108588,
    decodeIntegerRow 32 3 1 1472644700631964,
    decodeIntegerRow 32 3 1 1478460656620468,
    decodeIntegerRow 32 3 1 751939442516804,
    decodeIntegerRow 32 3 1 242570699816956,
    decodeIntegerRow 32 3 1 1162022477130228,
    decodeIntegerRow 32 3 1 1472812927218988,
    decodeIntegerRow 32 3 1 734996252999964,
    decodeIntegerRow 32 3 1 1614969050680996,
    decodeIntegerRow 32 3 1 704556395610348,
    decodeIntegerRow 32 3 1 690930042271356,
    decodeIntegerRow 32 3 1 242360804007028,
    decodeIntegerRow 32 3 1 751997813866572,
    decodeIntegerRow 32 3 1 374726036949436,
    decodeIntegerRow 32 3 1 1472644708742716,
    decodeIntegerRow 32 3 1 735049484387508,
    decodeIntegerRow 32 3 1 1615177558053772,
    decodeIntegerRow 32 3 1 704484561898236,
    decodeIntegerRow 32 3 1 1162022509126508,
    decodeIntegerRow 32 3 1 1610449478719324,
    decodeIntegerRow 32 3 1 1101080720960996,
    decodeIntegerRow 32 3 1 1478460665515948]

def cols_assocABC (r : LeftIndex 3 3 3) : List ℤ := cols_assocABCData.getD (leftPosition 3 3 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms333.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_2_0
  · exact cols_assocABC_eq_0_2_1
  · exact cols_assocABC_eq_0_3_0
  · exact cols_assocABC_eq_0_3_1
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_2_0
  · exact cols_assocABC_eq_1_2_1
  · exact cols_assocABC_eq_1_3_0
  · exact cols_assocABC_eq_1_3_1
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_1_1
  · exact cols_assocABC_eq_2_2_0
  · exact cols_assocABC_eq_2_2_1
  · exact cols_assocABC_eq_2_3_0
  · exact cols_assocABC_eq_2_3_1
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_1_1
  · exact cols_assocABC_eq_3_2_0
  · exact cols_assocABC_eq_3_2_1
  · exact cols_assocABC_eq_3_3_0
  · exact cols_assocABC_eq_3_3_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 9 4 3242923962571556943867006448000,
    decodeIntegerRow 32 9 4 1547280144698191888402268510080,
    decodeIntegerRow 32 9 4 1698027240123104413240949664640,
    decodeIntegerRow 32 9 4 1719167899583149766186629080960,
    decodeIntegerRow 32 9 4 1719167899669605923246412958080,
    decodeIntegerRow 32 9 4 1735656581045960558533935287680,
    decodeIntegerRow 32 9 4 1886403667716019981695914285440,
    decodeIntegerRow 32 9 4 3242923891668066808800120680320,
    decodeIntegerRow 32 9 4 190760566756005112739881786240,
    decodeIntegerRow 32 9 4 1886409410900054913635294680960,
    decodeIntegerRow 32 9 4 1697975550592638686805562948480,
    decodeIntegerRow 32 9 4 1718702701784386769381255280000,
    decodeIntegerRow 32 9 4 1714981118616192205561032045440,
    decodeIntegerRow 32 9 4 1697975551466790025786526104960,
    decodeIntegerRow 32 9 4 1886409418778088733957619562880,
    decodeIntegerRow 32 9 4 3242923324440027150789002116480,
    decodeIntegerRow 32 9 4 1714981118616193852690471440144,
    decodeIntegerRow 32 9 4 1697975551466789842775281577584,
    decodeIntegerRow 32 9 4 1886409418778088713650587684496,
    decodeIntegerRow 32 9 4 3242923324440027153299486838544,
    decodeIntegerRow 32 9 4 190760566756005115250366601616,
    decodeIntegerRow 32 9 4 1886409410900054933942327505424,
    decodeIntegerRow 32 9 4 1697975550592638869816798972656,
    decodeIntegerRow 32 9 4 1718702701784388416510618147216,
    decodeIntegerRow 32 9 4 1719167899669604276117738838416,
    decodeIntegerRow 32 9 4 1735656581045960741551370039824,
    decodeIntegerRow 32 9 4 1886403667716019961333092911856,
    decodeIntegerRow 32 9 4 3242923891668066810808508553616,
    decodeIntegerRow 32 9 4 3242923962571556941858618691344,
    decodeIntegerRow 32 9 4 1547280144698191868039448079984,
    decodeIntegerRow 32 9 4 1698027240123104596258392919696,
    decodeIntegerRow 32 9 4 1719167899583151413315379728144]

def cols_right0 (r : LeftIndex 3 3 3) : List ℤ := cols_right0Data.getD (leftPosition 3 3 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map (fun j => (right0Middle3 3 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_2_0
  · exact cols_right0_eq_0_2_1
  · exact cols_right0_eq_0_3_0
  · exact cols_right0_eq_0_3_1
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_2_0
  · exact cols_right0_eq_1_2_1
  · exact cols_right0_eq_1_3_0
  · exact cols_right0_eq_1_3_1
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_2_0
  · exact cols_right0_eq_2_2_1
  · exact cols_right0_eq_2_3_0
  · exact cols_right0_eq_2_3_1
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_2_0
  · exact cols_right0_eq_3_2_1
  · exact cols_right0_eq_3_3_0
  · exact cols_right0_eq_3_3_1

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 32 65 32 5154629049087417055625477486774702532095276425709106445312,
    decodeIntegerRow 32 65 32 5154629049087417059453381567408664263415871113474731445312,
    decodeIntegerRow 32 65 32 5154629049087401131544502049543129092285177673709106445312,
    decodeIntegerRow 32 65 32 5154629049087417304439242728031443921797733483474731445312,
    decodeIntegerRow 32 65 32 5076547094261004114590340532370990556199103436955001445312,
    decodeIntegerRow 32 65 32 79301985370575647067621277242036622483283283739698445312,
    decodeIntegerRow 32 65 32 5154647530023470648258058770433767772633582353629048245312,
    decodeIntegerRow 32 65 32 5155830309930900335469306751322555690724402666091347725312,
    decodeIntegerRow 32 65 32 5154629049087417059395369293265711518501696728143481445312,
    decodeIntegerRow 32 65 32 5154629049087417059394490735398899354211207810029106445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383023981484998441321384802731445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383231924175368184348719457906445312,
    decodeIntegerRow 32 65 32 5154629049020121889423279742896241357590705156326293945344,
    decodeIntegerRow 32 65 32 5154629049088452369702646148083705678395301103591918947392,
    decodeIntegerRow 32 65 32 5154628764765323927259034163044666810471564531326294080512,
    decodeIntegerRow 32 65 32 5154629053461603107582096080081422209889441728591927733312,
    decodeIntegerRow 32 65 32 5154629049087417059396275306065861568701780319794731445312,
    decodeIntegerRow 32 65 32 5154629049087417059395369293265711524102197959509106445312,
    decodeIntegerRow 32 65 32 5154629049087417059395382809540585554642457459692281445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383023981484998439995822381106445312,
    decodeIntegerRow 32 65 32 5154629049086381749088119893381055244431525468826293947392,
    decodeIntegerRow 32 65 32 5154629049020121889423279742896241357590705156326293945280,
    decodeIntegerRow 32 65 32 5154629044713231011208669961383338712937384843826302733312,
    decodeIntegerRow 32 65 32 5154628764765323927259034163044666810471564531326293810112,
    decodeIntegerRow 32 65 32 5154629049087417059337384474056120321528657978709106445312,
    decodeIntegerRow 32 65 32 5154629049087417055625477486774702168062696386943481445312,
    decodeIntegerRow 32 65 32 5154629049087416814351523313533289448322239098709106445312,
    decodeIntegerRow 32 65 32 5154629049087401131544502049541591054634513888943481445312,
    decodeIntegerRow 32 65 32 10229956112804258471723144764222724300343543293505323445312,
    decodeIntegerRow 32 65 32 5076547094261004114590340532370990556199103750697586445312,
    decodeIntegerRow 32 65 32 5153427788243933783321459290142205232102423906325722725312,
    decodeIntegerRow 32 65 32 5154647530023470648258058770433767772633582353554789645312]

def cols_right1 (r : LeftIndex 3 3 3) : List ℤ := cols_right1Data.getD (leftPosition 3 3 3 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map (fun j => (right1Middle3 3 3) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_2_0
  · exact cols_right1_eq_0_2_1
  · exact cols_right1_eq_0_3_0
  · exact cols_right1_eq_0_3_1
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_1_1
  · exact cols_right1_eq_1_2_0
  · exact cols_right1_eq_1_2_1
  · exact cols_right1_eq_1_3_0
  · exact cols_right1_eq_1_3_1
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_1_0
  · exact cols_right1_eq_2_1_1
  · exact cols_right1_eq_2_2_0
  · exact cols_right1_eq_2_2_1
  · exact cols_right1_eq_2_3_0
  · exact cols_right1_eq_2_3_1
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_1_0
  · exact cols_right1_eq_3_1_1
  · exact cols_right1_eq_3_2_0
  · exact cols_right1_eq_3_2_1
  · exact cols_right1_eq_3_3_0
  · exact cols_right1_eq_3_3_1

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 704556363823988,
    decodeIntegerRow 32 3 1 238051149116164,
    decodeIntegerRow 32 3 1 1118023910215356,
    decodeIntegerRow 32 3 1 1472812935327028,
    decodeIntegerRow 32 3 1 374726028051484,
    decodeIntegerRow 32 3 1 1101022349603412,
    decodeIntegerRow 32 3 1 1610659374532588,
    decodeIntegerRow 32 3 1 690930010284764,
    decodeIntegerRow 32 3 1 704484593674844,
    decodeIntegerRow 32 3 1 237842619855892,
    decodeIntegerRow 32 3 1 1117970730108588,
    decodeIntegerRow 32 3 1 1472644700631964,
    decodeIntegerRow 32 3 1 1478460656620468,
    decodeIntegerRow 32 3 1 751939442516804,
    decodeIntegerRow 32 3 1 242570699816956,
    decodeIntegerRow 32 3 1 1162022477130228,
    decodeIntegerRow 32 3 1 1472812927218988,
    decodeIntegerRow 32 3 1 734996252999964,
    decodeIntegerRow 32 3 1 1614969050680996,
    decodeIntegerRow 32 3 1 704556395610348,
    decodeIntegerRow 32 3 1 690930042271356,
    decodeIntegerRow 32 3 1 242360804007028,
    decodeIntegerRow 32 3 1 751997813866572,
    decodeIntegerRow 32 3 1 374726036949436,
    decodeIntegerRow 32 3 1 1472644708742716,
    decodeIntegerRow 32 3 1 735049484387508,
    decodeIntegerRow 32 3 1 1615177558053772,
    decodeIntegerRow 32 3 1 704484561898236,
    decodeIntegerRow 32 3 1 1162022509126508,
    decodeIntegerRow 32 3 1 1610449478719324,
    decodeIntegerRow 32 3 1 1101080720960996,
    decodeIntegerRow 32 3 1 1478460665515948]

def cols_left0 (r : LeftIndex 3 3 3) : List ℤ := cols_left0Data.getD (leftPosition 3 3 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map (fun j => (left0Middle3 3 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_2_0
  · exact cols_left0_eq_0_2_1
  · exact cols_left0_eq_0_3_0
  · exact cols_left0_eq_0_3_1
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_2_0
  · exact cols_left0_eq_1_2_1
  · exact cols_left0_eq_1_3_0
  · exact cols_left0_eq_1_3_1
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_2_0
  · exact cols_left0_eq_2_2_1
  · exact cols_left0_eq_2_3_0
  · exact cols_left0_eq_2_3_1
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_2_0
  · exact cols_left0_eq_3_2_1
  · exact cols_left0_eq_3_3_0
  · exact cols_left0_eq_3_3_1

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 32 17 8 1183955797380786358393352557545624403328,
    decodeIntegerRow 32 17 8 1183955797380201109070720731456033163376,
    decodeIntegerRow 32 17 8 1183955797539974174127582316468472941952,
    decodeIntegerRow 32 17 8 1183955797370837119886984576576604595824,
    decodeIntegerRow 32 17 8 1249503523186751747374485156894096083856,
    decodeIntegerRow 32 17 8 2298267136091041738613397288576024286592,
    decodeIntegerRow 32 17 8 1183728988640418681314951307801535760496,
    decodeIntegerRow 32 17 8 1180100048803379615601321854058691718272,
    decodeIntegerRow 32 17 8 1183955797380233735426729039377446012816,
    decodeIntegerRow 32 17 8 1183955797380235535501538613743123197312,
    decodeIntegerRow 32 17 8 1183955797380233622532763612706437663856,
    decodeIntegerRow 32 17 8 1183955797380233616304131053625587569792,
    decodeIntegerRow 32 17 8 1183955843545252921709272180177035552128,
    decodeIntegerRow 32 17 8 1183955794664644252405157911512442686576,
    decodeIntegerRow 32 17 8 1183969139070810972428353256946294945152,
    decodeIntegerRow 32 17 8 1183955012574905543539329612878956800624,
    decodeIntegerRow 32 17 8 1183955797380231710342567651321925642864,
    decodeIntegerRow 32 17 8 1183955797380233735426728491027105090688,
    decodeIntegerRow 32 17 8 1183955797380233629539975243806975796624,
    decodeIntegerRow 32 17 8 1183955797380233622532763614603843687808,
    decodeIntegerRow 32 17 8 1183955800095822993438948385808508560512,
    decodeIntegerRow 32 17 8 1183955843545252921709272180177035552144,
    decodeIntegerRow 32 17 8 1183956582185561702304776684441994368128,
    decodeIntegerRow 32 17 8 1183969139070810972428353256946294949776,
    decodeIntegerRow 32 17 8 1183955797380266136773227092616391588992,
    decodeIntegerRow 32 17 8 1183955797380786358393361879501420079504,
    decodeIntegerRow 32 17 8 1183955797389630125911322951920189598848,
    decodeIntegerRow 32 17 8 1183955797539974174130276361693423356816,
    decodeIntegerRow 32 17 8 69644458669425507230709008744540759664,
    decodeIntegerRow 32 17 8 1249503523186751747374485156887530665088,
    decodeIntegerRow 32 17 8 1187811545957087630242784443262260865424,
    decodeIntegerRow 32 17 8 1183728988640418681314951307801558478208]

def cols_left1 (r : LeftIndex 3 3 3) : List ℤ := cols_left1Data.getD (leftPosition 3 3 3 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map (fun j => (left1Middle3 3 3) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_2_0
  · exact cols_left1_eq_0_2_1
  · exact cols_left1_eq_0_3_0
  · exact cols_left1_eq_0_3_1
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_1_1
  · exact cols_left1_eq_1_2_0
  · exact cols_left1_eq_1_2_1
  · exact cols_left1_eq_1_3_0
  · exact cols_left1_eq_1_3_1
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_1_0
  · exact cols_left1_eq_2_1_1
  · exact cols_left1_eq_2_2_0
  · exact cols_left1_eq_2_2_1
  · exact cols_left1_eq_2_3_0
  · exact cols_left1_eq_2_3_1
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_1_0
  · exact cols_left1_eq_3_1_1
  · exact cols_left1_eq_3_2_0
  · exact cols_left1_eq_3_2_1
  · exact cols_left1_eq_3_3_0
  · exact cols_left1_eq_3_3_1

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 65 32 5076528897714339072938867668694055614071869225974993380480,
    decodeIntegerRow 32 65 32 78100720151886944120494134382650615854206730562698511232,
    decodeIntegerRow 32 65 32 5076565290942259986273739788601924330957598903688728380544,
    decodeIntegerRow 32 65 32 80503250587225585101984101280604266634309842454389515392,
    decodeIntegerRow 32 65 32 80503241840924109343056788850042391875760548667121935232,
    decodeIntegerRow 32 65 32 5232692238722978208186750944876315096768447119403134780544,
    decodeIntegerRow 32 65 32 10231157369272504457682292072249829427378540471737031951232,
    decodeIntegerRow 32 65 32 5076528328935562468720178404595798076424150522774893110144,
    decodeIntegerRow 32 65 32 5076565859451855420630508627159462893521416639198234780544,
    decodeIntegerRow 32 65 32 80503241840892261181133362820486644805920553495090955392,
    decodeIntegerRow 32 65 32 5076528328935561978518246889795651689093907086443219780480,
    decodeIntegerRow 32 65 32 78100728902297797866873497487987542594874806793031951232,
    decodeIntegerRow 32 65 32 10231157378022979037911817455945960351271186096681198511232,
    decodeIntegerRow 32 65 32 5076528897714338582733366167792805170676698250580819510144,
    decodeIntegerRow 32 65 32 80503250587193736940005778380790907227587347282323375232,
    decodeIntegerRow 32 65 32 5232692807232574622486964425725074722508827982546328380544,
    decodeIntegerRow 32 65 32 10228754847587640381850760263085508422884309847282323375232,
    decodeIntegerRow 32 65 32 5076565290942259496303801615839682309642665482546328380544,
    decodeIntegerRow 32 65 32 10231157378022979037911817455944422683252278014799514379392,
    decodeIntegerRow 32 65 32 5076528897714338582733366167692856385415113282774893380480,
    decodeIntegerRow 32 65 32 5232729769239272140272519151769058018822222125505719780480,
    decodeIntegerRow 32 65 32 10231157369272536320923892543975235701014692345855531951232,
    decodeIntegerRow 32 65 32 5076565859451855420630508627259459003018447433219978110080,
    decodeIntegerRow 32 65 32 80503241840892261181133362818948248724503518923121935232,
    decodeIntegerRow 32 65 32 78100728902329661108473969216469174665545510799531951232,
    decodeIntegerRow 32 65 32 5232729769239271650070587636968911631491978061837393110144,
    decodeIntegerRow 32 65 32 80503241840924109343056788848503995794343523751090955392,
    decodeIntegerRow 32 65 32 5232692238722978208186750944776318987271416953015078110080,
    decodeIntegerRow 32 65 32 5232692807232574132517026252762840482544561403688728380544,
    decodeIntegerRow 32 65 32 10228754847587608533688781940185695063477587342454389515392,
    decodeIntegerRow 32 65 32 5076528897714339072938867668594106828810284885505719510144,
    decodeIntegerRow 32 65 32 78100720151886944120494134384188283873114802793014379392]

def cols_right2 (r : LeftIndex 3 3 3) : List ℤ := cols_right2Data.getD (leftPosition 3 3 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 3 3) : (tripleIndices 4 4 2).map (fun j => (right2Middle3 3 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_2_0
  · exact cols_right2_eq_0_2_1
  · exact cols_right2_eq_0_3_0
  · exact cols_right2_eq_0_3_1
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_2_0
  · exact cols_right2_eq_1_2_1
  · exact cols_right2_eq_1_3_0
  · exact cols_right2_eq_1_3_1
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_2_0
  · exact cols_right2_eq_2_2_1
  · exact cols_right2_eq_2_3_0
  · exact cols_right2_eq_2_3_1
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_2_0
  · exact cols_right2_eq_3_2_1
  · exact cols_right2_eq_3_3_0
  · exact cols_right2_eq_3_3_1

theorem product0_eq : HexagonAtoms333.outerABC * HexagonAtoms333.assocABC = HexagonAtoms333.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 4 × Fin 2) (n := Fin 4 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms333.assocABC * HexagonAtoms333.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms333.innerRightABC * HexagonAtoms333.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms333.inverseACB * right0Middle3 3 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms333.innerABC * right1Middle3 3 3 = rowColumnMul rows_innerABC cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerABC_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms333.assocABC * left0Middle3 3 3 = rowColumnMul rows_assocABC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms333.innerRightABC * left1Middle3 3 3 = rowColumnMul rows_innerRightABC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms333.assocABC * right2Middle3 3 3 = rowColumnMul rows_assocABC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn333
