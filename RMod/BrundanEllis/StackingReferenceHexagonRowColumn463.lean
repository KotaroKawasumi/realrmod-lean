import RMod.BrundanEllis.StackingReferenceHexagonAtoms463
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn463
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 720367871280160,
    decodeIntegerRow 32 3 1 308083422153748,
    decodeIntegerRow 32 3 1 946841142057404,
    decodeIntegerRow 32 3 1 987503266061920,
    decodeIntegerRow 32 3 1 901088332003040,
    decodeIntegerRow 32 3 1 850244835811348,
    decodeIntegerRow 32 3 1 720869967171004,
    decodeIntegerRow 32 3 1 309589716203680,
    decodeIntegerRow 32 3 1 1132150220500000,
    decodeIntegerRow 32 3 1 1543430476190668,
    decodeIntegerRow 32 3 1 901088341554396,
    decodeIntegerRow 32 3 1 850244807157280,
    decodeIntegerRow 32 3 1 906179037213920,
    decodeIntegerRow 32 3 1 865516951531468,
    decodeIntegerRow 32 3 1 720367870335196,
    decodeIntegerRow 32 3 1 308083424988640,
    decodeIntegerRow 32 3 1 901094530729404,
    decodeIntegerRow 32 3 1 1002756756852640,
    decodeIntegerRow 32 3 1 1132087373468320,
    decodeIntegerRow 32 3 1 309778260842092,
    decodeIntegerRow 32 3 1 720305195254204,
    decodeIntegerRow 32 3 1 1545124794774880,
    decodeIntegerRow 32 3 1 906171298383200,
    decodeIntegerRow 32 3 1 987526511286892,
    decodeIntegerRow 32 3 1 906171288805596,
    decodeIntegerRow 32 3 1 987526482554080,
    decodeIntegerRow 32 3 1 1132714994542240,
    decodeIntegerRow 32 3 1 307895396910772,
    decodeIntegerRow 32 3 1 1132087372287196,
    decodeIntegerRow 32 3 1 309778257298720,
    decodeIntegerRow 32 3 1 951925648568160,
    decodeIntegerRow 32 3 1 850263403336372]

def rows_inverseACB (r : LeftIndex 4 3 6) : List ℤ := rows_inverseACBData.getD (leftPosition 4 3 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 3 6) : (tripleIndices 4 1 8).map ((HexagonAtoms463.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_0_4
  · exact rows_inverseACB_eq_2_0_5
  · exact rows_inverseACB_eq_2_0_6
  · exact rows_inverseACB_eq_2_0_7
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_0_4
  · exact rows_inverseACB_eq_3_0_5
  · exact rows_inverseACB_eq_3_0_6
  · exact rows_inverseACB_eq_3_0_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 857629831355212,
    decodeIntegerRow 32 3 1 948633352428136,
    decodeIntegerRow 32 3 1 1541638262277428,
    decodeIntegerRow 32 3 1 712982875736296,
    decodeIntegerRow 32 3 1 902880542373772,
    decodeIntegerRow 32 3 1 858131927246056,
    decodeIntegerRow 32 3 1 728254962714868,
    decodeIntegerRow 32 3 1 306291211783016,
    decodeIntegerRow 32 3 1 1140037341695416,
    decodeIntegerRow 32 3 1 1541638272197172,
    decodeIntegerRow 32 3 1 904386833220424,
    decodeIntegerRow 32 3 1 857629830336052,
    decodeIntegerRow 32 3 1 1546728967856696,
    decodeIntegerRow 32 3 1 728254991530612,
    decodeIntegerRow 32 3 1 994888260499144,
    decodeIntegerRow 32 3 1 902880545547892,
    decodeIntegerRow 32 3 1 1541644977565416,
    decodeIntegerRow 32 3 1 1140016306315852,
    decodeIntegerRow 32 3 1 857564744717416,
    decodeIntegerRow 32 3 1 904574347938868,
    decodeIntegerRow 32 3 1 728234128101736,
    decodeIntegerRow 32 3 1 1546721745219212,
    decodeIntegerRow 32 3 1 902691481173736,
    decodeIntegerRow 32 3 1 994827824005108,
    decodeIntegerRow 32 3 1 904574344738612,
    decodeIntegerRow 32 3 1 995455445162296,
    decodeIntegerRow 32 3 1 1140016334895412,
    decodeIntegerRow 32 3 1 311375201365704,
    decodeIntegerRow 32 3 1 994827822907252,
    decodeIntegerRow 32 3 1 950328704501176,
    decodeIntegerRow 32 3 1 1546721736008052,
    decodeIntegerRow 32 3 1 1124786031934024]

def rows_assocBCA (r : RightIndex 6 3 4) : List ℤ := rows_assocBCAData.getD (rightPosition 6 3 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 3 4) : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_0_4
  · exact rows_assocBCA_eq_2_0_5
  · exact rows_assocBCA_eq_2_0_6
  · exact rows_assocBCA_eq_2_0_7
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_0_4
  · exact rows_assocBCA_eq_3_0_5
  · exact rows_assocBCA_eq_3_0_6
  · exact rows_assocBCA_eq_3_0_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 644080544088088,
    decodeIntegerRow 32 3 1 333408061622236,
    decodeIntegerRow 32 3 1 1563671125708996,
    decodeIntegerRow 32 3 1 781906186706728,
    decodeIntegerRow 32 3 1 282570747890008,
    decodeIntegerRow 32 3 1 1056427696008796,
    decodeIntegerRow 32 3 1 659896625765956,
    decodeIntegerRow 32 3 1 330018919939048,
    decodeIntegerRow 32 3 1 926419179750168,
    decodeIntegerRow 32 3 1 926469458319196,
    decodeIntegerRow 32 3 1 926490292936516,
    decodeIntegerRow 32 3 1 926608240949288,
    decodeIntegerRow 32 3 1 926488054502488,
    decodeIntegerRow 32 3 1 926607207828956,
    decodeIntegerRow 32 3 1 926600492539076,
    decodeIntegerRow 32 3 1 926553141144808,
    decodeIntegerRow 32 3 1 1563671131745116,
    decodeIntegerRow 32 3 1 1071114032063272,
    decodeIntegerRow 32 3 1 644080571801752,
    decodeIntegerRow 32 3 1 1519612114842436,
    decodeIntegerRow 32 3 1 659896598209756,
    decodeIntegerRow 32 3 1 1523001282034792,
    decodeIntegerRow 32 3 1 282570754608472,
    decodeIntegerRow 32 3 1 796592522446276,
    decodeIntegerRow 32 3 1 926490292932004,
    decodeIntegerRow 32 3 1 926411947901528,
    decodeIntegerRow 32 3 1 926419179752168,
    decodeIntegerRow 32 3 1 926550730528444,
    decodeIntegerRow 32 3 1 926600492540964,
    decodeIntegerRow 32 3 1 926467047702808,
    decodeIntegerRow 32 3 1 926488054507048,
    decodeIntegerRow 32 3 1 926412981023804]

def rows_assocCAB (r : RightIndex 3 4 6) : List ℤ := rows_assocCABData.getD (rightPosition 3 4 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 4 6) : (tripleIndices 4 1 8).map ((HexagonAtoms463.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_0_1_4
  · exact rows_assocCAB_eq_0_1_5
  · exact rows_assocCAB_eq_0_1_6
  · exact rows_assocCAB_eq_0_1_7
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_1_1_4
  · exact rows_assocCAB_eq_1_1_5
  · exact rows_assocCAB_eq_1_1_6
  · exact rows_assocCAB_eq_1_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1544186977671416,
    decodeIntegerRow 32 3 1 1132390766108320,
    decodeIntegerRow 32 3 1 857848336021120,
    decodeIntegerRow 32 3 1 903727445143252,
    decodeIntegerRow 32 3 1 934135749306616,
    decodeIntegerRow 32 3 1 929051826331360,
    decodeIntegerRow 32 3 1 925662419991040,
    decodeIntegerRow 32 3 1 926228826621652,
    decodeIntegerRow 32 3 1 934135720608640,
    decodeIntegerRow 32 3 1 923968352955028,
    decodeIntegerRow 32 3 1 927357772050904,
    decodeIntegerRow 32 3 1 926228827680160,
    decodeIntegerRow 32 3 1 1544186977317120,
    decodeIntegerRow 32 3 1 720629422625428,
    decodeIntegerRow 32 3 1 995171852870104,
    decodeIntegerRow 32 3 1 903727445156320,
    decodeIntegerRow 32 3 1 926226502094344,
    decodeIntegerRow 32 3 1 925663194830560,
    decodeIntegerRow 32 3 1 923968104240640,
    decodeIntegerRow 32 3 1 918884525638828,
    decodeIntegerRow 32 3 1 903539158785544,
    decodeIntegerRow 32 3 1 857911098140320,
    decodeIntegerRow 32 3 1 720608502037120,
    decodeIntegerRow 32 3 1 308840184749228,
    decodeIntegerRow 32 3 1 949481030053120,
    decodeIntegerRow 32 3 1 857911098100972,
    decodeIntegerRow 32 3 1 720608501919016,
    decodeIntegerRow 32 3 1 1544180003748320,
    decodeIntegerRow 32 3 1 926793685690240,
    decodeIntegerRow 32 3 1 925663191643372,
    decodeIntegerRow 32 3 1 923968094674216,
    decodeIntegerRow 32 3 1 934135634515360]

def cols_right0 (r : LeftIndex 4 6 3) : List ℤ := cols_right0Data.getD (leftPosition 4 6 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 6 3) : (tripleIndices 4 1 8).map (fun j => (right0Middle4 6 3) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1544186977671416,
    decodeIntegerRow 32 3 1 1132390766108320,
    decodeIntegerRow 32 3 1 857848336021120,
    decodeIntegerRow 32 3 1 903727445143252,
    decodeIntegerRow 32 3 1 934135749306616,
    decodeIntegerRow 32 3 1 929051826331360,
    decodeIntegerRow 32 3 1 925662419991040,
    decodeIntegerRow 32 3 1 926228826621652,
    decodeIntegerRow 32 3 1 934135720608640,
    decodeIntegerRow 32 3 1 923968352955028,
    decodeIntegerRow 32 3 1 927357772050904,
    decodeIntegerRow 32 3 1 926228827680160,
    decodeIntegerRow 32 3 1 1544186977317120,
    decodeIntegerRow 32 3 1 720629422625428,
    decodeIntegerRow 32 3 1 995171852870104,
    decodeIntegerRow 32 3 1 903727445156320,
    decodeIntegerRow 32 3 1 926226502094344,
    decodeIntegerRow 32 3 1 925663194830560,
    decodeIntegerRow 32 3 1 923968104240640,
    decodeIntegerRow 32 3 1 918884525638828,
    decodeIntegerRow 32 3 1 903539158785544,
    decodeIntegerRow 32 3 1 857911098140320,
    decodeIntegerRow 32 3 1 720608502037120,
    decodeIntegerRow 32 3 1 308840184749228,
    decodeIntegerRow 32 3 1 949481030053120,
    decodeIntegerRow 32 3 1 857911098100972,
    decodeIntegerRow 32 3 1 720608501919016,
    decodeIntegerRow 32 3 1 1544180003748320,
    decodeIntegerRow 32 3 1 926793685690240,
    decodeIntegerRow 32 3 1 925663191643372,
    decodeIntegerRow 32 3 1 923968094674216,
    decodeIntegerRow 32 3 1 934135634515360]

def cols_left0 (r : LeftIndex 4 6 3) : List ℤ := cols_left0Data.getD (leftPosition 4 6 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 6 3) : (tripleIndices 4 1 8).map (fun j => (left0Middle4 6 3) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 9391337633072372070312,
    decodeIntegerRow 32 5 2 2405196428284400195312,
    decodeIntegerRow 32 5 2 21025687456121312695312,
    decodeIntegerRow 32 5 2 10136634111465965820312,
    decodeIntegerRow 32 5 2 2250224351873072070312,
    decodeIntegerRow 32 5 2 13116866350235450195312,
    decodeIntegerRow 32 5 2 9421378374160262695312,
    decodeIntegerRow 32 5 2 2400428056731665820312,
    decodeIntegerRow 32 5 2 11641508525466918907560,
    decodeIntegerRow 32 5 2 11641526499099731290352,
    decodeIntegerRow 32 5 2 11641528405838012852752,
    decodeIntegerRow 32 5 2 11641556224441528295064,
    decodeIntegerRow 32 5 2 11641528330154418787752,
    decodeIntegerRow 32 5 2 11641556206130981470064,
    decodeIntegerRow 32 5 2 11641555827713012658064,
    decodeIntegerRow 32 5 2 11641537943191528165272,
    decodeIntegerRow 32 5 2 21025687456140650195312,
    decodeIntegerRow 32 5 2 13146430254044090820312,
    decodeIntegerRow 32 5 2 9391337633193497070312,
    decodeIntegerRow 32 5 2 20877867937073462695312,
    decodeIntegerRow 32 5 2 9421378374039200195312,
    decodeIntegerRow 32 5 2 20882636308684790820312,
    decodeIntegerRow 32 5 2 2250224351892797070312,
    decodeIntegerRow 32 5 2 10166198015274512695312,
    decodeIntegerRow 32 5 2 11641528405838012537872,
    decodeIntegerRow 32 5 2 11641508140945434545064,
    decodeIntegerRow 32 5 2 11641508525466918983064,
    decodeIntegerRow 32 5 2 11641537866287231290352,
    decodeIntegerRow 32 5 2 11641555827713012732560,
    decodeIntegerRow 32 5 2 11641526422195434415272,
    decodeIntegerRow 32 5 2 11641528330154419102872,
    decodeIntegerRow 32 5 2 11641508159255981470064]

def cols_right2 (r : LeftIndex 4 6 3) : List ℤ := cols_right2Data.getD (leftPosition 4 6 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 6 3) : (tripleIndices 4 1 8).map (fun j => (right2Middle4 6 3) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms463.outerABC * HexagonAtoms463.assocABC = HexagonAtoms463.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms463.assocBAC * HexagonAtoms463.innerABC = HexagonAtoms463.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms463.innerRightABC * HexagonAtoms463.assocABC = HexagonAtoms463.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms463.inverseACB * right0Middle4 6 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms463.innerACB * right1Middle4 6 3 = right1Middle4 6 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms463.assocBCA * left0Middle4 6 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms463.innerRightBAC * left1Middle4 6 3 = left1Middle4 6 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms463.assocCAB * right2Middle4 6 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn463
