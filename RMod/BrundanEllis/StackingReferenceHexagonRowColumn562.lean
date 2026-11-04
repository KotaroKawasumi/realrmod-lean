import RMod.BrundanEllis.StackingReferenceHexagonAtoms562
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn562
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 923971715387824,
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

def rows_inverseACB (r : LeftIndex 5 2 6) : List ℤ := rows_inverseACBData.getD (leftPosition 5 2 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 2 6) : (tripleIndices 4 1 8).map ((HexagonAtoms562.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 289439461599116,
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

def rows_assocBCA (r : RightIndex 6 2 5) : List ℤ := rows_assocBCAData.getD (rightPosition 6 2 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 2 5) : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 651967678079716,
    decodeIntegerRow 32 3 1 331615867011484,
    decodeIntegerRow 32 3 1 1566969629958076,
    decodeIntegerRow 32 3 1 789291166230724,
    decodeIntegerRow 32 3 1 923120681878436,
    decodeIntegerRow 32 3 1 919165721247964,
    decodeIntegerRow 32 3 1 934417002271996,
    decodeIntegerRow 32 3 1 924816033584004,
    decodeIntegerRow 32 3 1 928204154900472,
    decodeIntegerRow 32 3 1 918603186658552,
    decodeIntegerRow 32 3 1 919165721090488,
    decodeIntegerRow 32 3 1 923120681537208,
    decodeIntegerRow 32 3 1 1063728992864632,
    decodeIntegerRow 32 3 1 286050565269112,
    decodeIntegerRow 32 3 1 331615854255928,
    decodeIntegerRow 32 3 1 651967650440248,
    decodeIntegerRow 32 3 1 1567150942748872,
    decodeIntegerRow 32 3 1 1063812705450952,
    decodeIntegerRow 32 3 1 652009519487992,
    decodeIntegerRow 32 3 1 1521209061914872,
    decodeIntegerRow 32 3 1 934419240701512,
    decodeIntegerRow 32 3 1 928205188389192,
    decodeIntegerRow 32 3 1 923121198439032,
    decodeIntegerRow 32 3 1 933852056987512,
    decodeIntegerRow 32 3 1 919168131706876,
    decodeIntegerRow 32 3 1 929898990753924,
    decodeIntegerRow 32 3 1 928205188021724,
    decodeIntegerRow 32 3 1 934419240622756,
    decodeIntegerRow 32 3 1 331811114183356,
    decodeIntegerRow 32 3 1 1201010696994244,
    decodeIntegerRow 32 3 1 1063812675686044,
    decodeIntegerRow 32 3 1 1567150936369636]

def rows_assocCAB (r : RightIndex 2 5 6) : List ℤ := rows_assocCABData.getD (rightPosition 2 5 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 5 6) : (tripleIndices 4 1 8).map ((HexagonAtoms562.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 789291181187692,
    decodeIntegerRow 32 3 1 286050561910880,
    decodeIntegerRow 32 3 1 331615860817440,
    decodeIntegerRow 32 3 1 1201052524631236,
    decodeIntegerRow 32 3 1 924816040144492,
    decodeIntegerRow 32 3 1 918603172804000,
    decodeIntegerRow 32 3 1 919165736051680,
    decodeIntegerRow 32 3 1 929899510333636,
    decodeIntegerRow 32 3 1 1567150939729868,
    decodeIntegerRow 32 3 1 1063812690489760,
    decodeIntegerRow 32 3 1 652009505633440,
    decodeIntegerRow 32 3 1 1521209068107996,
    decodeIntegerRow 32 3 1 934419254481868,
    decodeIntegerRow 32 3 1 928205181827680,
    decodeIntegerRow 32 3 1 923121195080800,
    decodeIntegerRow 32 3 1 933852042187996,
    decodeIntegerRow 32 3 1 1521209068475360,
    decodeIntegerRow 32 3 1 1201010683139692,
    decodeIntegerRow 32 3 1 1063812690647236,
    decodeIntegerRow 32 3 1 285869249463200,
    decodeIntegerRow 32 3 1 933852071944480,
    decodeIntegerRow 32 3 1 929898987395692,
    decodeIntegerRow 32 3 1 928205194583236,
    decodeIntegerRow 32 3 1 918600962009440,
    decodeIntegerRow 32 3 1 651967664299360,
    decodeIntegerRow 32 3 1 331615860449972,
    decodeIntegerRow 32 3 1 1566969626599844,
    decodeIntegerRow 32 3 1 789291181030240,
    decodeIntegerRow 32 3 1 923120684897440,
    decodeIntegerRow 32 3 1 919165706286772,
    decodeIntegerRow 32 3 1 934416988417444,
    decodeIntegerRow 32 3 1 924816027390880]

def cols_right0 (r : LeftIndex 5 6 2) : List ℤ := cols_right0Data.getD (leftPosition 5 6 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 6 2) : (tripleIndices 4 1 8).map (fun j => (right0Middle5 6 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 789291181187692,
    decodeIntegerRow 32 3 1 286050561910880,
    decodeIntegerRow 32 3 1 331615860817440,
    decodeIntegerRow 32 3 1 1201052524631236,
    decodeIntegerRow 32 3 1 924816040144492,
    decodeIntegerRow 32 3 1 918603172804000,
    decodeIntegerRow 32 3 1 919165736051680,
    decodeIntegerRow 32 3 1 929899510333636,
    decodeIntegerRow 32 3 1 1567150939729868,
    decodeIntegerRow 32 3 1 1063812690489760,
    decodeIntegerRow 32 3 1 652009505633440,
    decodeIntegerRow 32 3 1 1521209068107996,
    decodeIntegerRow 32 3 1 934419254481868,
    decodeIntegerRow 32 3 1 928205181827680,
    decodeIntegerRow 32 3 1 923121195080800,
    decodeIntegerRow 32 3 1 933852042187996,
    decodeIntegerRow 32 3 1 1521209068475360,
    decodeIntegerRow 32 3 1 1201010683139692,
    decodeIntegerRow 32 3 1 1063812690647236,
    decodeIntegerRow 32 3 1 285869249463200,
    decodeIntegerRow 32 3 1 933852071944480,
    decodeIntegerRow 32 3 1 929898987395692,
    decodeIntegerRow 32 3 1 928205194583236,
    decodeIntegerRow 32 3 1 918600962009440,
    decodeIntegerRow 32 3 1 651967664299360,
    decodeIntegerRow 32 3 1 331615860449972,
    decodeIntegerRow 32 3 1 1566969626599844,
    decodeIntegerRow 32 3 1 789291181030240,
    decodeIntegerRow 32 3 1 923120684897440,
    decodeIntegerRow 32 3 1 919165706286772,
    decodeIntegerRow 32 3 1 934416988417444,
    decodeIntegerRow 32 3 1 924816027390880]

def cols_left0 (r : LeftIndex 5 6 2) : List ℤ := cols_left0Data.getD (leftPosition 5 6 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 6 2) : (tripleIndices 4 1 8).map (fun j => (left0Middle5 6 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 9406354188979614415312,
    decodeIntegerRow 32 5 2 2402788209929809595312,
    decodeIntegerRow 32 5 2 21029240083704223595312,
    decodeIntegerRow 32 5 2 10151421785293090975312,
    decodeIntegerRow 32 5 2 11637955897903539258064,
    decodeIntegerRow 32 5 2 11626750192337059570352,
    decodeIntegerRow 32 5 2 11656552515335098632752,
    decodeIntegerRow 32 5 2 11639148006057640820560,
    decodeIntegerRow 32 5 2 11643916359329125195560,
    decodeIntegerRow 32 5 2 11626511850051895507752,
    decodeIntegerRow 32 5 2 11626750192337012695272,
    decodeIntegerRow 32 5 2 11637955897903345507560,
    decodeIntegerRow 32 5 2 13131642579970825350312,
    decodeIntegerRow 32 5 2 2253824281702270470312,
    decodeIntegerRow 32 5 2 2402788209900512670312,
    decodeIntegerRow 32 5 2 9406354188858520350312,
    decodeIntegerRow 32 5 2 21029287385950317420312,
    decodeIntegerRow 32 5 2 13131654024185669100312,
    decodeIntegerRow 32 5 2 9406361818374145350312,
    decodeIntegerRow 32 5 2 20880228090271606470312,
    decodeIntegerRow 32 5 2 11656552591018692382872,
    decodeIntegerRow 32 5 2 11643916377639868945560,
    decodeIntegerRow 32 5 2 11637955910110570507560,
    decodeIntegerRow 32 5 2 11656314096145606445352,
    decodeIntegerRow 32 5 2 11626750269241309570352,
    decodeIntegerRow 32 5 2 11645108455276586132560,
    decodeIntegerRow 32 5 2 11643916377639672070064,
    decodeIntegerRow 32 5 2 11656552591018661132752,
    decodeIntegerRow 32 5 2 2402836275086059595312,
    decodeIntegerRow 32 5 2 13876702547133910975312,
    decodeIntegerRow 32 5 2 13131654024062621915312,
    decodeIntegerRow 32 5 2 21029287385930786095312]

def cols_right2 (r : LeftIndex 5 6 2) : List ℤ := cols_right2Data.getD (leftPosition 5 6 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 6 2) : (tripleIndices 4 1 8).map (fun j => (right2Middle5 6 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms562.outerABC * HexagonAtoms562.assocABC = HexagonAtoms562.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms562.assocBAC * HexagonAtoms562.innerABC = HexagonAtoms562.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms562.innerRightABC * HexagonAtoms562.assocABC = HexagonAtoms562.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms562.inverseACB * right0Middle5 6 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms562.innerACB * right1Middle5 6 2 = right1Middle5 6 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms562.assocBCA * left0Middle5 6 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms562.innerRightBAC * left1Middle5 6 2 = left1Middle5 6 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms562.assocCAB * right2Middle5 6 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn562
