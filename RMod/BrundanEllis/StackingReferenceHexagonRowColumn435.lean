import RMod.BrundanEllis.StackingReferenceHexagonAtoms435
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn435
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 328422224402716,
    decodeIntegerRow 32 3 1 797198088915688,
    decodeIntegerRow 32 3 1 1193708151335164,
    decodeIntegerRow 32 3 1 1568846033338792,
    decodeIntegerRow 32 3 1 926510079504088,
    decodeIntegerRow 32 3 1 926510088218756,
    decodeIntegerRow 32 3 1 926510091421928,
    decodeIntegerRow 32 3 1 926510080531996,
    decodeIntegerRow 32 3 1 781298352047128,
    decodeIntegerRow 32 3 1 1518014915500036,
    decodeIntegerRow 32 3 1 1565275566112168,
    decodeIntegerRow 32 3 1 644667543032476,
    decodeIntegerRow 32 3 1 926510100973284,
    decodeIntegerRow 32 3 1 926510079587032,
    decodeIntegerRow 32 3 1 926510108166916,
    decodeIntegerRow 32 3 1 926510091052568,
    decodeIntegerRow 32 3 1 926510079508324,
    decodeIntegerRow 32 3 1 926510088219672,
    decodeIntegerRow 32 3 1 926510091420036,
    decodeIntegerRow 32 3 1 926510080527448,
    decodeIntegerRow 32 3 1 1524793740936232,
    decodeIntegerRow 32 3 1 1055903544332284,
    decodeIntegerRow 32 3 1 659351468313112,
    decodeIntegerRow 32 3 1 284356501423204,
    decodeIntegerRow 32 3 1 926510087877528,
    decodeIntegerRow 32 3 1 926510109268996,
    decodeIntegerRow 32 3 1 926510080689448,
    decodeIntegerRow 32 3 1 926510097797276,
    decodeIntegerRow 32 3 1 781384273302244,
    decodeIntegerRow 32 3 1 1517820172134232,
    decodeIntegerRow 32 3 1 1565455845779716,
    decodeIntegerRow 32 3 1 644623291003288]

def rows_inverseACB (r : LeftIndex 4 5 3) : List ℤ := rows_inverseACBData.getD (leftPosition 4 5 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 5 3) : (tripleIndices 8 1 4).map ((HexagonAtoms435.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 1524597964449124,
    decodeIntegerRow 32 3 1 1055822099936152,
    decodeIntegerRow 32 3 1 659312037516676,
    decodeIntegerRow 32 3 1 284174155513048,
    decodeIntegerRow 32 3 1 926510109347752,
    decodeIntegerRow 32 3 1 926510100633084,
    decodeIntegerRow 32 3 1 926510097429912,
    decodeIntegerRow 32 3 1 926510108319844,
    decodeIntegerRow 32 3 1 1071721836804712,
    decodeIntegerRow 32 3 1 335005273351804,
    decodeIntegerRow 32 3 1 287744622739672,
    decodeIntegerRow 32 3 1 1208352645819364,
    decodeIntegerRow 32 3 1 926510087878556,
    decodeIntegerRow 32 3 1 926510109264808,
    decodeIntegerRow 32 3 1 926510080684924,
    decodeIntegerRow 32 3 1 926510097799272,
    decodeIntegerRow 32 3 1 926510079508324,
    decodeIntegerRow 32 3 1 926510088219672,
    decodeIntegerRow 32 3 1 926510091420036,
    decodeIntegerRow 32 3 1 926510080527448,
    decodeIntegerRow 32 3 1 1524793740936232,
    decodeIntegerRow 32 3 1 1055903544332284,
    decodeIntegerRow 32 3 1 659351468313112,
    decodeIntegerRow 32 3 1 284356501423204,
    decodeIntegerRow 32 3 1 926510087877528,
    decodeIntegerRow 32 3 1 926510109268996,
    decodeIntegerRow 32 3 1 926510080689448,
    decodeIntegerRow 32 3 1 926510097797276,
    decodeIntegerRow 32 3 1 781384273302244,
    decodeIntegerRow 32 3 1 1517820172134232,
    decodeIntegerRow 32 3 1 1565455845779716,
    decodeIntegerRow 32 3 1 644623291003288]

def rows_assocBCA (r : RightIndex 3 5 4) : List ℤ := rows_assocBCAData.getD (rightPosition 3 5 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 5 4) : (tripleIndices 8 1 4).map ((HexagonAtoms435.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 1658623241745056,
    decodeIntegerRow 32 3 1 469113716571560,
    decodeIntegerRow 32 3 1 11368660277000,
    decodeIntegerRow 32 3 1 560592992142432,
    decodeIntegerRow 32 3 1 937806436206760,
    decodeIntegerRow 32 3 1 921989835841504,
    decodeIntegerRow 32 3 1 935547167850592,
    decodeIntegerRow 32 3 1 932160417656440,
    decodeIntegerRow 32 3 1 560592992352320,
    decodeIntegerRow 32 3 1 11368660801920,
    decodeIntegerRow 32 3 1 1383906472017920,
    decodeIntegerRow 32 3 1 194396947526720,
    decodeIntegerRow 32 3 1 932160396392320,
    decodeIntegerRow 32 3 1 935547133840960,
    decodeIntegerRow 32 3 1 931030335999040,
    decodeIntegerRow 32 3 1 915213795157120,
    decodeIntegerRow 32 3 1 935548545348256,
    decodeIntegerRow 32 3 1 920863214939560,
    decodeIntegerRow 32 3 1 915212030773000,
    decodeIntegerRow 32 3 1 921992590836832,
    decodeIntegerRow 32 3 1 11508131653080,
    decodeIntegerRow 32 3 1 1292650350911136,
    decodeIntegerRow 32 3 1 194508524207648,
    decodeIntegerRow 32 3 1 468834773819400,
    decodeIntegerRow 32 3 1 921992607837760,
    decodeIntegerRow 32 3 1 915212073291520,
    decodeIntegerRow 32 3 1 932156952661120,
    decodeIntegerRow 32 3 1 917471677518400,
    decodeIntegerRow 32 3 1 468834774081920,
    decodeIntegerRow 32 3 1 194508524627520,
    decodeIntegerRow 32 3 1 560369838150720,
    decodeIntegerRow 32 3 1 1841512056673920]

def rows_assocCAB (r : RightIndex 5 4 3) : List ℤ := rows_assocCABData.getD (rightPosition 5 4 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 4 3) : (tripleIndices 4 2 4).map ((HexagonAtoms435.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_1_1
  · exact rows_assocCAB_eq_2_1_2
  · exact rows_assocCAB_eq_2_1_3
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_1_1
  · exact rows_assocCAB_eq_3_1_2
  · exact rows_assocCAB_eq_3_1_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 881950539463096,
    decodeIntegerRow 32 3 1 1018706872716184,
    decodeIntegerRow 32 3 1 524888147794252,
    decodeIntegerRow 32 3 1 1755144493417012,
    decodeIntegerRow 32 3 1 926510095516468,
    decodeIntegerRow 32 3 1 926510092316212,
    decodeIntegerRow 32 3 1 926510104227896,
    decodeIntegerRow 32 3 1 926510075411816,
    decodeIntegerRow 32 3 1 108015264472936,
    decodeIntegerRow 32 3 1 1348453020546616,
    decodeIntegerRow 32 3 1 1017326106093388,
    decodeIntegerRow 32 3 1 879565578932812,
    decodeIntegerRow 32 3 1 926510113675572,
    decodeIntegerRow 32 3 1 926510085096012,
    decodeIntegerRow 32 3 1 926510092284136,
    decodeIntegerRow 32 3 1 926510095461064,
    decodeIntegerRow 32 3 1 926510104228212,
    decodeIntegerRow 32 3 1 926510113439372,
    decodeIntegerRow 32 3 1 926510093338216,
    decodeIntegerRow 32 3 1 926510092310344,
    decodeIntegerRow 32 3 1 1328117749546216,
    decodeIntegerRow 32 3 1 1755172215505336,
    decodeIntegerRow 32 3 1 881821915860748,
    decodeIntegerRow 32 3 1 834562814930572,
    decodeIntegerRow 32 3 1 926510092289932,
    decodeIntegerRow 32 3 1 926510093387788,
    decodeIntegerRow 32 3 1 926510075175624,
    decodeIntegerRow 32 3 1 926510085096344,
    decodeIntegerRow 32 3 1 835441484599624,
    decodeIntegerRow 32 3 1 879688003807336,
    decodeIntegerRow 32 3 1 108043330935028,
    decodeIntegerRow 32 3 1 504553565541388]

def cols_right0 (r : LeftIndex 4 3 5) : List ℤ := cols_right0Data.getD (leftPosition 4 3 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 3 5) : (tripleIndices 8 1 4).map (fun j => (right0Middle4 3 5) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 881950539463096,
    decodeIntegerRow 32 3 1 1018706872716184,
    decodeIntegerRow 32 3 1 524888147794252,
    decodeIntegerRow 32 3 1 1755144493417012,
    decodeIntegerRow 32 3 1 926510095516468,
    decodeIntegerRow 32 3 1 926510092316212,
    decodeIntegerRow 32 3 1 926510104227896,
    decodeIntegerRow 32 3 1 926510075411816,
    decodeIntegerRow 32 3 1 108015264472936,
    decodeIntegerRow 32 3 1 1348453020546616,
    decodeIntegerRow 32 3 1 1017326106093388,
    decodeIntegerRow 32 3 1 879565578932812,
    decodeIntegerRow 32 3 1 926510113675572,
    decodeIntegerRow 32 3 1 926510085096012,
    decodeIntegerRow 32 3 1 926510092284136,
    decodeIntegerRow 32 3 1 926510095461064,
    decodeIntegerRow 32 3 1 926510104228212,
    decodeIntegerRow 32 3 1 926510113439372,
    decodeIntegerRow 32 3 1 926510093338216,
    decodeIntegerRow 32 3 1 926510092310344,
    decodeIntegerRow 32 3 1 1328117749546216,
    decodeIntegerRow 32 3 1 1755172215505336,
    decodeIntegerRow 32 3 1 881821915860748,
    decodeIntegerRow 32 3 1 834562814930572,
    decodeIntegerRow 32 3 1 926510092289932,
    decodeIntegerRow 32 3 1 926510093387788,
    decodeIntegerRow 32 3 1 926510075175624,
    decodeIntegerRow 32 3 1 926510085096344,
    decodeIntegerRow 32 3 1 835441484599624,
    decodeIntegerRow 32 3 1 879688003807336,
    decodeIntegerRow 32 3 1 108043330935028,
    decodeIntegerRow 32 3 1 504553565541388]

def cols_left0 (r : LeftIndex 4 3 5) : List ℤ := cols_left0Data.getD (leftPosition 4 3 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 3 5) : (tripleIndices 8 1 4).map (fun j => (left0Middle4 3 5) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 22370386552810781445504,
    decodeIntegerRow 32 5 2 3892958116531290820624,
    decodeIntegerRow 32 5 2 18606615066406445104,
    decodeIntegerRow 32 5 2 4489002275466843945600,
    decodeIntegerRow 32 5 2 11660128800201293815312,
    decodeIntegerRow 32 5 2 11630088046904418765312,
    decodeIntegerRow 32 5 2 11658698291162231325312,
    decodeIntegerRow 32 5 2 11653929996464966015312,
    decodeIntegerRow 32 5 2 4489002275466993945024,
    decodeIntegerRow 32 5 2 18606615066650195520,
    decodeIntegerRow 32 5 2 19390106248855509570624,
    decodeIntegerRow 32 5 2 912677812576406445504,
    decodeIntegerRow 32 5 2 11653929996363403125312,
    decodeIntegerRow 32 5 2 11658698291021606565312,
    decodeIntegerRow 32 5 2 11652976318388793765312,
    decodeIntegerRow 32 5 2 11622935565338012565312,
    decodeIntegerRow 32 5 2 11624366015630981325312,
    decodeIntegerRow 32 5 2 11653929901250121875312,
    decodeIntegerRow 32 5 2 11660128863677856575312,
    decodeIntegerRow 32 5 2 11652976230591918765312,
    decodeIntegerRow 32 5 2 23264418077468993945104,
    decodeIntegerRow 32 5 2 4488947343826218945024,
    decodeIntegerRow 32 5 2 22370349931717031445120,
    decodeIntegerRow 32 5 2 19390165758133015820624,
    decodeIntegerRow 32 5 2 11652976230498169125312,
    decodeIntegerRow 32 5 2 11660128863525512565312,
    decodeIntegerRow 32 5 2 11629134464238403125312,
    decodeIntegerRow 32 5 2 11658698349615356325312,
    decodeIntegerRow 32 5 2 19390165758132853320000,
    decodeIntegerRow 32 5 2 22370349931716806445504,
    decodeIntegerRow 32 5 2 18794117021560593945024,
    decodeIntegerRow 32 5 2 18646287918212695104]

def cols_right2 (r : LeftIndex 4 3 5) : List ℤ := cols_right2Data.getD (leftPosition 4 3 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 3 5) : (tripleIndices 4 2 4).map (fun j => (right2Middle4 3 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms435.outerABC * HexagonAtoms435.assocABC = HexagonAtoms435.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product1_eq : HexagonAtoms435.assocBAC * HexagonAtoms435.innerABC = HexagonAtoms435.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms435.innerRightABC * HexagonAtoms435.assocABC = HexagonAtoms435.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms435.inverseACB * right0Middle4 3 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms435.innerACB * right1Middle4 3 5 = right1Middle4 3 5 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms435.assocBCA * left0Middle4 3 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms435.innerRightBAC * left1Middle4 3 5 = left1Middle4 3 5 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms435.assocCAB * right2Middle4 3 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn435
