import RMod.BrundanEllis.StackingReferenceHexagonAtoms313
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn313
open Superfusion

theorem assocBCA_alias : HexagonAtoms313.assocBCA = HexagonAtoms313.assocBAC :=
  HexagonAtoms313.assocBCA_eq.symm.trans HexagonAtoms313.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 26306328]

def rows_inverseACB (r : LeftIndex 3 3 1) : List ℤ := rows_inverseACBData.getD (leftPosition 3 3 1 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 3 1) : (tripleIndices 2 4 2).map ((HexagonAtoms313.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 36219508,
    decodeIntegerRow 16 3 1 27819788,
    decodeIntegerRow 16 3 1 24670344,
    decodeIntegerRow 16 3 1 35169256,
    decodeIntegerRow 16 3 1 6826228,
    decodeIntegerRow 16 3 1 15222668,
    decodeIntegerRow 16 3 1 18371784,
    decodeIntegerRow 16 3 1 7875496,
    decodeIntegerRow 16 3 1 27977304,
    decodeIntegerRow 16 3 1 36586936,
    decodeIntegerRow 16 3 1 7536268,
    decodeIntegerRow 16 3 1 18297588,
    decodeIntegerRow 16 3 1 27981464,
    decodeIntegerRow 16 3 1 36587896,
    decodeIntegerRow 16 3 1 7534348,
    decodeIntegerRow 16 3 1 18293108]

def rows_innerACB (r : LeftIndex 3 3 1) : List ℤ := rows_innerACBData.getD (leftPosition 3 3 1 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 3 3 1) : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_0_1
  · exact rows_innerACB_eq_2_1_0
  · exact rows_innerACB_eq_2_1_1
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_0_1
  · exact rows_innerACB_eq_3_1_0
  · exact rows_innerACB_eq_3_1_1

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37465780,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 21575872]

def rows_assocBAC (r : RightIndex 1 3 3) : List ℤ := rows_assocBACData.getD (rightPosition 1 3 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 1 3 3) : (tripleIndices 2 4 2).map ((HexagonAtoms313.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_1_1
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_1_1

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 36219508,
    decodeIntegerRow 16 3 1 27819788,
    decodeIntegerRow 16 3 1 24670344,
    decodeIntegerRow 16 3 1 35169256,
    decodeIntegerRow 16 3 1 6826228,
    decodeIntegerRow 16 3 1 15222668,
    decodeIntegerRow 16 3 1 18371784,
    decodeIntegerRow 16 3 1 7875496,
    decodeIntegerRow 16 3 1 27977304,
    decodeIntegerRow 16 3 1 36586936,
    decodeIntegerRow 16 3 1 7536268,
    decodeIntegerRow 16 3 1 18297588,
    decodeIntegerRow 16 3 1 27981464,
    decodeIntegerRow 16 3 1 36587896,
    decodeIntegerRow 16 3 1 7534348,
    decodeIntegerRow 16 3 1 18293108]

def rows_innerRightBAC (r : RightIndex 1 3 3) : List ℤ := rows_innerRightBACData.getD (rightPosition 1 3 3 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 1 3 3) : (tripleIndices 4 2 2).map ((HexagonAtoms313.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_0_1
  · exact rows_innerRightBAC_eq_2_1_0
  · exact rows_innerRightBAC_eq_2_1_1
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_0_1
  · exact rows_innerRightBAC_eq_3_1_0
  · exact rows_innerRightBAC_eq_3_1_1

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21503758,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21462124,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 20991916,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 35872276,
    decodeIntegerRow 16 3 1 26306356]

def rows_assocCAB (r : RightIndex 3 3 1) : List ℤ := rows_assocCABData.getD (rightPosition 3 3 1 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 3 1) : (tripleIndices 4 2 2).map ((HexagonAtoms313.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_2_0
  · exact rows_assocCAB_eq_0_2_1
  · exact rows_assocCAB_eq_0_3_0
  · exact rows_assocCAB_eq_0_3_1
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_2_0
  · exact rows_assocCAB_eq_1_2_1
  · exact rows_assocCAB_eq_1_3_0
  · exact rows_assocCAB_eq_1_3_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346214,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 21503686]

def cols_right0 (r : LeftIndex 3 1 3) : List ℤ := cols_right0Data.getD (leftPosition 3 1 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 1 3) : (tripleIndices 2 4 2).map (fun j => (right0Middle3 1 3) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 18334742,
    decodeIntegerRow 16 3 1 7705906,
    decodeIntegerRow 16 3 1 27900678,
    decodeIntegerRow 16 3 1 36403714,
    decodeIntegerRow 16 3 1 21707554,
    decodeIntegerRow 16 3 1 21604198,
    decodeIntegerRow 16 3 1 21692974,
    decodeIntegerRow 16 3 1 21560458,
    decodeIntegerRow 16 3 1 7705882,
    decodeIntegerRow 16 3 1 18334686,
    decodeIntegerRow 16 3 1 36403702,
    decodeIntegerRow 16 3 1 27900626,
    decodeIntegerRow 16 3 1 21599986,
    decodeIntegerRow 16 3 1 21706582,
    decodeIntegerRow 16 3 1 21564994,
    decodeIntegerRow 16 3 1 21694918]

def cols_right1 (r : LeftIndex 3 1 3) : List ℤ := cols_right1Data.getD (leftPosition 3 1 3 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 3 1 3) : (tripleIndices 4 2 2).map (fun j => (right1Middle3 1 3) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346214,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 21503686]

def cols_left0 (r : LeftIndex 3 1 3) : List ℤ := cols_left0Data.getD (leftPosition 3 1 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 1 3) : (tripleIndices 2 4 2).map (fun j => (left0Middle3 1 3) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 18334742,
    decodeIntegerRow 16 3 1 7705906,
    decodeIntegerRow 16 3 1 27900678,
    decodeIntegerRow 16 3 1 36403714,
    decodeIntegerRow 16 3 1 21707554,
    decodeIntegerRow 16 3 1 21604198,
    decodeIntegerRow 16 3 1 21692974,
    decodeIntegerRow 16 3 1 21560458,
    decodeIntegerRow 16 3 1 7705882,
    decodeIntegerRow 16 3 1 18334686,
    decodeIntegerRow 16 3 1 36403702,
    decodeIntegerRow 16 3 1 27900626,
    decodeIntegerRow 16 3 1 21599986,
    decodeIntegerRow 16 3 1 21706582,
    decodeIntegerRow 16 3 1 21564994,
    decodeIntegerRow 16 3 1 21694918]

def cols_left1 (r : LeftIndex 3 1 3) : List ℤ := cols_left1Data.getD (leftPosition 3 1 3 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 3 1 3) : (tripleIndices 4 2 2).map (fun j => (left1Middle3 1 3) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 1750074622804192,
    decodeIntegerRow 16 9 4 1018017264242848,
    decodeIntegerRow 16 9 4 926510266376608,
    decodeIntegerRow 16 9 4 926511644081632,
    decodeIntegerRow 16 9 4 936677557739232,
    decodeIntegerRow 16 9 4 927639812571808,
    decodeIntegerRow 16 9 4 926496166420192,
    decodeIntegerRow 16 9 4 926384572313248,
    decodeIntegerRow 16 9 4 926524060695400,
    decodeIntegerRow 16 9 4 926635620790120,
    decodeIntegerRow 16 9 4 936677557739240,
    decodeIntegerRow 16 9 4 927639812571880,
    decodeIntegerRow 16 9 4 926510266849000,
    decodeIntegerRow 16 9 4 926511644134120,
    decodeIntegerRow 16 9 4 102945566047000,
    decodeIntegerRow 16 9 4 835002924603160]

def cols_right2 (r : LeftIndex 3 1 3) : List ℤ := cols_right2Data.getD (leftPosition 3 1 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 1 3) : (tripleIndices 4 2 2).map (fun j => (right2Middle3 1 3) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms313.outerABC * HexagonAtoms313.assocABC = HexagonAtoms313.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms313.assocBAC * HexagonAtoms313.innerABC = HexagonAtoms313.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product2_eq : HexagonAtoms313.innerRightABC * HexagonAtoms313.assocABC = HexagonAtoms313.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product3_eq : HexagonAtoms313.inverseACB * right0Middle3 1 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms313.innerACB * right1Middle3 1 3 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms313.assocBAC * left0Middle3 1 3 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms313.innerRightBAC * left1Middle3 1 3 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms313.assocCAB * right2Middle3 1 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn313
