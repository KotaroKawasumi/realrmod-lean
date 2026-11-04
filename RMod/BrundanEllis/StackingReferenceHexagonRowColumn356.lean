import RMod.BrundanEllis.StackingReferenceHexagonAtoms356
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn356
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510080778548,
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

def rows_outerABC (r : LeftIndex 5 6 3) : List ℤ := rows_outerABCData.getD (leftPosition 5 6 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 5 6 3) : (tripleIndices 2 4 4).map ((HexagonAtoms356.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_1_1
  · exact rows_outerABC_eq_0_1_2
  · exact rows_outerABC_eq_0_1_3
  · exact rows_outerABC_eq_0_2_0
  · exact rows_outerABC_eq_0_2_1
  · exact rows_outerABC_eq_0_2_2
  · exact rows_outerABC_eq_0_2_3
  · exact rows_outerABC_eq_0_3_0
  · exact rows_outerABC_eq_0_3_1
  · exact rows_outerABC_eq_0_3_2
  · exact rows_outerABC_eq_0_3_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_1_1
  · exact rows_outerABC_eq_1_1_2
  · exact rows_outerABC_eq_1_1_3
  · exact rows_outerABC_eq_1_2_0
  · exact rows_outerABC_eq_1_2_1
  · exact rows_outerABC_eq_1_2_2
  · exact rows_outerABC_eq_1_2_3
  · exact rows_outerABC_eq_1_3_0
  · exact rows_outerABC_eq_1_3_1
  · exact rows_outerABC_eq_1_3_2
  · exact rows_outerABC_eq_1_3_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 926520683919368,
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

def rows_inverseACB (r : LeftIndex 3 6 5) : List ℤ := rows_inverseACBData.getD (leftPosition 3 6 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 6 5) : (tripleIndices 2 4 4).map ((HexagonAtoms356.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 926411259154012,
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

def rows_assocBCA (r : RightIndex 5 6 3) : List ℤ := rows_assocBCAData.getD (rightPosition 5 6 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 6 3) : (tripleIndices 2 4 4).map ((HexagonAtoms356.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 1563580727593952,
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

def rows_assocCAB (r : RightIndex 6 3 5) : List ℤ := rows_assocCABData.getD (rightPosition 6 3 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 3 5) : (tripleIndices 4 2 4).map ((HexagonAtoms356.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_4_0_0
  · exact rows_assocCAB_eq_4_0_1
  · exact rows_assocCAB_eq_4_0_2
  · exact rows_assocCAB_eq_4_0_3
  · exact rows_assocCAB_eq_5_0_0
  · exact rows_assocCAB_eq_5_0_1
  · exact rows_assocCAB_eq_5_0_2
  · exact rows_assocCAB_eq_5_0_3
  · exact rows_assocCAB_eq_6_0_0
  · exact rows_assocCAB_eq_6_0_1
  · exact rows_assocCAB_eq_6_0_2
  · exact rows_assocCAB_eq_6_0_3
  · exact rows_assocCAB_eq_7_0_0
  · exact rows_assocCAB_eq_7_0_1
  · exact rows_assocCAB_eq_7_0_2
  · exact rows_assocCAB_eq_7_0_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 293847267056684,
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

def cols_assocABC (r : LeftIndex 3 5 6) : List ℤ := cols_assocABCData.getD (leftPosition 3 5 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 5 6) : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms356.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_4_0_0
  · exact cols_assocABC_eq_4_0_1
  · exact cols_assocABC_eq_4_0_2
  · exact cols_assocABC_eq_4_0_3
  · exact cols_assocABC_eq_5_0_0
  · exact cols_assocABC_eq_5_0_1
  · exact cols_assocABC_eq_5_0_2
  · exact cols_assocABC_eq_5_0_3
  · exact cols_assocABC_eq_6_0_0
  · exact cols_assocABC_eq_6_0_1
  · exact cols_assocABC_eq_6_0_2
  · exact cols_assocABC_eq_6_0_3
  · exact cols_assocABC_eq_7_0_0
  · exact cols_assocABC_eq_7_0_1
  · exact cols_assocABC_eq_7_0_2
  · exact cols_assocABC_eq_7_0_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 293847267056684,
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

def cols_right0 (r : LeftIndex 3 5 6) : List ℤ := cols_right0Data.getD (leftPosition 3 5 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 5 6) : (tripleIndices 2 4 4).map (fun j => (right0Middle3 5 6) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_4_0_0
  · exact cols_right0_eq_4_0_1
  · exact cols_right0_eq_4_0_2
  · exact cols_right0_eq_4_0_3
  · exact cols_right0_eq_5_0_0
  · exact cols_right0_eq_5_0_1
  · exact cols_right0_eq_5_0_2
  · exact cols_right0_eq_5_0_3
  · exact cols_right0_eq_6_0_0
  · exact cols_right0_eq_6_0_1
  · exact cols_right0_eq_6_0_2
  · exact cols_right0_eq_6_0_3
  · exact cols_right0_eq_7_0_0
  · exact cols_right0_eq_7_0_1
  · exact cols_right0_eq_7_0_2
  · exact cols_right0_eq_7_0_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1735679517896940558828891082240,
    decodeIntegerRow 32 9 4 1718934985551076698702113056016,
    decodeIntegerRow 32 9 4 3242691008668418150636517948160,
    decodeIntegerRow 32 9 4 1886380698968187400578271315216,
    decodeIntegerRow 32 9 4 1886380698870940901067322447360,
    decodeIntegerRow 32 9 4 190992810748875838422867869584,
    decodeIntegerRow 32 9 4 1718934977674110238315599133440,
    decodeIntegerRow 32 9 4 1698004231502873782350333648784,
    decodeIntegerRow 32 9 4 1697998488308163786659182320496,
    decodeIntegerRow 32 9 4 1714748204488058571458886629120,
    decodeIntegerRow 32 9 4 190527612852718080156782525296,
    decodeIntegerRow 32 9 4 1547251432766472596625078039040,
    decodeIntegerRow 32 9 4 1547251432669196448791116044784,
    decodeIntegerRow 32 9 4 3243156206564309073995332099840,
    decodeIntegerRow 32 9 4 1714748196608690596907620825584,
    decodeIntegerRow 32 9 4 1735685261070036927037273592320,
    decodeIntegerRow 32 9 4 3243156206564309053663543095040,
    decodeIntegerRow 32 9 4 1547251432669196446532019875824,
    decodeIntegerRow 32 9 4 1735685261070035280159265784320,
    decodeIntegerRow 32 9 4 1714748196608690413921175408624,
    decodeIntegerRow 32 9 4 1718935615804454096185407772160,
    decodeIntegerRow 32 9 4 1735685331984347051120658016144,
    decodeIntegerRow 32 9 4 1886432387526039890291858717440,
    decodeIntegerRow 32 9 4 3243156207439794384169201043344,
    decodeIntegerRow 32 9 4 190992810748875818084803609456,
    decodeIntegerRow 32 9 4 1886380698870940898807546033920,
    decodeIntegerRow 32 9 4 1698004231502872134970227942256,
    decodeIntegerRow 32 9 4 1718934977674110055273365271040,
    decodeIntegerRow 32 9 4 1714748834741435968997970000656,
    decodeIntegerRow 32 9 4 1698004302395570278448853245440,
    decodeIntegerRow 32 9 4 1547303121324325086339362691856,
    decodeIntegerRow 32 9 4 190992811624094313683343420160]

def cols_left0 (r : LeftIndex 3 5 6) : List ℤ := cols_left0Data.getD (leftPosition 3 5 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 5 6) : (tripleIndices 2 4 4).map (fun j => (left0Middle3 5 6) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_4_0_0
  · exact cols_left0_eq_4_0_1
  · exact cols_left0_eq_4_0_2
  · exact cols_left0_eq_4_0_3
  · exact cols_left0_eq_5_0_0
  · exact cols_left0_eq_5_0_1
  · exact cols_left0_eq_5_0_2
  · exact cols_left0_eq_5_0_3
  · exact cols_left0_eq_6_0_0
  · exact cols_left0_eq_6_0_1
  · exact cols_left0_eq_6_0_2
  · exact cols_left0_eq_6_0_3
  · exact cols_left0_eq_7_0_0
  · exact cols_left0_eq_7_0_1
  · exact cols_left0_eq_7_0_2
  · exact cols_left0_eq_7_0_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 21025663811101781408064,
    decodeIntegerRow 32 5 2 10166203698868262850272,
    decodeIntegerRow 32 5 2 13861689768203231287872,
    decodeIntegerRow 32 5 2 20877891960540062670560,
    decodeIntegerRow 32 5 2 2400404014983618920064,
    decodeIntegerRow 32 5 2 13891730584732528477872,
    decodeIntegerRow 32 5 2 13146424493546044100352,
    decodeIntegerRow 32 5 2 21032816356287328358064,
    decodeIntegerRow 32 5 2 2250248009119359608064,
    decodeIntegerRow 32 5 2 13146424493422950040272,
    decodeIntegerRow 32 5 2 9391333780533309727872,
    decodeIntegerRow 32 5 2 2400404014954125220560,
    decodeIntegerRow 32 5 2 20877891960510962720064,
    decodeIntegerRow 32 5 2 9421374597304793787872,
    decodeIntegerRow 32 5 2 10166203698745262540352,
    decodeIntegerRow 32 5 2 2257400554265843908064,
    decodeIntegerRow 32 5 2 13891722879775528477872,
    decodeIntegerRow 32 5 2 2400452098450218920064,
    decodeIntegerRow 32 5 2 21032863670720728358064,
    decodeIntegerRow 32 5 2 13146436014419044100352,
    decodeIntegerRow 32 5 2 13116872033829200040352,
    decodeIntegerRow 32 5 2 2257353264226781482560,
    decodeIntegerRow 32 5 2 2405220451751000220064,
    decodeIntegerRow 32 5 2 9421382151015731602752,
    decodeIntegerRow 32 5 2 13861682214492294102752,
    decodeIntegerRow 32 5 2 2405220451721900170560,
    decodeIntegerRow 32 5 2 21025711101140843982560,
    decodeIntegerRow 32 5 2 13116872033706200350272,
    decodeIntegerRow 32 5 2 13146436014542137540272,
    decodeIntegerRow 32 5 2 2250200694646509608064,
    decodeIntegerRow 32 5 2 2400452098479712720560,
    decodeIntegerRow 32 5 2 9391341485732559727872]

def cols_right2 (r : LeftIndex 3 5 6) : List ℤ := cols_right2Data.getD (leftPosition 3 5 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 5 6) : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 6) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_4_0_0
  · exact cols_right2_eq_4_0_1
  · exact cols_right2_eq_4_0_2
  · exact cols_right2_eq_4_0_3
  · exact cols_right2_eq_5_0_0
  · exact cols_right2_eq_5_0_1
  · exact cols_right2_eq_5_0_2
  · exact cols_right2_eq_5_0_3
  · exact cols_right2_eq_6_0_0
  · exact cols_right2_eq_6_0_1
  · exact cols_right2_eq_6_0_2
  · exact cols_right2_eq_6_0_3
  · exact cols_right2_eq_7_0_0
  · exact cols_right2_eq_7_0_1
  · exact cols_right2_eq_7_0_2
  · exact cols_right2_eq_7_0_3

theorem product0_eq : HexagonAtoms356.outerABC * HexagonAtoms356.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms356.assocBAC * HexagonAtoms356.innerABC = HexagonAtoms356.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms356.innerRightABC * HexagonAtoms356.assocABC = HexagonAtoms356.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms356.inverseACB * right0Middle3 5 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms356.innerACB * right1Middle3 5 6 = right1Middle3 5 6 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms356.assocBCA * left0Middle3 5 6 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms356.innerRightBAC * left1Middle3 5 6 = left1Middle3 5 6 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms356.assocCAB * right2Middle3 5 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn356
