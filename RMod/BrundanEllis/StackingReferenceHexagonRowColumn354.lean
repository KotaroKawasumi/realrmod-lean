import RMod.BrundanEllis.StackingReferenceHexagonAtoms354
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn354
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425921,
    decodeIntegerRow 32 3 1 926510094425923,
    decodeIntegerRow 32 3 1 926510094425929,
    decodeIntegerRow 32 3 1 926510094425947,
    decodeIntegerRow 32 3 1 926510094426001,
    decodeIntegerRow 32 3 1 926510094426163,
    decodeIntegerRow 32 3 1 926510094426649,
    decodeIntegerRow 32 3 1 926510094428107,
    decodeIntegerRow 32 3 1 926510094432481,
    decodeIntegerRow 32 3 1 926510094445603,
    decodeIntegerRow 32 3 1 926510094484969,
    decodeIntegerRow 32 3 1 926510094603067,
    decodeIntegerRow 32 3 1 926510094957361,
    decodeIntegerRow 32 3 1 926510096020243,
    decodeIntegerRow 32 3 1 926510099208889,
    decodeIntegerRow 32 3 1 926510108774827,
    decodeIntegerRow 32 3 1 926510051379199,
    decodeIntegerRow 32 3 1 926509965285757,
    decodeIntegerRow 32 3 1 926509707005431,
    decodeIntegerRow 32 3 1 926508932164453,
    decodeIntegerRow 32 3 1 926506607641519,
    decodeIntegerRow 32 3 1 926499634072717,
    decodeIntegerRow 32 3 1 926478713366311,
    decodeIntegerRow 32 3 1 926415951247093,
    decodeIntegerRow 32 3 1 926227664889439,
    decodeIntegerRow 32 3 1 925662805816477,
    decodeIntegerRow 32 3 1 923968228597591,
    decodeIntegerRow 32 3 1 918884496940933,
    decodeIntegerRow 32 3 1 903633301970959,
    decodeIntegerRow 32 3 1 857879717061037,
    decodeIntegerRow 32 3 1 720618962331271,
    decodeIntegerRow 32 3 1 308836698141973]

def rows_outerABC (r : LeftIndex 5 4 3) : List ℤ := rows_outerABCData.getD (leftPosition 5 4 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 5 4 3) : (tripleIndices 4 2 4).map ((HexagonAtoms354.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_1_1
  · exact rows_outerABC_eq_0_1_2
  · exact rows_outerABC_eq_0_1_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_1_1
  · exact rows_outerABC_eq_1_1_2
  · exact rows_outerABC_eq_1_1_3
  · exact rows_outerABC_eq_2_0_0
  · exact rows_outerABC_eq_2_0_1
  · exact rows_outerABC_eq_2_0_2
  · exact rows_outerABC_eq_2_0_3
  · exact rows_outerABC_eq_2_1_0
  · exact rows_outerABC_eq_2_1_1
  · exact rows_outerABC_eq_2_1_2
  · exact rows_outerABC_eq_2_1_3
  · exact rows_outerABC_eq_3_0_0
  · exact rows_outerABC_eq_3_0_1
  · exact rows_outerABC_eq_3_0_2
  · exact rows_outerABC_eq_3_0_3
  · exact rows_outerABC_eq_3_1_0
  · exact rows_outerABC_eq_3_1_1
  · exact rows_outerABC_eq_3_1_2
  · exact rows_outerABC_eq_3_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 194396947526720,
    decodeIntegerRow 32 3 1 1383906472017920,
    decodeIntegerRow 32 3 1 1841651528049920,
    decodeIntegerRow 32 3 1 1292427196499520,
    decodeIntegerRow 32 3 1 915213795157120,
    decodeIntegerRow 32 3 1 931030335999040,
    decodeIntegerRow 32 3 1 917473055010880,
    decodeIntegerRow 32 3 1 920859792459520,
    decodeIntegerRow 32 3 1 1292427196709408,
    decodeIntegerRow 32 3 1 1841651528574840,
    decodeIntegerRow 32 3 1 469113716571560,
    decodeIntegerRow 32 3 1 1658623241745056,
    decodeIntegerRow 32 3 1 920859771195400,
    decodeIntegerRow 32 3 1 917473021001248,
    decodeIntegerRow 32 3 1 921989835841504,
    decodeIntegerRow 32 3 1 937806436206760,
    decodeIntegerRow 32 3 1 935548511333440,
    decodeIntegerRow 32 3 1 920863236190720,
    decodeIntegerRow 32 3 1 915212073291520,
    decodeIntegerRow 32 3 1 921992607837760,
    decodeIntegerRow 32 3 1 11508132177920,
    decodeIntegerRow 32 3 1 1292650350701120,
    decodeIntegerRow 32 3 1 194508524627520,
    decodeIntegerRow 32 3 1 468834774081920,
    decodeIntegerRow 32 3 1 921992590836832,
    decodeIntegerRow 32 3 1 915212030773000,
    decodeIntegerRow 32 3 1 932156973912280,
    decodeIntegerRow 32 3 1 917471643503584,
    decodeIntegerRow 32 3 1 468834773819400,
    decodeIntegerRow 32 3 1 194508524207648,
    decodeIntegerRow 32 3 1 560369837940704,
    decodeIntegerRow 32 3 1 1841512057198760]

def rows_inverseACB (r : LeftIndex 3 4 5) : List ℤ := rows_inverseACBData.getD (leftPosition 3 4 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 4 5) : (tripleIndices 4 2 4).map ((HexagonAtoms354.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 1658623241745056,
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

def rows_assocBCA (r : RightIndex 5 4 3) : List ℤ := rows_assocBCAData.getD (rightPosition 5 4 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 4 3) : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 931593910053172,
    decodeIntegerRow 32 3 1 936677384488012,
    decodeIntegerRow 32 3 1 925945991061736,
    decodeIntegerRow 32 3 1 925378817032264,
    decodeIntegerRow 32 3 1 916342459987144,
    decodeIntegerRow 32 3 1 931593737860456,
    decodeIntegerRow 32 3 1 927638272455988,
    decodeIntegerRow 32 3 1 925944441380428,
    decodeIntegerRow 32 3 1 927638253323788,
    decodeIntegerRow 32 3 1 927075709208308,
    decodeIntegerRow 32 3 1 936677730987544,
    decodeIntegerRow 32 3 1 931593742117816,
    decodeIntegerRow 32 3 1 927074159525704,
    decodeIntegerRow 32 3 1 925378836163816,
    decodeIntegerRow 32 3 1 931593914298868,
    decodeIntegerRow 32 3 1 916342802235148,
    decodeIntegerRow 32 3 1 1338299332210228,
    decodeIntegerRow 32 3 1 1750060675680052,
    decodeIntegerRow 32 3 1 880819271871416,
    decodeIntegerRow 32 3 1 834877400485736,
    decodeIntegerRow 32 3 1 1750088569955224,
    decodeIntegerRow 32 3 1 514734803779144,
    decodeIntegerRow 32 3 1 835128448962612,
    decodeIntegerRow 32 3 1 972326441218868,
    decodeIntegerRow 32 3 1 835128448726412,
    decodeIntegerRow 32 3 1 880693747160588,
    decodeIntegerRow 32 3 1 102931618922824,
    decodeIntegerRow 32 3 1 514734803831704,
    decodeIntegerRow 32 3 1 972200917452824,
    decodeIntegerRow 32 3 1 834877400249544,
    decodeIntegerRow 32 3 1 1338299332157812,
    decodeIntegerRow 32 3 1 102959513198068]

def rows_assocCAB (r : RightIndex 4 3 5) : List ℤ := rows_assocCABData.getD (rightPosition 4 3 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 4 3 5) : (tripleIndices 4 2 4).map ((HexagonAtoms354.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 933852731995336,
    decodeIntegerRow 32 3 1 928205873766616,
    decodeIntegerRow 32 3 1 923119827148588,
    decodeIntegerRow 32 3 1 918602340565612,
    decodeIntegerRow 32 3 1 928203463145704,
    decodeIntegerRow 32 3 1 919166423733256,
    decodeIntegerRow 32 3 1 918601824003988,
    decodeIntegerRow 32 3 1 929898123269548,
    decodeIntegerRow 32 3 1 934418394607576,
    decodeIntegerRow 32 3 1 929898136028344,
    decodeIntegerRow 32 3 1 928203469527532,
    decodeIntegerRow 32 3 1 933853792751572,
    decodeIntegerRow 32 3 1 929900374453624,
    decodeIntegerRow 32 3 1 918602310803944,
    decodeIntegerRow 32 3 1 933852759632212,
    decodeIntegerRow 32 3 1 924814308712468,
    decodeIntegerRow 32 3 1 285938984796904,
    decodeIntegerRow 32 3 1 652079241282056,
    decodeIntegerRow 32 3 1 789346969619988,
    decodeIntegerRow 32 3 1 331671649013548,
    decodeIntegerRow 32 3 1 651897928493256,
    decodeIntegerRow 32 3 1 1567039362642136,
    decodeIntegerRow 32 3 1 331755331839148,
    decodeIntegerRow 32 3 1 1063868479158252,
    decodeIntegerRow 32 3 1 1521264856671496,
    decodeIntegerRow 32 3 1 1063868479079576,
    decodeIntegerRow 32 3 1 651897928650668,
    decodeIntegerRow 32 3 1 285980826577132,
    decodeIntegerRow 32 3 1 1063673219153064,
    decodeIntegerRow 32 3 1 331671649354696,
    decodeIntegerRow 32 3 1 285938985164308,
    decodeIntegerRow 32 3 1 1200940947412268]

def cols_assocABC (r : LeftIndex 3 5 4) : List ℤ := cols_assocABCData.getD (leftPosition 3 5 4 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 5 4) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms354.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 933852731995336,
    decodeIntegerRow 32 3 1 928205873766616,
    decodeIntegerRow 32 3 1 923119827148588,
    decodeIntegerRow 32 3 1 918602340565612,
    decodeIntegerRow 32 3 1 928203463145704,
    decodeIntegerRow 32 3 1 919166423733256,
    decodeIntegerRow 32 3 1 918601824003988,
    decodeIntegerRow 32 3 1 929898123269548,
    decodeIntegerRow 32 3 1 934418394607576,
    decodeIntegerRow 32 3 1 929898136028344,
    decodeIntegerRow 32 3 1 928203469527532,
    decodeIntegerRow 32 3 1 933853792751572,
    decodeIntegerRow 32 3 1 929900374453624,
    decodeIntegerRow 32 3 1 918602310803944,
    decodeIntegerRow 32 3 1 933852759632212,
    decodeIntegerRow 32 3 1 924814308712468,
    decodeIntegerRow 32 3 1 285938984796904,
    decodeIntegerRow 32 3 1 652079241282056,
    decodeIntegerRow 32 3 1 789346969619988,
    decodeIntegerRow 32 3 1 331671649013548,
    decodeIntegerRow 32 3 1 651897928493256,
    decodeIntegerRow 32 3 1 1567039362642136,
    decodeIntegerRow 32 3 1 331755331839148,
    decodeIntegerRow 32 3 1 1063868479158252,
    decodeIntegerRow 32 3 1 1521264856671496,
    decodeIntegerRow 32 3 1 1063868479079576,
    decodeIntegerRow 32 3 1 651897928650668,
    decodeIntegerRow 32 3 1 285980826577132,
    decodeIntegerRow 32 3 1 1063673219153064,
    decodeIntegerRow 32 3 1 331671649354696,
    decodeIntegerRow 32 3 1 285938985164308,
    decodeIntegerRow 32 3 1 1200940947412268]

def cols_right0 (r : LeftIndex 3 5 4) : List ℤ := cols_right0Data.getD (leftPosition 3 5 4 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 5 4) : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 4) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 919167429219628,
    decodeIntegerRow 32 3 1 924814308712468,
    decodeIntegerRow 32 3 1 929900374453624,
    decodeIntegerRow 32 3 1 934417878047896,
    decodeIntegerRow 32 3 1 924816719324308,
    decodeIntegerRow 32 3 1 933853792751572,
    decodeIntegerRow 32 3 1 934418394607576,
    decodeIntegerRow 32 3 1 923122052823496,
    decodeIntegerRow 32 3 1 918601824003988,
    decodeIntegerRow 32 3 1 923122065582292,
    decodeIntegerRow 32 3 1 924816725706136,
    decodeIntegerRow 32 3 1 919166423733256,
    decodeIntegerRow 32 3 1 923119827148588,
    decodeIntegerRow 32 3 1 934417848286228,
    decodeIntegerRow 32 3 1 919167456856504,
    decodeIntegerRow 32 3 1 928205873766616,
    decodeIntegerRow 32 3 1 1567081203687532,
    decodeIntegerRow 32 3 1 1200940947412268,
    decodeIntegerRow 32 3 1 1063673219153064,
    decodeIntegerRow 32 3 1 1521348539497144,
    decodeIntegerRow 32 3 1 1201122260201172,
    decodeIntegerRow 32 3 1 285980826577132,
    decodeIntegerRow 32 3 1 1521264856671496,
    decodeIntegerRow 32 3 1 789151709772264,
    decodeIntegerRow 32 3 1 331755331839148,
    decodeIntegerRow 32 3 1 789151709693588,
    decodeIntegerRow 32 3 1 1201122260358584,
    decodeIntegerRow 32 3 1 1567039362642136,
    decodeIntegerRow 32 3 1 789346969619988,
    decodeIntegerRow 32 3 1 1521348539838292,
    decodeIntegerRow 32 3 1 1567081204054936,
    decodeIntegerRow 32 3 1 652079241282056]

def cols_left0 (r : LeftIndex 3 5 4) : List ℤ := cols_left0Data.getD (leftPosition 3 5 4 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 5 4) : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 4) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1716635155525741703434475655616,
    decodeIntegerRow 32 9 4 1716583466870761305242283502144,
    decodeIntegerRow 32 9 4 1716844462667632588991434661200,
    decodeIntegerRow 32 9 4 1716845100809983834698557392720,
    decodeIntegerRow 32 9 4 1717100353421899421030707746640,
    decodeIntegerRow 32 9 4 1716635155525860296726604688720,
    decodeIntegerRow 32 9 4 1716838719494536220783051206336,
    decodeIntegerRow 32 9 4 1716844462677238645650442080064,
    decodeIntegerRow 32 9 4 1716838719494537684897768743744,
    decodeIntegerRow 32 9 4 1716839357615275669150802881216,
    decodeIntegerRow 32 9 4 1716583466870613045551685020080,
    decodeIntegerRow 32 9 4 1716635155525860274132199254960,
    decodeIntegerRow 32 9 4 1716839357624881725809811349840,
    decodeIntegerRow 32 9 4 1716845100809982370583840695120,
    decodeIntegerRow 32 9 4 1716635155525741680840155252416,
    decodeIntegerRow 32 9 4 1717100353421751197491089934144,
    decodeIntegerRow 32 9 4 360324844950292435179959094976,
    decodeIntegerRow 32 9 4 21195579623914720118046870976,
    decodeIntegerRow 32 9 4 1733589002890462909504726085040,
    decodeIntegerRow 32 9 4 1737775854858186751050337219920,
    decodeIntegerRow 32 9 4 21195578651301483393492572080,
    decodeIntegerRow 32 9 4 3073358974564129460098246557520,
    decodeIntegerRow 32 9 4 1737775776076514576361438589376,
    decodeIntegerRow 32 9 4 1700094754376711835402004099776,
    decodeIntegerRow 32 9 4 1737775776076514576584592791104,
    decodeIntegerRow 32 9 4 1733589065915800649534787741504,
    decodeIntegerRow 32 9 4 3412488241641211001261601532240,
    decodeIntegerRow 32 9 4 3073358974564129460094802813360,
    decodeIntegerRow 32 9 4 1700094817402049574874180252080,
    decodeIntegerRow 32 9 4 1737775854858186751273491421520,
    decodeIntegerRow 32 9 4 360324844950292435183402826176,
    decodeIntegerRow 32 9 4 3412488240668597764537047222976]

def cols_right2 (r : LeftIndex 3 5 4) : List ℤ := cols_right2Data.getD (leftPosition 3 5 4 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 5 4) : (tripleIndices 4 2 4).map (fun j => (right2Middle3 5 4) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms354.outerABC * HexagonAtoms354.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms354.assocBAC * HexagonAtoms354.innerABC = HexagonAtoms354.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms354.innerRightABC * HexagonAtoms354.assocABC = HexagonAtoms354.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms354.inverseACB * right0Middle3 5 4 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms354.innerACB * right1Middle3 5 4 = right1Middle3 5 4 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms354.assocBCA * left0Middle3 5 4 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms354.innerRightBAC * left1Middle3 5 4 = left1Middle3 5 4 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms354.assocCAB * right2Middle3 5 4 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn354
