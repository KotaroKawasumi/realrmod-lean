import RMod.BrundanEllis.StackingReferenceHexagonAtoms545
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn545
open Superfusion

theorem assocBCA_alias : HexagonAtoms545.assocBCA = HexagonAtoms545.assocBAC :=
  HexagonAtoms545.assocBCA_eq.symm.trans HexagonAtoms545.assocBAC_eq

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

def rows_outerABC (r : LeftIndex 4 5 5) : List ℤ := rows_outerABCData.getD (leftPosition 4 5 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 4 5 5) : (tripleIndices 4 2 4).map ((HexagonAtoms545.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 933854452804372,
    decodeIntegerRow 32 3 1 923120684895496,
    decodeIntegerRow 32 3 1 924816027389908,
    decodeIntegerRow 32 3 1 918603172799464,
    decodeIntegerRow 32 3 1 923120678520148,
    decodeIntegerRow 32 3 1 933854482560856,
    decodeIntegerRow 32 3 1 918603200438932,
    decodeIntegerRow 32 3 1 924816040145464,
    decodeIntegerRow 32 3 1 1201052524552504,
    decodeIntegerRow 32 3 1 331615860817388,
    decodeIntegerRow 32 3 1 1566969626941016,
    decodeIntegerRow 32 3 1 1063729007821612,
    decodeIntegerRow 32 3 1 1521404328401816,
    decodeIntegerRow 32 3 1 651967664220628,
    decodeIntegerRow 32 3 1 789291181187704,
    decodeIntegerRow 32 3 1 286050562252052,
    decodeIntegerRow 32 3 1 1567150939388696,
    decodeIntegerRow 32 3 1 789207498362068,
    decodeIntegerRow 32 3 1 1201010683218424,
    decodeIntegerRow 32 3 1 1521209068475412,
    decodeIntegerRow 32 3 1 1063812690647224,
    decodeIntegerRow 32 3 1 285869249122028,
    decodeIntegerRow 32 3 1 331811120743896,
    decodeIntegerRow 32 3 1 652009505712172,
    decodeIntegerRow 32 3 1 924815007023188,
    decodeIntegerRow 32 3 1 934419226846936,
    decodeIntegerRow 32 3 1 933852071948692,
    decodeIntegerRow 32 3 1 929898993772984,
    decodeIntegerRow 32 3 1 934419254477332,
    decodeIntegerRow 32 3 1 924814994269576,
    decodeIntegerRow 32 3 1 929898987393748,
    decodeIntegerRow 32 3 1 933852042183784]

def rows_inverseACB (r : LeftIndex 5 5 4) : List ℤ := rows_inverseACBData.getD (leftPosition 5 5 4 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 5 4) : (tripleIndices 4 2 4).map ((HexagonAtoms545.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 919165707349492,
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

def rows_innerACB (r : LeftIndex 5 5 4) : List ℤ := rows_innerACBData.getD (leftPosition 5 5 4 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 5 5 4) : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_1_2
  · exact rows_innerACB_eq_0_1_3
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_0_2
  · exact rows_innerACB_eq_1_0_3
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_1_1_2
  · exact rows_innerACB_eq_1_1_3
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_0_1
  · exact rows_innerACB_eq_2_0_2
  · exact rows_innerACB_eq_2_0_3
  · exact rows_innerACB_eq_2_1_0
  · exact rows_innerACB_eq_2_1_1
  · exact rows_innerACB_eq_2_1_2
  · exact rows_innerACB_eq_2_1_3
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_0_1
  · exact rows_innerACB_eq_3_0_2
  · exact rows_innerACB_eq_3_0_3
  · exact rows_innerACB_eq_3_1_0
  · exact rows_innerACB_eq_3_1_1
  · exact rows_innerACB_eq_3_1_2
  · exact rows_innerACB_eq_3_1_3

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 926513452070914,
    decodeIntegerRow 32 3 1 926520511730206,
    decodeIntegerRow 32 3 1 926540313224146,
    decodeIntegerRow 32 3 1 926603850184014,
    decodeIntegerRow 32 3 1 728244560367382,
    decodeIntegerRow 32 3 1 1541641626482422,
    decodeIntegerRow 32 3 1 904480595540518,
    decodeIntegerRow 32 3 1 994858056662278,
    decodeIntegerRow 32 3 1 902786017967338,
    decodeIntegerRow 32 3 1 857597273234698,
    decodeIntegerRow 32 3 1 712993365358042,
    decodeIntegerRow 32 3 1 306294830725882,
    decodeIntegerRow 32 3 1 926477551104766,
    decodeIntegerRow 32 3 1 926604625024994,
    decodeIntegerRow 32 3 1 926506478500654,
    decodeIntegerRow 32 3 1 926520597823666,
    decodeIntegerRow 32 3 1 926499677117242,
    decodeIntegerRow 32 3 1 926506736782438,
    decodeIntegerRow 32 3 1 926416338667338,
    decodeIntegerRow 32 3 1 926479875627862,
    decodeIntegerRow 32 3 1 1541641623280654,
    decodeIntegerRow 32 3 1 728244559265134,
    decodeIntegerRow 32 3 1 994858027846366,
    decodeIntegerRow 32 3 1 904480585620286,
    decodeIntegerRow 32 3 1 995422887037426,
    decodeIntegerRow 32 3 1 950234180096146,
    decodeIntegerRow 32 3 1 1546725354950434,
    decodeIntegerRow 32 3 1 1140026824517314,
    decodeIntegerRow 32 3 1 926604625025478,
    decodeIntegerRow 32 3 1 926477551104922,
    decodeIntegerRow 32 3 1 926520597828022,
    decodeIntegerRow 32 3 1 926506478502058]

def rows_assocBAC (r : RightIndex 4 5 5) : List ℤ := rows_assocBACData.getD (rightPosition 4 5 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 4 5 5) : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocBAC) r) = rows_assocBAC r := by
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

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 919165707349492,
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

def rows_innerRightBAC (r : RightIndex 4 5 5) : List ℤ := rows_innerRightBACData.getD (rightPosition 4 5 5 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 4 5 5) : (tripleIndices 4 2 4).map ((HexagonAtoms545.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_1_2
  · exact rows_innerRightBAC_eq_0_1_3
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_0_2
  · exact rows_innerRightBAC_eq_1_0_3
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_1_1_2
  · exact rows_innerRightBAC_eq_1_1_3
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_0_1
  · exact rows_innerRightBAC_eq_2_0_2
  · exact rows_innerRightBAC_eq_2_0_3
  · exact rows_innerRightBAC_eq_2_1_0
  · exact rows_innerRightBAC_eq_2_1_1
  · exact rows_innerRightBAC_eq_2_1_2
  · exact rows_innerRightBAC_eq_2_1_3
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_0_1
  · exact rows_innerRightBAC_eq_3_0_2
  · exact rows_innerRightBAC_eq_3_0_3
  · exact rows_innerRightBAC_eq_3_1_0
  · exact rows_innerRightBAC_eq_3_1_1
  · exact rows_innerRightBAC_eq_3_1_2
  · exact rows_innerRightBAC_eq_3_1_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 926488069463848,
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

def rows_assocCAB (r : RightIndex 5 5 4) : List ℤ := rows_assocCABData.getD (rightPosition 5 5 4 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 5 4) : (tripleIndices 4 2 4).map ((HexagonAtoms545.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 1201032723137296,
    decodeIntegerRow 32 3 1 331712973853060,
    decodeIntegerRow 32 3 1 1567060024712944,
    decodeIntegerRow 32 3 1 1063769643766660,
    decodeIntegerRow 32 3 1 928302307985300,
    decodeIntegerRow 32 3 1 918581132880592,
    decodeIntegerRow 32 3 1 919208782770580,
    decodeIntegerRow 32 3 1 923211599571248,
    decodeIntegerRow 32 3 1 919208753009872,
    decodeIntegerRow 32 3 1 929808595657940,
    decodeIntegerRow 32 3 1 928302295230768,
    decodeIntegerRow 32 3 1 934439028336340,
    decodeIntegerRow 32 3 1 285960163795780,
    decodeIntegerRow 32 3 1 1063769643928336,
    decodeIntegerRow 32 3 1 651987465788740,
    decodeIntegerRow 32 3 1 331712974219504,
    decodeIntegerRow 32 3 1 923030286782340,
    decodeIntegerRow 32 3 1 933895088906896,
    decodeIntegerRow 32 3 1 918622974293380,
    decodeIntegerRow 32 3 1 924913140792944,
    decodeIntegerRow 32 3 1 789248134464592,
    decodeIntegerRow 32 3 1 1567060541275540,
    decodeIntegerRow 32 3 1 1521306181878448,
    decodeIntegerRow 32 3 1 1201030484712340,
    decodeIntegerRow 32 3 1 331714007341780,
    decodeIntegerRow 32 3 1 1201030484629072,
    decodeIntegerRow 32 3 1 1063772054540500,
    decodeIntegerRow 32 3 1 1567060541614768,
    decodeIntegerRow 32 3 1 918623001928336,
    decodeIntegerRow 32 3 1 928107035304260,
    decodeIntegerRow 32 3 1 923030280405104,
    decodeIntegerRow 32 3 1 919125070184260]

def cols_assocABC (r : LeftIndex 5 4 5) : List ℤ := cols_assocABCData.getD (leftPosition 5 4 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 4 5) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms545.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1201032723137296,
    decodeIntegerRow 32 3 1 331712973853060,
    decodeIntegerRow 32 3 1 1567060024712944,
    decodeIntegerRow 32 3 1 1063769643766660,
    decodeIntegerRow 32 3 1 928302307985300,
    decodeIntegerRow 32 3 1 918581132880592,
    decodeIntegerRow 32 3 1 919208782770580,
    decodeIntegerRow 32 3 1 923211599571248,
    decodeIntegerRow 32 3 1 919208753009872,
    decodeIntegerRow 32 3 1 929808595657940,
    decodeIntegerRow 32 3 1 928302295230768,
    decodeIntegerRow 32 3 1 934439028336340,
    decodeIntegerRow 32 3 1 285960163795780,
    decodeIntegerRow 32 3 1 1063769643928336,
    decodeIntegerRow 32 3 1 651987465788740,
    decodeIntegerRow 32 3 1 331712974219504,
    decodeIntegerRow 32 3 1 923030286782340,
    decodeIntegerRow 32 3 1 933895088906896,
    decodeIntegerRow 32 3 1 918622974293380,
    decodeIntegerRow 32 3 1 924913140792944,
    decodeIntegerRow 32 3 1 789248134464592,
    decodeIntegerRow 32 3 1 1567060541275540,
    decodeIntegerRow 32 3 1 1521306181878448,
    decodeIntegerRow 32 3 1 1201030484712340,
    decodeIntegerRow 32 3 1 331714007341780,
    decodeIntegerRow 32 3 1 1201030484629072,
    decodeIntegerRow 32 3 1 1063772054540500,
    decodeIntegerRow 32 3 1 1567060541614768,
    decodeIntegerRow 32 3 1 918623001928336,
    decodeIntegerRow 32 3 1 928107035304260,
    decodeIntegerRow 32 3 1 923030280405104,
    decodeIntegerRow 32 3 1 919125070184260]

def cols_right0 (r : LeftIndex 5 4 5) : List ℤ := cols_right0Data.getD (leftPosition 5 4 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 4 5) : (tripleIndices 4 2 4).map (fun j => (right0Middle5 4 5) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1718935300678966052851503276808,
    decodeIntegerRow 32 9 4 1735682424929837813668200844792,
    decodeIntegerRow 32 9 4 1886406543247127644902329306248,
    decodeIntegerRow 32 9 4 3242923608053972768609555653752,
    decodeIntegerRow 32 9 4 1698001395351867857248264307128,
    decodeIntegerRow 32 9 4 1714748519614747188888721811272,
    decodeIntegerRow 32 9 4 190760212238406298594696102968,
    decodeIntegerRow 32 9 4 1547277277045399663917030597832,
    decodeIntegerRow 32 9 4 1716816065867329997346432056248,
    decodeIntegerRow 32 9 4 1717074509531944359107682653512,
    decodeIntegerRow 32 9 4 1716841595019567543571761208888,
    decodeIntegerRow 32 9 4 1716844817189959488349454070472,
    decodeIntegerRow 32 9 4 1716609311635920038602265256952,
    decodeIntegerRow 32 9 4 1716867754522443810983871991048,
    decodeIntegerRow 32 9 4 1716839074006057953528399534712,
    decodeIntegerRow 32 9 4 1716842233151112158554939479688,
    decodeIntegerRow 32 9 4 1547277277045383192626463025912,
    decodeIntegerRow 32 9 4 3242923608053972951623895293448,
    decodeIntegerRow 32 9 4 1714748519613546411471419191672,
    decodeIntegerRow 32 9 4 1735682424929837815927637137288,
    decodeIntegerRow 32 9 4 3242923608054106369077492625992,
    decodeIntegerRow 32 9 4 1547277277045398016787973840568,
    decodeIntegerRow 32 9 4 1735682424940644629669021073352,
    decodeIntegerRow 32 9 4 1714748519614747168553795178808,
    decodeIntegerRow 32 9 4 1716841595019567543574898836552,
    decodeIntegerRow 32 9 4 1716839003102552996308735141048,
    decodeIntegerRow 32 9 4 1716816065867329997597481005512,
    decodeIntegerRow 32 9 4 1716609310760568125578060658488,
    decodeIntegerRow 32 9 4 1716839074006057953528748160008,
    decodeIntegerRow 32 9 4 1716841587141400326105970709752,
    decodeIntegerRow 32 9 4 1716609311635920038630159584648,
    decodeIntegerRow 32 9 4 1716816065770068673925025102712]

def cols_right1 (r : LeftIndex 5 4 5) : List ℤ := cols_right1Data.getD (leftPosition 5 4 5 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 5 4 5) : (tripleIndices 4 2 4).map (fun j => (right1Middle5 4 5) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_1_2
  · exact cols_right1_eq_0_1_3
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_1_1
  · exact cols_right1_eq_1_1_2
  · exact cols_right1_eq_1_1_3
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_0_2
  · exact cols_right1_eq_2_0_3
  · exact cols_right1_eq_2_1_0
  · exact cols_right1_eq_2_1_1
  · exact cols_right1_eq_2_1_2
  · exact cols_right1_eq_2_1_3
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_0_2
  · exact cols_right1_eq_3_0_3
  · exact cols_right1_eq_3_1_0
  · exact cols_right1_eq_3_1_1
  · exact cols_right1_eq_3_1_2
  · exact cols_right1_eq_3_1_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 651987465788740,
    decodeIntegerRow 32 3 1 1521307214632336,
    decodeIntegerRow 32 3 1 285960163795780,
    decodeIntegerRow 32 3 1 789250544923504,
    decodeIntegerRow 32 3 1 924717893621072,
    decodeIntegerRow 32 3 1 934439028336340,
    decodeIntegerRow 32 3 1 933811435841968,
    decodeIntegerRow 32 3 1 929808595657940,
    decodeIntegerRow 32 3 1 933811406081260,
    decodeIntegerRow 32 3 1 923211599571248,
    decodeIntegerRow 32 3 1 924717880866540,
    decodeIntegerRow 32 3 1 918581132880592,
    decodeIntegerRow 32 3 1 1567060024712944,
    decodeIntegerRow 32 3 1 789250545085180,
    decodeIntegerRow 32 3 1 1201032723137296,
    decodeIntegerRow 32 3 1 1521307214998780,
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

def cols_left0 (r : LeftIndex 5 4 5) : List ℤ := cols_left0Data.getD (leftPosition 5 4 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 4 5) : (tripleIndices 4 2 4).map (fun j => (left0Middle5 4 5) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 32 3 1 903632916144766,
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

def cols_left1 (r : LeftIndex 5 4 5) : List ℤ := cols_left1Data.getD (leftPosition 5 4 5 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 5 4 5) : (tripleIndices 4 2 4).map (fun j => (left1Middle5 4 5) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_1_2
  · exact cols_left1_eq_0_1_3
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_1_1
  · exact cols_left1_eq_1_1_2
  · exact cols_left1_eq_1_1_3
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_0_2
  · exact cols_left1_eq_2_0_3
  · exact cols_left1_eq_2_1_0
  · exact cols_left1_eq_2_1_1
  · exact cols_left1_eq_2_1_2
  · exact cols_left1_eq_2_1_3
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_0_2
  · exact cols_left1_eq_3_0_3
  · exact cols_left1_eq_3_1_0
  · exact cols_left1_eq_3_1_1
  · exact cols_left1_eq_3_1_2
  · exact cols_left1_eq_3_1_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 17 8 1183955797389079302630210150207854756832,
    decodeIntegerRow 32 17 8 1183955797220460438742594126134906205152,
    decodeIntegerRow 32 17 8 1183955797220525479678250083901361520608,
    decodeIntegerRow 32 17 8 1183955797370282471446910136296273899488,
    decodeIntegerRow 32 17 8 69872006049549229433315353868416799744,
    decodeIntegerRow 32 17 8 1253345927357439034672021106062027726336,
    decodeIntegerRow 32 17 8 1245634435634909761064348991147959038976,
    decodeIntegerRow 32 17 8 2298493113860509302050556562136885476864,
    decodeIntegerRow 32 17 8 1183955797370282471492699613523131659232,
    decodeIntegerRow 32 17 8 1183955797539941766163003146484159775712,
    decodeIntegerRow 32 17 8 1183955797220460438740058005919753482208,
    decodeIntegerRow 32 17 8 1183955797371387943168088022179835330528,
    decodeIntegerRow 32 17 8 2298493113860509302050556562137248881664,
    decodeIntegerRow 32 17 8 1122277159125557484779757306166425458176,
    decodeIntegerRow 32 17 8 1253345927357439034672021106055463648256,
    decodeIntegerRow 32 17 8 2298039588710918016410790943452125607424,
    decodeIntegerRow 32 17 8 69416818959263187453664600587544862688,
    decodeIntegerRow 32 17 8 1245661113584885719043158733430098567712,
    decodeIntegerRow 32 17 8 1114538978590694771125694500397783081952,
    decodeIntegerRow 32 17 8 69870528768931668242306345338908007968,
    decodeIntegerRow 32 17 8 1183955797390180948413856681724448521216,
    decodeIntegerRow 32 17 8 1183955797220525691454609645277050059776,
    decodeIntegerRow 32 17 8 1183955797540006568858852319897480879104,
    decodeIntegerRow 32 17 8 1183955797389075478295626348577279826944,
    decodeIntegerRow 32 17 8 69870528768931668242306345338499010528,
    decodeIntegerRow 32 17 8 1253372616169772474718411796929732252192,
    decodeIntegerRow 32 17 8 1245661113584885719043158733423531807712,
    decodeIntegerRow 32 17 8 2298494775801204058390441696733042822688,
    decodeIntegerRow 32 17 8 1183955797389075478249818291950635529216,
    decodeIntegerRow 32 17 8 1183955797220460676987789001161165485056,
    decodeIntegerRow 32 17 8 1183955797220525691451757675265526191104,
    decodeIntegerRow 32 17 8 1183955797370286297384460199086637732864]

def cols_right2 (r : LeftIndex 5 4 5) : List ℤ := cols_right2Data.getD (leftPosition 5 4 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 4 5) : (tripleIndices 4 2 4).map (fun j => (right2Middle5 4 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms545.outerABC * HexagonAtoms545.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms545.assocBAC * HexagonAtoms545.innerABC = HexagonAtoms545.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms545.innerRightABC * HexagonAtoms545.assocABC = HexagonAtoms545.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms545.inverseACB * right0Middle5 4 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms545.innerACB * right1Middle5 4 5 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms545.assocBAC * left0Middle5 4 5 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms545.innerRightBAC * left1Middle5 4 5 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms545.assocCAB * right2Middle5 4 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn545
