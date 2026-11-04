import RMod.BrundanEllis.StackingReferenceHexagonAtoms325
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn325
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

def rows_outerABC (r : LeftIndex 2 5 3) : List ℤ := rows_outerABCData.getD (leftPosition 2 5 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 2 5 3) : (tripleIndices 4 2 4).map ((HexagonAtoms325.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 335200020088964,
    decodeIntegerRow 32 3 1 781384259565772,
    decodeIntegerRow 32 3 1 1208396883005476,
    decodeIntegerRow 32 3 1 1565455852328108,
    decodeIntegerRow 32 3 1 284174161720212,
    decodeIntegerRow 32 3 1 659312022594844,
    decodeIntegerRow 32 3 1 797198102809612,
    decodeIntegerRow 32 3 1 328422221398724,
    decodeIntegerRow 32 3 1 328422227406708,
    decodeIntegerRow 32 3 1 797198075021764,
    decodeIntegerRow 32 3 1 1193708136413332,
    decodeIntegerRow 32 3 1 1568846039545956,
    decodeIntegerRow 32 3 1 1565455839231324,
    decodeIntegerRow 32 3 1 1208396912691628,
    decodeIntegerRow 32 3 1 1071635901813124,
    decodeIntegerRow 32 3 1 1517820175505588,
    decodeIntegerRow 32 3 1 659351483230708,
    decodeIntegerRow 32 3 1 1568663693634884,
    decodeIntegerRow 32 3 1 328226450921492,
    decodeIntegerRow 32 3 1 1055903558230756,
    decodeIntegerRow 32 3 1 781298365788124,
    decodeIntegerRow 32 3 1 1518014918873388,
    decodeIntegerRow 32 3 1 1565275559564804,
    decodeIntegerRow 32 3 1 644667528193588,
    decodeIntegerRow 32 3 1 644667557871364,
    decodeIntegerRow 32 3 1 1565275572659532,
    decodeIntegerRow 32 3 1 335005276725156,
    decodeIntegerRow 32 3 1 1071721850545708,
    decodeIntegerRow 32 3 1 1055903530433812,
    decodeIntegerRow 32 3 1 328226444909724,
    decodeIntegerRow 32 3 1 284356507629452,
    decodeIntegerRow 32 3 1 1193668735456324]

def rows_inverseACB (r : LeftIndex 3 5 2) : List ℤ := rows_inverseACBData.getD (leftPosition 3 5 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 5 2) : (tripleIndices 4 2 4).map ((HexagonAtoms325.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_4_0_0
  · exact rows_inverseACB_eq_4_0_1
  · exact rows_inverseACB_eq_4_0_2
  · exact rows_inverseACB_eq_4_0_3
  · exact rows_inverseACB_eq_5_0_0
  · exact rows_inverseACB_eq_5_0_1
  · exact rows_inverseACB_eq_5_0_2
  · exact rows_inverseACB_eq_5_0_3
  · exact rows_inverseACB_eq_6_0_0
  · exact rows_inverseACB_eq_6_0_1
  · exact rows_inverseACB_eq_6_0_2
  · exact rows_inverseACB_eq_6_0_3
  · exact rows_inverseACB_eq_7_0_0
  · exact rows_inverseACB_eq_7_0_1
  · exact rows_inverseACB_eq_7_0_2
  · exact rows_inverseACB_eq_7_0_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 1517820175505588,
    decodeIntegerRow 32 3 1 1071635901813124,
    decodeIntegerRow 32 3 1 644623276160212,
    decodeIntegerRow 32 3 1 287564349620516,
    decodeIntegerRow 32 3 1 1568846039545956,
    decodeIntegerRow 32 3 1 1193708136413332,
    decodeIntegerRow 32 3 1 1055822113830076,
    decodeIntegerRow 32 3 1 1524597961445132,
    decodeIntegerRow 32 3 1 1524597967453116,
    decodeIntegerRow 32 3 1 1055822086042228,
    decodeIntegerRow 32 3 1 659312022594844,
    decodeIntegerRow 32 3 1 284174161720212,
    decodeIntegerRow 32 3 1 287564336523732,
    decodeIntegerRow 32 3 1 644623305846364,
    decodeIntegerRow 32 3 1 781384259565772,
    decodeIntegerRow 32 3 1 335200020088964,
    decodeIntegerRow 32 3 1 1193668735456324,
    decodeIntegerRow 32 3 1 284356507629452,
    decodeIntegerRow 32 3 1 1524793743942116,
    decodeIntegerRow 32 3 1 797116658418028,
    decodeIntegerRow 32 3 1 1071721850545708,
    decodeIntegerRow 32 3 1 335005276725156,
    decodeIntegerRow 32 3 1 287744616192308,
    decodeIntegerRow 32 3 1 1208352630980476,
    decodeIntegerRow 32 3 1 1208352660658252,
    decodeIntegerRow 32 3 1 287744629287036,
    decodeIntegerRow 32 3 1 1518014918873388,
    decodeIntegerRow 32 3 1 781298365788124,
    decodeIntegerRow 32 3 1 797116630621084,
    decodeIntegerRow 32 3 1 1524793737930348,
    decodeIntegerRow 32 3 1 1568663693634884,
    decodeIntegerRow 32 3 1 659351483230708]

def rows_assocBCA (r : RightIndex 2 5 3) : List ℤ := rows_assocBCAData.getD (rightPosition 2 5 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 2 5 3) : (tripleIndices 4 2 4).map ((HexagonAtoms325.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_4_0_0
  · exact rows_assocBCA_eq_4_0_1
  · exact rows_assocBCA_eq_4_0_2
  · exact rows_assocBCA_eq_4_0_3
  · exact rows_assocBCA_eq_5_0_0
  · exact rows_assocBCA_eq_5_0_1
  · exact rows_assocBCA_eq_5_0_2
  · exact rows_assocBCA_eq_5_0_3
  · exact rows_assocBCA_eq_6_0_0
  · exact rows_assocBCA_eq_6_0_1
  · exact rows_assocBCA_eq_6_0_2
  · exact rows_assocBCA_eq_6_0_3
  · exact rows_assocBCA_eq_7_0_0
  · exact rows_assocBCA_eq_7_0_1
  · exact rows_assocBCA_eq_7_0_2
  · exact rows_assocBCA_eq_7_0_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 719771659379482,
    decodeIntegerRow 32 3 1 1544465915483062,
    decodeIntegerRow 32 3 1 941761291049266,
    decodeIntegerRow 32 3 1 860421583597954,
    decodeIntegerRow 32 3 1 926520942199666,
    decodeIntegerRow 32 3 1 926505445380286,
    decodeIntegerRow 32 3 1 926604194558758,
    decodeIntegerRow 32 3 1 926478842508662,
    decodeIntegerRow 32 3 1 926505445379818,
    decodeIntegerRow 32 3 1 926499246652282,
    decodeIntegerRow 32 3 1 926478842504286,
    decodeIntegerRow 32 3 1 926415994294546,
    decodeIntegerRow 32 3 1 308554263842206,
    decodeIntegerRow 32 3 1 719771688064174,
    decodeIntegerRow 32 3 1 992598606671062,
    decodeIntegerRow 32 3 1 941761287742522,
    decodeIntegerRow 32 3 1 896007706021246,
    decodeIntegerRow 32 3 1 855337850878414,
    decodeIntegerRow 32 3 1 721466265296182,
    decodeIntegerRow 32 3 1 309119122875802,
    decodeIntegerRow 32 3 1 926415908201098,
    decodeIntegerRow 32 3 1 926478584223962,
    decodeIntegerRow 32 3 1 926520167358526,
    decodeIntegerRow 32 3 1 926512418949106,
    decodeIntegerRow 32 3 1 926541604623506,
    decodeIntegerRow 32 3 1 926415908199646,
    decodeIntegerRow 32 3 1 926507769903238,
    decodeIntegerRow 32 3 1 926520167358742,
    decodeIntegerRow 32 3 1 855337851587002,
    decodeIntegerRow 32 3 1 957012485901142,
    decodeIntegerRow 32 3 1 309119132481106,
    decodeIntegerRow 32 3 1 1131553952266594]

def rows_assocCAB (r : RightIndex 5 3 2) : List ℤ := rows_assocCABData.getD (rightPosition 5 3 2 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_2 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_3 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_2 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_3 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_2 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_3 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_2 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_3 : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 3 2) : (tripleIndices 8 1 4).map ((HexagonAtoms325.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_0_2_0
  · exact rows_assocCAB_eq_0_2_1
  · exact rows_assocCAB_eq_0_2_2
  · exact rows_assocCAB_eq_0_2_3
  · exact rows_assocCAB_eq_0_3_0
  · exact rows_assocCAB_eq_0_3_1
  · exact rows_assocCAB_eq_0_3_2
  · exact rows_assocCAB_eq_0_3_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_1_2_0
  · exact rows_assocCAB_eq_1_2_1
  · exact rows_assocCAB_eq_1_2_2
  · exact rows_assocCAB_eq_1_2_3
  · exact rows_assocCAB_eq_1_3_0
  · exact rows_assocCAB_eq_1_3_1
  · exact rows_assocCAB_eq_1_3_2
  · exact rows_assocCAB_eq_1_3_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 720629422684474,
    decodeIntegerRow 32 3 1 1544180003925466,
    decodeIntegerRow 32 3 1 949481030059708,
    decodeIntegerRow 32 3 1 857848336001428,
    decodeIntegerRow 32 3 1 918884539987654,
    decodeIntegerRow 32 3 1 923968357737754,
    decodeIntegerRow 32 3 1 927357770455852,
    decodeIntegerRow 32 3 1 926793686223868,
    decodeIntegerRow 32 3 1 926510092832326,
    decodeIntegerRow 32 3 1 926510094955174,
    decodeIntegerRow 32 3 1 926510080076932,
    decodeIntegerRow 32 3 1 926510099209132,
    decodeIntegerRow 32 3 1 926510094432454,
    decodeIntegerRow 32 3 1 926510094445594,
    decodeIntegerRow 32 3 1 926510094484972,
    decodeIntegerRow 32 3 1 926510094603068,
    decodeIntegerRow 32 3 1 949292743702054,
    decodeIntegerRow 32 3 1 995109090731194,
    decodeIntegerRow 32 3 1 1132411686873772,
    decodeIntegerRow 32 3 1 1544186977494268,
    decodeIntegerRow 32 3 1 927356995614874,
    decodeIntegerRow 32 3 1 926228827150906,
    decodeIntegerRow 32 3 1 934135734957628,
    decodeIntegerRow 32 3 1 923968099457428,
    decodeIntegerRow 32 3 1 926510080077094,
    decodeIntegerRow 32 3 1 926510089643194,
    decodeIntegerRow 32 3 1 926510096020972,
    decodeIntegerRow 32 3 1 926510094959548,
    decodeIntegerRow 32 3 1 926510094484966,
    decodeIntegerRow 32 3 1 926510094248774,
    decodeIntegerRow 32 3 1 926510094419332,
    decodeIntegerRow 32 3 1 926510094445612]

def cols_assocABC (r : LeftIndex 3 2 5) : List ℤ := cols_assocABCData.getD (leftPosition 3 2 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 2 5) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms325.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_0_2_0
  · exact cols_assocABC_eq_0_2_1
  · exact cols_assocABC_eq_0_2_2
  · exact cols_assocABC_eq_0_2_3
  · exact cols_assocABC_eq_0_3_0
  · exact cols_assocABC_eq_0_3_1
  · exact cols_assocABC_eq_0_3_2
  · exact cols_assocABC_eq_0_3_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3
  · exact cols_assocABC_eq_1_2_0
  · exact cols_assocABC_eq_1_2_1
  · exact cols_assocABC_eq_1_2_2
  · exact cols_assocABC_eq_1_2_3
  · exact cols_assocABC_eq_1_3_0
  · exact cols_assocABC_eq_1_3_1
  · exact cols_assocABC_eq_1_3_2
  · exact cols_assocABC_eq_1_3_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 720629422684474,
    decodeIntegerRow 32 3 1 1544180003925466,
    decodeIntegerRow 32 3 1 949481030059708,
    decodeIntegerRow 32 3 1 857848336001428,
    decodeIntegerRow 32 3 1 918884539987654,
    decodeIntegerRow 32 3 1 923968357737754,
    decodeIntegerRow 32 3 1 927357770455852,
    decodeIntegerRow 32 3 1 926793686223868,
    decodeIntegerRow 32 3 1 926510092832326,
    decodeIntegerRow 32 3 1 926510094955174,
    decodeIntegerRow 32 3 1 926510080076932,
    decodeIntegerRow 32 3 1 926510099209132,
    decodeIntegerRow 32 3 1 926510094432454,
    decodeIntegerRow 32 3 1 926510094445594,
    decodeIntegerRow 32 3 1 926510094484972,
    decodeIntegerRow 32 3 1 926510094603068,
    decodeIntegerRow 32 3 1 949292743702054,
    decodeIntegerRow 32 3 1 995109090731194,
    decodeIntegerRow 32 3 1 1132411686873772,
    decodeIntegerRow 32 3 1 1544186977494268,
    decodeIntegerRow 32 3 1 927356995614874,
    decodeIntegerRow 32 3 1 926228827150906,
    decodeIntegerRow 32 3 1 934135734957628,
    decodeIntegerRow 32 3 1 923968099457428,
    decodeIntegerRow 32 3 1 926510080077094,
    decodeIntegerRow 32 3 1 926510089643194,
    decodeIntegerRow 32 3 1 926510096020972,
    decodeIntegerRow 32 3 1 926510094959548,
    decodeIntegerRow 32 3 1 926510094484966,
    decodeIntegerRow 32 3 1 926510094248774,
    decodeIntegerRow 32 3 1 926510094419332,
    decodeIntegerRow 32 3 1 926510094445612]

def cols_right0 (r : LeftIndex 3 2 5) : List ℤ := cols_right0Data.getD (leftPosition 3 2 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 2 5) : (tripleIndices 4 2 4).map (fun j => (right0Middle3 2 5) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_0_2_0
  · exact cols_right0_eq_0_2_1
  · exact cols_right0_eq_0_2_2
  · exact cols_right0_eq_0_2_3
  · exact cols_right0_eq_0_3_0
  · exact cols_right0_eq_0_3_1
  · exact cols_right0_eq_0_3_2
  · exact cols_right0_eq_0_3_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_1_2_0
  · exact cols_right0_eq_1_2_1
  · exact cols_right0_eq_1_2_2
  · exact cols_right0_eq_1_2_3
  · exact cols_right0_eq_1_3_0
  · exact cols_right0_eq_1_3_1
  · exact cols_right0_eq_1_3_2
  · exact cols_right0_eq_1_3_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1132390766167366,
    decodeIntegerRow 32 3 1 308840184926374,
    decodeIntegerRow 32 3 1 903539158792132,
    decodeIntegerRow 32 3 1 995171852850412,
    decodeIntegerRow 32 3 1 934135648864186,
    decodeIntegerRow 32 3 1 929051831114086,
    decodeIntegerRow 32 3 1 925662418395988,
    decodeIntegerRow 32 3 1 926226502627972,
    decodeIntegerRow 32 3 1 926510092832326,
    decodeIntegerRow 32 3 1 926510094955174,
    decodeIntegerRow 32 3 1 926510080076932,
    decodeIntegerRow 32 3 1 926510099209132,
    decodeIntegerRow 32 3 1 926510094432454,
    decodeIntegerRow 32 3 1 926510094445594,
    decodeIntegerRow 32 3 1 926510094484972,
    decodeIntegerRow 32 3 1 926510094603068,
    decodeIntegerRow 32 3 1 903727445149786,
    decodeIntegerRow 32 3 1 857911098120646,
    decodeIntegerRow 32 3 1 720608501978068,
    decodeIntegerRow 32 3 1 308833211357572,
    decodeIntegerRow 32 3 1 925663193236966,
    decodeIntegerRow 32 3 1 926791361700934,
    decodeIntegerRow 32 3 1 918884453894212,
    decodeIntegerRow 32 3 1 929052089394412,
    decodeIntegerRow 32 3 1 926510080077094,
    decodeIntegerRow 32 3 1 926510089643194,
    decodeIntegerRow 32 3 1 926510096020972,
    decodeIntegerRow 32 3 1 926510094959548,
    decodeIntegerRow 32 3 1 926510094484966,
    decodeIntegerRow 32 3 1 926510094248774,
    decodeIntegerRow 32 3 1 926510094419332,
    decodeIntegerRow 32 3 1 926510094445612]

def cols_left0 (r : LeftIndex 3 2 5) : List ℤ := cols_left0Data.getD (leftPosition 3 2 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 2 5) : (tripleIndices 4 2 4).map (fun j => (left0Middle3 2 5) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_0_2_0
  · exact cols_left0_eq_0_2_1
  · exact cols_left0_eq_0_2_2
  · exact cols_left0_eq_0_2_3
  · exact cols_left0_eq_0_3_0
  · exact cols_left0_eq_0_3_1
  · exact cols_left0_eq_0_3_2
  · exact cols_left0_eq_0_3_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_1_2_0
  · exact cols_left0_eq_1_2_1
  · exact cols_left0_eq_1_2_2
  · exact cols_left0_eq_1_2_3
  · exact cols_left0_eq_1_3_0
  · exact cols_left0_eq_1_3_1
  · exact cols_left0_eq_1_3_2
  · exact cols_left0_eq_1_3_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 11641532182678817420272,
    decodeIntegerRow 32 5 2 11641532182755101600560,
    decodeIntegerRow 32 5 2 11641532182633033163064,
    decodeIntegerRow 32 5 2 11641532182703223607752,
    decodeIntegerRow 32 5 2 21014505853347778320312,
    decodeIntegerRow 32 5 2 13874327904129028320312,
    decodeIntegerRow 32 5 2 13135228386306762695312,
    decodeIntegerRow 32 5 2 20895296106033325195312,
    decodeIntegerRow 32 5 2 9408747917556762695312,
    decodeIntegerRow 32 5 2 21014457712478637695312,
    decodeIntegerRow 32 5 2 2387815484695434570312,
    decodeIntegerRow 32 5 2 13135220775222778320312,
    decodeIntegerRow 32 5 2 11641532182755101915064,
    decodeIntegerRow 32 5 2 11641532182708145545272,
    decodeIntegerRow 32 5 2 11641532182703223657872,
    decodeIntegerRow 32 5 2 11641532182753930038064,
    decodeIntegerRow 32 5 2 10154996165847778320312,
    decodeIntegerRow 32 5 2 20865208062820434570312,
    decodeIntegerRow 32 5 2 21044021691970825195312,
    decodeIntegerRow 32 5 2 9403979533767700195312,
    decodeIntegerRow 32 5 2 11641532182632835978064,
    decodeIntegerRow 32 5 2 11641532182683692357872,
    decodeIntegerRow 32 5 2 11641532182708114295352,
    decodeIntegerRow 32 5 2 11641532182754908165560,
    decodeIntegerRow 32 5 2 11641532182703270482872,
    decodeIntegerRow 32 5 2 11641532182632836287560,
    decodeIntegerRow 32 5 2 11641532182632055040560,
    decodeIntegerRow 32 5 2 11641532182708114220272,
    decodeIntegerRow 32 5 2 20865255441970825195312,
    decodeIntegerRow 32 5 2 13128075847244262695312,
    decodeIntegerRow 32 5 2 9403968101882934570312,
    decodeIntegerRow 32 5 2 2238994683914184570312]

def cols_right2 (r : LeftIndex 3 2 5) : List ℤ := cols_right2Data.getD (leftPosition 3 2 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 2 5) : (tripleIndices 8 1 4).map (fun j => (right2Middle3 2 5) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_0_2_0
  · exact cols_right2_eq_0_2_1
  · exact cols_right2_eq_0_2_2
  · exact cols_right2_eq_0_2_3
  · exact cols_right2_eq_0_3_0
  · exact cols_right2_eq_0_3_1
  · exact cols_right2_eq_0_3_2
  · exact cols_right2_eq_0_3_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_1_2_0
  · exact cols_right2_eq_1_2_1
  · exact cols_right2_eq_1_2_2
  · exact cols_right2_eq_1_2_3
  · exact cols_right2_eq_1_3_0
  · exact cols_right2_eq_1_3_1
  · exact cols_right2_eq_1_3_2
  · exact cols_right2_eq_1_3_3

theorem product0_eq : HexagonAtoms325.outerABC * HexagonAtoms325.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms325.assocBAC * HexagonAtoms325.innerABC = HexagonAtoms325.assocBAC :=
  Matrix.mul_one (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product2_eq : HexagonAtoms325.innerRightABC * HexagonAtoms325.assocABC = HexagonAtoms325.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product3_eq : HexagonAtoms325.inverseACB * right0Middle3 2 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms325.innerACB * right1Middle3 2 5 = right1Middle3 2 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product5_eq : HexagonAtoms325.assocBCA * left0Middle3 2 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms325.innerRightBAC * left1Middle3 2 5 = left1Middle3 2 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product7_eq : HexagonAtoms325.assocCAB * right2Middle3 2 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn325
