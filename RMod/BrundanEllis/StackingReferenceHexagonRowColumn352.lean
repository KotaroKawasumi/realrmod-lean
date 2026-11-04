import RMod.BrundanEllis.StackingReferenceHexagonAtoms352
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn352
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

def rows_outerABC (r : LeftIndex 5 2 3) : List ℤ := rows_outerABCData.getD (leftPosition 5 2 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 5 2 3) : (tripleIndices 4 2 4).map ((HexagonAtoms352.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 720629422684474,
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

def rows_inverseACB (r : LeftIndex 3 2 5) : List ℤ := rows_inverseACBData.getD (leftPosition 3 2 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 2 5) : (tripleIndices 4 2 4).map ((HexagonAtoms352.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_2_1
  · exact rows_inverseACB_eq_0_2_2
  · exact rows_inverseACB_eq_0_2_3
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_3_1
  · exact rows_inverseACB_eq_0_3_2
  · exact rows_inverseACB_eq_0_3_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_2_1
  · exact rows_inverseACB_eq_1_2_2
  · exact rows_inverseACB_eq_1_2_3
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_1_3_1
  · exact rows_inverseACB_eq_1_3_2
  · exact rows_inverseACB_eq_1_3_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 333505187778884,
    decodeIntegerRow 32 3 1 781949203669132,
    decodeIntegerRow 32 3 1 1193143392214756,
    decodeIntegerRow 32 3 1 1570540349258348,
    decodeIntegerRow 32 3 1 282479833555484,
    decodeIntegerRow 32 3 1 659876824355308,
    decodeIntegerRow 32 3 1 781949233268164,
    decodeIntegerRow 32 3 1 333505174657908,
    decodeIntegerRow 32 3 1 1208961684608428,
    decodeIntegerRow 32 3 1 289258665370916,
    decodeIntegerRow 32 3 1 1522903122756788,
    decodeIntegerRow 32 3 1 796633128792316,
    decodeIntegerRow 32 3 1 796633158706252,
    decodeIntegerRow 32 3 1 1522903135143036,
    decodeIntegerRow 32 3 1 1563761530201388,
    decodeIntegerRow 32 3 1 644058531804124,
    decodeIntegerRow 32 3 1 796551856578844,
    decodeIntegerRow 32 3 1 1523099415803628,
    decodeIntegerRow 32 3 1 1563580727254724,
    decodeIntegerRow 32 3 1 644102584090228,
    decodeIntegerRow 32 3 1 1208917577209924,
    decodeIntegerRow 32 3 1 289439454880652,
    decodeIntegerRow 32 3 1 1523099428191716,
    decodeIntegerRow 32 3 1 796551886501228,
    decodeIntegerRow 32 3 1 1570358519910732,
    decodeIntegerRow 32 3 1 1193103789226876,
    decodeIntegerRow 32 3 1 1071157078628908,
    decodeIntegerRow 32 3 1 1519709227877084,
    decodeIntegerRow 32 3 1 1519709241000108,
    decodeIntegerRow 32 3 1 1071157049021476,
    decodeIntegerRow 32 3 1 659916427334068,
    decodeIntegerRow 32 3 1 282661662906876]

def rows_assocBCA (r : RightIndex 5 2 3) : List ℤ := rows_assocBCAData.getD (rightPosition 5 2 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 2 3) : (tripleIndices 4 2 4).map ((HexagonAtoms352.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_0_2_0
  · exact rows_assocBCA_eq_0_2_1
  · exact rows_assocBCA_eq_0_2_2
  · exact rows_assocBCA_eq_0_2_3
  · exact rows_assocBCA_eq_0_3_0
  · exact rows_assocBCA_eq_0_3_1
  · exact rows_assocBCA_eq_0_3_2
  · exact rows_assocBCA_eq_0_3_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3
  · exact rows_assocBCA_eq_1_2_0
  · exact rows_assocBCA_eq_1_2_1
  · exact rows_assocBCA_eq_1_2_2
  · exact rows_assocBCA_eq_1_2_3
  · exact rows_assocBCA_eq_1_3_0
  · exact rows_assocBCA_eq_1_3_1
  · exact rows_assocBCA_eq_1_3_2
  · exact rows_assocBCA_eq_1_3_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 929989890377764,
    decodeIntegerRow 32 3 1 918622981733592,
    decodeIntegerRow 32 3 1 933811417772996,
    decodeIntegerRow 32 3 1 924717873426328,
    decodeIntegerRow 32 3 1 924717901061284,
    decodeIntegerRow 32 3 1 933811424150232,
    decodeIntegerRow 32 3 1 934397194363716,
    decodeIntegerRow 32 3 1 923030268713368,
    decodeIntegerRow 32 3 1 929808607349608,
    decodeIntegerRow 32 3 1 918581153075364,
    decodeIntegerRow 32 3 1 933895106975912,
    decodeIntegerRow 32 3 1 924913160987716,
    decodeIntegerRow 32 3 1 928107055499032,
    decodeIntegerRow 32 3 1 919125088253276,
    decodeIntegerRow 32 3 1 918581140320728,
    decodeIntegerRow 32 3 1 929808577588924,
    decodeIntegerRow 32 3 1 1521307214857192,
    decodeIntegerRow 32 3 1 1063769643677884,
    decodeIntegerRow 32 3 1 651989703997912,
    decodeIntegerRow 32 3 1 285959647487524,
    decodeIntegerRow 32 3 1 1567060541525992,
    decodeIntegerRow 32 3 1 1201030484487484,
    decodeIntegerRow 32 3 1 1063769644017112,
    decodeIntegerRow 32 3 1 1521307214773924,
    decodeIntegerRow 32 3 1 331714007194684,
    decodeIntegerRow 32 3 1 789248134216408,
    decodeIntegerRow 32 3 1 1201032722916004,
    decodeIntegerRow 32 3 1 1567060024961128,
    decodeIntegerRow 32 3 1 1567060024807876,
    decodeIntegerRow 32 3 1 1201032723284392,
    decodeIntegerRow 32 3 1 1063772054292316,
    decodeIntegerRow 32 3 1 1521306181731352]

def rows_assocCAB (r : RightIndex 2 3 5) : List ℤ := rows_assocCABData.getD (rightPosition 2 3 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 3 5) : (tripleIndices 2 4 4).map ((HexagonAtoms352.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 335200020088964,
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

def cols_assocABC (r : LeftIndex 3 5 2) : List ℤ := cols_assocABCData.getD (leftPosition 3 5 2 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 5 2) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms352.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 335200020088964,
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

def cols_right0 (r : LeftIndex 3 5 2) : List ℤ := cols_right0Data.getD (leftPosition 3 5 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 5 2) : (tripleIndices 4 2 4).map (fun j => (right0Middle3 5 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1517820175505588,
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

def cols_left0 (r : LeftIndex 3 5 2) : List ℤ := cols_left0Data.getD (leftPosition 3 5 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 5 2) : (tripleIndices 4 2 4).map (fun j => (left0Middle3 5 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 11637932252945434570352,
    decodeIntegerRow 32 5 2 11656548738494262695064,
    decodeIntegerRow 32 5 2 11626755952844848632560,
    decodeIntegerRow 32 5 2 11643940401137817382872,
    decodeIntegerRow 32 5 2 11643940401016723632752,
    decodeIntegerRow 32 5 2 11626755952825317383064,
    decodeIntegerRow 32 5 2 11626515626921997070064,
    decodeIntegerRow 32 5 2 11645132112564575195352,
    decodeIntegerRow 32 5 2 11637979555068481445352,
    decodeIntegerRow 32 5 2 11656556367859497070064,
    decodeIntegerRow 32 5 2 11626744508733520507560,
    decodeIntegerRow 32 5 2 11643892335831176757872,
    decodeIntegerRow 32 5 2 11639172029434692382872,
    decodeIntegerRow 32 5 2 11656319856633911132560,
    decodeIntegerRow 32 5 2 11656556367888793945560,
    decodeIntegerRow 32 5 2 11637979555191528320272,
    decodeIntegerRow 32 5 2 2402812233352645350312,
    decodeIntegerRow 32 5 2 10151416101760961095312,
    decodeIntegerRow 32 5 2 13876706323928931420312,
    decodeIntegerRow 32 5 2 21029263740920996915312,
    decodeIntegerRow 32 5 2 2253800624465918790312,
    decodeIntegerRow 32 5 2 9406358041458228295312,
    decodeIntegerRow 32 5 2 10151416101760767420312,
    decodeIntegerRow 32 5 2 2402812233352676915312,
    decodeIntegerRow 32 5 2 20880252113723739415312,
    decodeIntegerRow 32 5 2 13131648340530492420312,
    decodeIntegerRow 32 5 2 9406357965774634595312,
    decodeIntegerRow 32 5 2 2253800636672950350312,
    decodeIntegerRow 32 5 2 2253800636672996915312,
    decodeIntegerRow 32 5 2 9406357965774437670312,
    decodeIntegerRow 32 5 2 10151416024856664295312,
    decodeIntegerRow 32 5 2 2402812251663192540312]

def cols_right2 (r : LeftIndex 3 5 2) : List ℤ := cols_right2Data.getD (leftPosition 3 5 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 5 2) : (tripleIndices 2 4 4).map (fun j => (right2Middle3 5 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms352.outerABC * HexagonAtoms352.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms352.assocBAC * HexagonAtoms352.innerABC = HexagonAtoms352.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms352.innerRightABC * HexagonAtoms352.assocABC = HexagonAtoms352.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms352.inverseACB * right0Middle3 5 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms352.innerACB * right1Middle3 5 2 = right1Middle3 5 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms352.assocBCA * left0Middle3 5 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms352.innerRightBAC * left1Middle3 5 2 = left1Middle3 5 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms352.assocCAB * right2Middle3 5 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn352
