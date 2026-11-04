import RMod.BrundanEllis.StackingReferenceHexagonAtoms434
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn434
open Superfusion

theorem assocBCA_alias : HexagonAtoms434.assocBCA = HexagonAtoms434.assocBAC :=
  HexagonAtoms434.assocBCA_eq.symm.trans HexagonAtoms434.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 929055442255682,
    decodeIntegerRow 32 3 1 918874022238826,
    decodeIntegerRow 32 3 1 926196283298398,
    decodeIntegerRow 32 3 1 927451524619894,
    decodeIntegerRow 32 3 1 1132401183532978,
    decodeIntegerRow 32 3 1 308836827459526,
    decodeIntegerRow 32 3 1 903633689398738,
    decodeIntegerRow 32 3 1 995139309551206,
    decodeIntegerRow 32 3 1 925756950589654,
    decodeIntegerRow 32 3 1 926761143434242,
    decodeIntegerRow 32 3 1 918894942945226,
    decodeIntegerRow 32 3 1 929048468686878,
    decodeIntegerRow 32 3 1 857878554782074,
    decodeIntegerRow 32 3 1 949387274295538,
    decodeIntegerRow 32 3 1 308836569178714,
    decodeIntegerRow 32 3 1 1132401269626258,
    decodeIntegerRow 32 3 1 949386499467682,
    decodeIntegerRow 32 3 1 857880879344374,
    decodeIntegerRow 32 3 1 720619005437122,
    decodeIntegerRow 32 3 1 1544183361747094,
    decodeIntegerRow 32 3 1 926196284361262,
    decodeIntegerRow 32 3 1 927451527808486,
    decodeIntegerRow 32 3 1 929055451821618,
    decodeIntegerRow 32 3 1 918874050936634,
    decodeIntegerRow 32 3 1 1544183620026934,
    decodeIntegerRow 32 3 1 720618919343518,
    decodeIntegerRow 32 3 1 995141634034774,
    decodeIntegerRow 32 3 1 903632914544638,
    decodeIntegerRow 32 3 1 918894971643046,
    decodeIntegerRow 32 3 1 929048478252818,
    decodeIntegerRow 32 3 1 925756947400954,
    decodeIntegerRow 32 3 1 926761142371342]

def rows_inverseACB (r : LeftIndex 4 4 3) : List ℤ := rows_inverseACBData.getD (leftPosition 4 4 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 4 3) : (tripleIndices 4 1 8).map ((HexagonAtoms434.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425921,
    decodeIntegerRow 32 3 1 926510094425923,
    decodeIntegerRow 32 3 1 926510094425929,
    decodeIntegerRow 32 3 1 926510094425947,
    decodeIntegerRow 32 3 1 926510094426001,
    decodeIntegerRow 32 3 1 926510094426163,
    decodeIntegerRow 32 3 1 926510094426649,
    decodeIntegerRow 32 3 1 926510094428107,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094406237,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510094248773,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510089642951,
    decodeIntegerRow 32 3 1 926510080077013,
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

def rows_innerACB (r : LeftIndex 4 4 3) : List ℤ := rows_innerACBData.getD (leftPosition 4 4 3 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 4 4 3) : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_0_4
  · exact rows_innerACB_eq_0_0_5
  · exact rows_innerACB_eq_0_0_6
  · exact rows_innerACB_eq_0_0_7
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_0_2
  · exact rows_innerACB_eq_1_0_3
  · exact rows_innerACB_eq_1_0_4
  · exact rows_innerACB_eq_1_0_5
  · exact rows_innerACB_eq_1_0_6
  · exact rows_innerACB_eq_1_0_7
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_0_1
  · exact rows_innerACB_eq_2_0_2
  · exact rows_innerACB_eq_2_0_3
  · exact rows_innerACB_eq_2_0_4
  · exact rows_innerACB_eq_2_0_5
  · exact rows_innerACB_eq_2_0_6
  · exact rows_innerACB_eq_2_0_7
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_0_1
  · exact rows_innerACB_eq_3_0_2
  · exact rows_innerACB_eq_3_0_3
  · exact rows_innerACB_eq_3_0_4
  · exact rows_innerACB_eq_3_0_5
  · exact rows_innerACB_eq_3_0_6
  · exact rows_innerACB_eq_3_0_7

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 929055442255682,
    decodeIntegerRow 32 3 1 918874022238826,
    decodeIntegerRow 32 3 1 926196283298398,
    decodeIntegerRow 32 3 1 927451524619894,
    decodeIntegerRow 32 3 1 1132401183532978,
    decodeIntegerRow 32 3 1 308836827459526,
    decodeIntegerRow 32 3 1 903633689398738,
    decodeIntegerRow 32 3 1 995139309551206,
    decodeIntegerRow 32 3 1 927263238262186,
    decodeIntegerRow 32 3 1 926259045417598,
    decodeIntegerRow 32 3 1 934125245906614,
    decodeIntegerRow 32 3 1 923971720164962,
    decodeIntegerRow 32 3 1 995141634069766,
    decodeIntegerRow 32 3 1 903632914556302,
    decodeIntegerRow 32 3 1 1544183619673126,
    decodeIntegerRow 32 3 1 720618919225582,
    decodeIntegerRow 32 3 1 903633689384158,
    decodeIntegerRow 32 3 1 995139309507466,
    decodeIntegerRow 32 3 1 1132401183414718,
    decodeIntegerRow 32 3 1 308836827104746,
    decodeIntegerRow 32 3 1 926823904490578,
    decodeIntegerRow 32 3 1 925568661043354,
    decodeIntegerRow 32 3 1 923964737030222,
    decodeIntegerRow 32 3 1 934146137915206,
    decodeIntegerRow 32 3 1 308836568824906,
    decodeIntegerRow 32 3 1 1132401269508322,
    decodeIntegerRow 32 3 1 857878554817066,
    decodeIntegerRow 32 3 1 949387274307202,
    decodeIntegerRow 32 3 1 934125217208794,
    decodeIntegerRow 32 3 1 923971710599022,
    decodeIntegerRow 32 3 1 927263241450886,
    decodeIntegerRow 32 3 1 926259046480498]

def rows_assocBAC (r : RightIndex 3 4 4) : List ℤ := rows_assocBACData.getD (rightPosition 3 4 4 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 3 4 4) : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_0_4
  · exact rows_assocBAC_eq_0_0_5
  · exact rows_assocBAC_eq_0_0_6
  · exact rows_assocBAC_eq_0_0_7
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_0_4
  · exact rows_assocBAC_eq_1_0_5
  · exact rows_assocBAC_eq_1_0_6
  · exact rows_assocBAC_eq_1_0_7
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_2_0_4
  · exact rows_assocBAC_eq_2_0_5
  · exact rows_assocBAC_eq_2_0_6
  · exact rows_assocBAC_eq_2_0_7
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3
  · exact rows_assocBAC_eq_3_0_4
  · exact rows_assocBAC_eq_3_0_5
  · exact rows_assocBAC_eq_3_0_6
  · exact rows_assocBAC_eq_3_0_7

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425921,
    decodeIntegerRow 32 3 1 926510094425923,
    decodeIntegerRow 32 3 1 926510094425929,
    decodeIntegerRow 32 3 1 926510094425947,
    decodeIntegerRow 32 3 1 926510094426001,
    decodeIntegerRow 32 3 1 926510094426163,
    decodeIntegerRow 32 3 1 926510094426649,
    decodeIntegerRow 32 3 1 926510094428107,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094406237,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510094248773,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510089642951,
    decodeIntegerRow 32 3 1 926510080077013,
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

def rows_innerRightBAC (r : RightIndex 3 4 4) : List ℤ := rows_innerRightBACData.getD (rightPosition 3 4 4 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 3 4 4) : (tripleIndices 4 1 8).map ((HexagonAtoms434.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_0_4
  · exact rows_innerRightBAC_eq_0_0_5
  · exact rows_innerRightBAC_eq_0_0_6
  · exact rows_innerRightBAC_eq_0_0_7
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_0_2
  · exact rows_innerRightBAC_eq_1_0_3
  · exact rows_innerRightBAC_eq_1_0_4
  · exact rows_innerRightBAC_eq_1_0_5
  · exact rows_innerRightBAC_eq_1_0_6
  · exact rows_innerRightBAC_eq_1_0_7
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_0_1
  · exact rows_innerRightBAC_eq_2_0_2
  · exact rows_innerRightBAC_eq_2_0_3
  · exact rows_innerRightBAC_eq_2_0_4
  · exact rows_innerRightBAC_eq_2_0_5
  · exact rows_innerRightBAC_eq_2_0_6
  · exact rows_innerRightBAC_eq_2_0_7
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_0_1
  · exact rows_innerRightBAC_eq_3_0_2
  · exact rows_innerRightBAC_eq_3_0_3
  · exact rows_innerRightBAC_eq_3_0_4
  · exact rows_innerRightBAC_eq_3_0_5
  · exact rows_innerRightBAC_eq_3_0_6
  · exact rows_innerRightBAC_eq_3_0_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 995109090554048,
    decodeIntegerRow 32 3 1 949292743643008,
    decodeIntegerRow 32 3 1 308833211377264,
    decodeIntegerRow 32 3 1 720608501984656,
    decodeIntegerRow 32 3 1 925663178888140,
    decodeIntegerRow 32 3 1 926228822368180,
    decodeIntegerRow 32 3 1 934135736552680,
    decodeIntegerRow 32 3 1 929052089928040,
    decodeIntegerRow 32 3 1 918884538394060,
    decodeIntegerRow 32 3 1 923968357208500,
    decodeIntegerRow 32 3 1 927357784804840,
    decodeIntegerRow 32 3 1 926793691007080,
    decodeIntegerRow 32 3 1 308840184946048,
    decodeIntegerRow 32 3 1 720629422691008,
    decodeIntegerRow 32 3 1 995171852673264,
    decodeIntegerRow 32 3 1 949481030000656,
    decodeIntegerRow 32 3 1 925663207585792,
    decodeIntegerRow 32 3 1 926791356918208,
    decodeIntegerRow 32 3 1 918884455489264,
    decodeIntegerRow 32 3 1 929052088860784,
    decodeIntegerRow 32 3 1 857911097943500,
    decodeIntegerRow 32 3 1 949292743761100,
    decodeIntegerRow 32 3 1 308833211337880,
    decodeIntegerRow 32 3 1 1132411686880360,
    decodeIntegerRow 32 3 1 1544180003945140,
    decodeIntegerRow 32 3 1 720629422677940,
    decodeIntegerRow 32 3 1 995171853027560,
    decodeIntegerRow 32 3 1 903539158733080,
    decodeIntegerRow 32 3 1 918884541581248,
    decodeIntegerRow 32 3 1 929051830584832,
    decodeIntegerRow 32 3 1 925662432744976,
    decodeIntegerRow 32 3 1 926793681440656]

def rows_assocCAB (r : RightIndex 4 4 3) : List ℤ := rows_assocCABData.getD (rightPosition 4 4 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 4 4 3) : (tripleIndices 4 1 8).map ((HexagonAtoms434.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_0_4
  · exact rows_assocCAB_eq_2_0_5
  · exact rows_assocCAB_eq_2_0_6
  · exact rows_assocCAB_eq_2_0_7
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_0_4
  · exact rows_assocCAB_eq_3_0_5
  · exact rows_assocCAB_eq_3_0_6
  · exact rows_assocCAB_eq_3_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 923964746596160,
    decodeIntegerRow 32 3 1 934146166613020,
    decodeIntegerRow 32 3 1 926823905553460,
    decodeIntegerRow 32 3 1 925568664232000,
    decodeIntegerRow 32 3 1 720619005319024,
    decodeIntegerRow 32 3 1 1544183361392800,
    decodeIntegerRow 32 3 1 949386499454560,
    decodeIntegerRow 32 3 1 857880879305008,
    decodeIntegerRow 32 3 1 949386499466224,
    decodeIntegerRow 32 3 1 857880879340000,
    decodeIntegerRow 32 3 1 720619005436960,
    decodeIntegerRow 32 3 1 1544183361746608,
    decodeIntegerRow 32 3 1 926196284361280,
    decodeIntegerRow 32 3 1 927451527808540,
    decodeIntegerRow 32 3 1 929055451821620,
    decodeIntegerRow 32 3 1 918874050936640,
    decodeIntegerRow 32 3 1 1132401269626420,
    decodeIntegerRow 32 3 1 1544183619672640,
    decodeIntegerRow 32 3 1 949387274294080,
    decodeIntegerRow 32 3 1 995141634074140,
    decodeIntegerRow 32 3 1 923971720164960,
    decodeIntegerRow 32 3 1 918894942945232,
    decodeIntegerRow 32 3 1 926259045417616,
    decodeIntegerRow 32 3 1 925756950589600,
    decodeIntegerRow 32 3 1 926761142371360,
    decodeIntegerRow 32 3 1 927263241450832,
    decodeIntegerRow 32 3 1 929048478252816,
    decodeIntegerRow 32 3 1 934125217208800,
    decodeIntegerRow 32 3 1 949387274308660,
    decodeIntegerRow 32 3 1 995141634030400,
    decodeIntegerRow 32 3 1 1132401269508160,
    decodeIntegerRow 32 3 1 1544183620027420]

def cols_right0 (r : LeftIndex 4 3 4) : List ℤ := cols_right0Data.getD (leftPosition 4 3 4 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 3 4) : (tripleIndices 4 1 8).map (fun j => (right0Middle4 3 4) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_0_4
  · exact cols_right0_eq_2_0_5
  · exact cols_right0_eq_2_0_6
  · exact cols_right0_eq_2_0_7
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_0_4
  · exact cols_right0_eq_3_0_5
  · exact cols_right0_eq_3_0_6
  · exact cols_right0_eq_3_0_7

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 32 5 2 12014056444167993164060,
    decodeIntegerRow 32 5 2 11716014146804790039052,
    decodeIntegerRow 32 5 2 2328306245803836914012,
    decodeIntegerRow 32 5 2 9778886079788208788812,
    decodeIntegerRow 32 5 2 11640936143814086912812,
    decodeIntegerRow 32 5 2 11641413011538696282812,
    decodeIntegerRow 32 5 2 11656433344194946257812,
    decodeIntegerRow 32 5 2 11644512416458618007812,
    decodeIntegerRow 32 5 2 11626631021802368132812,
    decodeIntegerRow 32 5 2 11638551951980102382812,
    decodeIntegerRow 32 5 2 11642128236831665037812,
    decodeIntegerRow 32 5 2 11641651430142211907812,
    decodeIntegerRow 32 5 2 2328306627273563476612,
    decodeIntegerRow 32 5 2 9778887987136841601812,
    decodeIntegerRow 32 5 2 12014065980911157226564,
    decodeIntegerRow 32 5 2 11716061830520610351572,
    decodeIntegerRow 32 5 2 11640936143936157227812,
    decodeIntegerRow 32 5 2 11641651353823852532812,
    decodeIntegerRow 32 5 2 11626631021196899382812,
    decodeIntegerRow 32 5 2 11644512416457641757812,
    decodeIntegerRow 32 5 2 11269007921218774414060,
    decodeIntegerRow 32 5 2 11716014146804829101572,
    decodeIntegerRow 32 5 2 2328306245803829101612,
    decodeIntegerRow 32 5 2 13504178285598755663812,
    decodeIntegerRow 32 5 2 20954757738113407226612,
    decodeIntegerRow 32 5 2 9778887987136840038812,
    decodeIntegerRow 32 5 2 12014065980911352539060,
    decodeIntegerRow 32 5 2 11567002534866313476572,
    decodeIntegerRow 32 5 2 11626631021807251007812,
    decodeIntegerRow 32 5 2 11644512413405883632812,
    decodeIntegerRow 32 5 2 11640936128677368162812,
    decodeIntegerRow 32 5 2 11641651430117797857812]

def cols_right1 (r : LeftIndex 4 3 4) : List ℤ := cols_right1Data.getD (leftPosition 4 3 4 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 4 3 4) : (tripleIndices 4 1 8).map (fun j => (right1Middle4 3 4) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_0_4
  · exact cols_right1_eq_0_0_5
  · exact cols_right1_eq_0_0_6
  · exact cols_right1_eq_0_0_7
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_0_4
  · exact cols_right1_eq_1_0_5
  · exact cols_right1_eq_1_0_6
  · exact cols_right1_eq_1_0_7
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_0_2
  · exact cols_right1_eq_2_0_3
  · exact cols_right1_eq_2_0_4
  · exact cols_right1_eq_2_0_5
  · exact cols_right1_eq_2_0_6
  · exact cols_right1_eq_2_0_7
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_0_2
  · exact cols_right1_eq_3_0_3
  · exact cols_right1_eq_3_0_4
  · exact cols_right1_eq_3_0_5
  · exact cols_right1_eq_3_0_6
  · exact cols_right1_eq_3_0_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 923964746596160,
    decodeIntegerRow 32 3 1 934146166613020,
    decodeIntegerRow 32 3 1 926823905553460,
    decodeIntegerRow 32 3 1 925568664232000,
    decodeIntegerRow 32 3 1 720619005319024,
    decodeIntegerRow 32 3 1 1544183361392800,
    decodeIntegerRow 32 3 1 949386499454560,
    decodeIntegerRow 32 3 1 857880879305008,
    decodeIntegerRow 32 3 1 949386499466224,
    decodeIntegerRow 32 3 1 857880879340000,
    decodeIntegerRow 32 3 1 720619005436960,
    decodeIntegerRow 32 3 1 1544183361746608,
    decodeIntegerRow 32 3 1 926196284361280,
    decodeIntegerRow 32 3 1 927451527808540,
    decodeIntegerRow 32 3 1 929055451821620,
    decodeIntegerRow 32 3 1 918874050936640,
    decodeIntegerRow 32 3 1 1132401269626420,
    decodeIntegerRow 32 3 1 1544183619672640,
    decodeIntegerRow 32 3 1 949387274294080,
    decodeIntegerRow 32 3 1 995141634074140,
    decodeIntegerRow 32 3 1 923971720164960,
    decodeIntegerRow 32 3 1 918894942945232,
    decodeIntegerRow 32 3 1 926259045417616,
    decodeIntegerRow 32 3 1 925756950589600,
    decodeIntegerRow 32 3 1 926761142371360,
    decodeIntegerRow 32 3 1 927263241450832,
    decodeIntegerRow 32 3 1 929048478252816,
    decodeIntegerRow 32 3 1 934125217208800,
    decodeIntegerRow 32 3 1 949387274308660,
    decodeIntegerRow 32 3 1 995141634030400,
    decodeIntegerRow 32 3 1 1132401269508160,
    decodeIntegerRow 32 3 1 1544183620027420]

def cols_left0 (r : LeftIndex 4 3 4) : List ℤ := cols_left0Data.getD (leftPosition 4 3 4 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 3 4) : (tripleIndices 4 1 8).map (fun j => (left0Middle4 3 4) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_0_4
  · exact cols_left0_eq_2_0_5
  · exact cols_left0_eq_2_0_6
  · exact cols_left0_eq_2_0_7
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_0_4
  · exact cols_left0_eq_3_0_5
  · exact cols_left0_eq_3_0_6
  · exact cols_left0_eq_3_0_7

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 32 3 1 857911098297794,
    decodeIntegerRow 32 3 1 903727445208838,
    decodeIntegerRow 32 3 1 1544186977474594,
    decodeIntegerRow 32 3 1 1132411686867238,
    decodeIntegerRow 32 3 1 927357009963862,
    decodeIntegerRow 32 3 1 926791366484146,
    decodeIntegerRow 32 3 1 918884452300618,
    decodeIntegerRow 32 3 1 923968098928174,
    decodeIntegerRow 32 3 1 934135650459238,
    decodeIntegerRow 32 3 1 929051831647714,
    decodeIntegerRow 32 3 1 925662404047162,
    decodeIntegerRow 32 3 1 926226497845246,
    decodeIntegerRow 32 3 1 1544180003905774,
    decodeIntegerRow 32 3 1 1132390766160778,
    decodeIntegerRow 32 3 1 857848336178574,
    decodeIntegerRow 32 3 1 903539158851178,
    decodeIntegerRow 32 3 1 927356981265886,
    decodeIntegerRow 32 3 1 926228831934118,
    decodeIntegerRow 32 3 1 934135733364034,
    decodeIntegerRow 32 3 1 923968099986682,
    decodeIntegerRow 32 3 1 995109090908342,
    decodeIntegerRow 32 3 1 903727445090734,
    decodeIntegerRow 32 3 1 1544186977513942,
    decodeIntegerRow 32 3 1 720608501971534,
    decodeIntegerRow 32 3 1 308840184906682,
    decodeIntegerRow 32 3 1 1132390766173954,
    decodeIntegerRow 32 3 1 857848335824282,
    decodeIntegerRow 32 3 1 949481030118754,
    decodeIntegerRow 32 3 1 934135647269134,
    decodeIntegerRow 32 3 1 923968358271382,
    decodeIntegerRow 32 3 1 927357756107026,
    decodeIntegerRow 32 3 1 926226507410698]

def cols_left1 (r : LeftIndex 4 3 4) : List ℤ := cols_left1Data.getD (leftPosition 4 3 4 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 4 3 4) : (tripleIndices 4 1 8).map (fun j => (left1Middle4 3 4) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_0_4
  · exact cols_left1_eq_0_0_5
  · exact cols_left1_eq_0_0_6
  · exact cols_left1_eq_0_0_7
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_0_4
  · exact cols_left1_eq_1_0_5
  · exact cols_left1_eq_1_0_6
  · exact cols_left1_eq_1_0_7
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_0_2
  · exact cols_left1_eq_2_0_3
  · exact cols_left1_eq_2_0_4
  · exact cols_left1_eq_2_0_5
  · exact cols_left1_eq_2_0_6
  · exact cols_left1_eq_2_0_7
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_0_2
  · exact cols_left1_eq_3_0_3
  · exact cols_left1_eq_3_0_4
  · exact cols_left1_eq_3_0_5
  · exact cols_left1_eq_3_0_6
  · exact cols_left1_eq_3_0_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 11269007921218969726560,
    decodeIntegerRow 32 5 2 11567050218582172851552,
    decodeIntegerRow 32 5 2 20954758119583125976512,
    decodeIntegerRow 32 5 2 13504178285598754101312,
    decodeIntegerRow 32 5 2 11642128221572875975312,
    decodeIntegerRow 32 5 2 11641651353848266595312,
    decodeIntegerRow 32 5 2 11626631021192016570312,
    decodeIntegerRow 32 5 2 11638551948928344570312,
    decodeIntegerRow 32 5 2 11656433343584594695312,
    decodeIntegerRow 32 5 2 11644512413406860195312,
    decodeIntegerRow 32 5 2 11640936128555297850312,
    decodeIntegerRow 32 5 2 11641412935244750970312,
    decodeIntegerRow 32 5 2 20954757738113399414112,
    decodeIntegerRow 32 5 2 13504176378250121289312,
    decodeIntegerRow 32 5 2 11268998384475805664064,
    decodeIntegerRow 32 5 2 11567002534866352539072,
    decodeIntegerRow 32 5 2 11642128221450805665312,
    decodeIntegerRow 32 5 2 11641413011563110345312,
    decodeIntegerRow 32 5 2 11656433344190063445312,
    decodeIntegerRow 32 5 2 11638551948929321445312,
    decodeIntegerRow 32 5 2 12014056444168188476560,
    decodeIntegerRow 32 5 2 11567050218582133789072,
    decodeIntegerRow 32 5 2 20954758119583133789112,
    decodeIntegerRow 32 5 2 9778886079788207226312,
    decodeIntegerRow 32 5 2 2328306627273555664112,
    decodeIntegerRow 32 5 2 13504176378250122851312,
    decodeIntegerRow 32 5 2 11268998384475610351560,
    decodeIntegerRow 32 5 2 11716061830520649414072,
    decodeIntegerRow 32 5 2 11656433343579711945312,
    decodeIntegerRow 32 5 2 11638551951981078945312,
    decodeIntegerRow 32 5 2 11642128236709594725312,
    decodeIntegerRow 32 5 2 11641412935269165045312]

def cols_right2 (r : LeftIndex 4 3 4) : List ℤ := cols_right2Data.getD (leftPosition 4 3 4 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 3 4) : (tripleIndices 4 1 8).map (fun j => (right2Middle4 3 4) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_0_4
  · exact cols_right2_eq_2_0_5
  · exact cols_right2_eq_2_0_6
  · exact cols_right2_eq_2_0_7
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_0_4
  · exact cols_right2_eq_3_0_5
  · exact cols_right2_eq_3_0_6
  · exact cols_right2_eq_3_0_7

theorem product0_eq : HexagonAtoms434.outerABC * HexagonAtoms434.assocABC = HexagonAtoms434.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms434.assocBAC * HexagonAtoms434.innerABC = HexagonAtoms434.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms434.innerRightABC * HexagonAtoms434.assocABC = HexagonAtoms434.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms434.inverseACB * right0Middle4 3 4 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms434.innerACB * right1Middle4 3 4 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms434.assocBAC * left0Middle4 3 4 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms434.innerRightBAC * left1Middle4 3 4 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms434.assocCAB * right2Middle4 3 4 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn434
