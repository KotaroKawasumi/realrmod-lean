import RMod.BrundanEllis.StackingReferenceHexagonAtoms323
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn323
open Superfusion

theorem assocBCA_alias : HexagonAtoms323.assocBCA = HexagonAtoms323.assocBAC :=
  HexagonAtoms323.assocBCA_eq.symm.trans HexagonAtoms323.assocBAC_eq

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def rows_outerABC (r : LeftIndex 2 3 3) : List ℤ := rows_outerABCData.getD (leftPosition 2 3 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 2 3 3) : (tripleIndices 2 8 1).map ((HexagonAtoms323.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_2_0
  · exact rows_outerABC_eq_0_3_0
  · exact rows_outerABC_eq_0_4_0
  · exact rows_outerABC_eq_0_5_0
  · exact rows_outerABC_eq_0_6_0
  · exact rows_outerABC_eq_0_7_0
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_2_0
  · exact rows_outerABC_eq_1_3_0
  · exact rows_outerABC_eq_1_4_0
  · exact rows_outerABC_eq_1_5_0
  · exact rows_outerABC_eq_1_6_0
  · exact rows_outerABC_eq_1_7_0

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 21700264,
    decodeIntegerRow 16 3 1 21582328]

def rows_inverseACB (r : LeftIndex 3 3 2) : List ℤ := rows_inverseACBData.getD (leftPosition 3 3 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 3 2) : (tripleIndices 2 8 1).map ((HexagonAtoms323.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_2_0
  · exact rows_inverseACB_eq_2_3_0
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_2_0
  · exact rows_inverseACB_eq_3_3_0

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 23621404,
    decodeIntegerRow 16 3 1 22570168,
    decodeIntegerRow 16 3 1 40418876,
    decodeIntegerRow 16 3 1 30970872,
    decodeIntegerRow 16 3 1 19422364,
    decodeIntegerRow 16 3 1 20470648,
    decodeIntegerRow 16 3 1 2627516,
    decodeIntegerRow 16 3 1 12075192,
    decodeIntegerRow 16 3 1 40891272,
    decodeIntegerRow 16 3 1 11839644,
    decodeIntegerRow 16 3 1 23673928,
    decodeIntegerRow 16 3 1 20450236,
    decodeIntegerRow 16 3 1 40891592,
    decodeIntegerRow 16 3 1 11839004,
    decodeIntegerRow 16 3 1 23676808,
    decodeIntegerRow 16 3 1 20444476]

def rows_innerACB (r : LeftIndex 3 3 2) : List ℤ := rows_innerACBData.getD (leftPosition 3 3 2 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 3 3 2) : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_2_0
  · exact rows_innerACB_eq_0_3_0
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_2_0
  · exact rows_innerACB_eq_1_3_0
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_1_0
  · exact rows_innerACB_eq_2_2_0
  · exact rows_innerACB_eq_2_3_0
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_1_0
  · exact rows_innerACB_eq_3_2_0
  · exact rows_innerACB_eq_3_3_0

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523328,
    decodeIntegerRow 16 3 1 21523344,
    decodeIntegerRow 16 3 1 21785800,
    decodeIntegerRow 16 3 1 21392140,
    decodeIntegerRow 16 3 1 21523320,
    decodeIntegerRow 16 3 1 21523340,
    decodeIntegerRow 16 3 1 21313408,
    decodeIntegerRow 16 3 1 21628336,
    decodeIntegerRow 16 3 1 21526600,
    decodeIntegerRow 16 3 1 21524980,
    decodeIntegerRow 16 3 1 4517248,
    decodeIntegerRow 16 3 1 30026416,
    decodeIntegerRow 16 3 1 21520768,
    decodeIntegerRow 16 3 1 21522064,
    decodeIntegerRow 16 3 1 265720,
    decodeIntegerRow 16 3 1 32152180]

def rows_assocBAC (r : RightIndex 2 3 3) : List ℤ := rows_assocBACData.getD (rightPosition 2 3 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 2 3 3) : (tripleIndices 2 8 1).map ((HexagonAtoms323.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_2_0
  · exact rows_assocBAC_eq_0_3_0
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_2_0
  · exact rows_assocBAC_eq_1_3_0
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_2_0
  · exact rows_assocBAC_eq_2_3_0
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_2_0
  · exact rows_assocBAC_eq_3_3_0

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 23621404,
    decodeIntegerRow 16 3 1 22570168,
    decodeIntegerRow 16 3 1 40418876,
    decodeIntegerRow 16 3 1 30970872,
    decodeIntegerRow 16 3 1 19422364,
    decodeIntegerRow 16 3 1 20470648,
    decodeIntegerRow 16 3 1 2627516,
    decodeIntegerRow 16 3 1 12075192,
    decodeIntegerRow 16 3 1 40891272,
    decodeIntegerRow 16 3 1 11839644,
    decodeIntegerRow 16 3 1 23673928,
    decodeIntegerRow 16 3 1 20450236,
    decodeIntegerRow 16 3 1 40891592,
    decodeIntegerRow 16 3 1 11839004,
    decodeIntegerRow 16 3 1 23676808,
    decodeIntegerRow 16 3 1 20444476]

def rows_innerRightBAC (r : RightIndex 2 3 3) : List ℤ := rows_innerRightBACData.getD (rightPosition 2 3 3 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 2 3 3) : (tripleIndices 4 4 1).map ((HexagonAtoms323.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_2_0
  · exact rows_innerRightBAC_eq_0_3_0
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_2_0
  · exact rows_innerRightBAC_eq_1_3_0
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_1_0
  · exact rows_innerRightBAC_eq_2_2_0
  · exact rows_innerRightBAC_eq_2_3_0
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_1_0
  · exact rows_innerRightBAC_eq_3_2_0
  · exact rows_innerRightBAC_eq_3_3_0

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 20998480,
    decodeIntegerRow 16 3 1 19948720,
    decodeIntegerRow 16 3 1 21524098,
    decodeIntegerRow 16 3 1 21521146,
    decodeIntegerRow 16 3 1 6997306,
    decodeIntegerRow 16 3 1 16681342,
    decodeIntegerRow 16 3 1 21523600,
    decodeIntegerRow 16 3 1 21523280,
    decodeIntegerRow 16 3 1 21523114,
    decodeIntegerRow 16 3 1 21523442,
    decodeIntegerRow 16 3 1 35695120,
    decodeIntegerRow 16 3 1 26247280,
    decodeIntegerRow 16 3 1 21524080,
    decodeIntegerRow 16 3 1 21521200,
    decodeIntegerRow 16 3 1 20985358,
    decodeIntegerRow 16 3 1 19909354]

def rows_assocCAB (r : RightIndex 3 3 2) : List ℤ := rows_assocCABData.getD (rightPosition 3 3 2 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 3 2) : (tripleIndices 4 4 1).map ((HexagonAtoms323.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_2_0
  · exact rows_assocCAB_eq_0_3_0
  · exact rows_assocCAB_eq_0_4_0
  · exact rows_assocCAB_eq_0_5_0
  · exact rows_assocCAB_eq_0_6_0
  · exact rows_assocCAB_eq_0_7_0
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_2_0
  · exact rows_assocCAB_eq_1_3_0
  · exact rows_assocCAB_eq_1_4_0
  · exact rows_assocCAB_eq_1_5_0
  · exact rows_assocCAB_eq_1_6_0
  · exact rows_assocCAB_eq_1_7_0

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21524818,
    decodeIntegerRow 16 3 1 21497116,
    decodeIntegerRow 16 3 1 21510238,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 2391484,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523342,
    decodeIntegerRow 16 3 1 21523396,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21523684,
    decodeIntegerRow 16 3 1 21523522]

def cols_assocABC (r : LeftIndex 3 2 3) : List ℤ := cols_assocABCData.getD (leftPosition 3 2 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_4_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_5_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_6_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_7_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_4_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_5_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_6_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_7_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 2 3) : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms323.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_2_0
  · exact cols_assocABC_eq_0_3_0
  · exact cols_assocABC_eq_0_4_0
  · exact cols_assocABC_eq_0_5_0
  · exact cols_assocABC_eq_0_6_0
  · exact cols_assocABC_eq_0_7_0
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_2_0
  · exact cols_assocABC_eq_1_3_0
  · exact cols_assocABC_eq_1_4_0
  · exact cols_assocABC_eq_1_5_0
  · exact cols_assocABC_eq_1_6_0
  · exact cols_assocABC_eq_1_7_0

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21524818,
    decodeIntegerRow 16 3 1 21497116,
    decodeIntegerRow 16 3 1 21510238,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 2391484,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523342,
    decodeIntegerRow 16 3 1 21523396,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21523684,
    decodeIntegerRow 16 3 1 21523522]

def cols_right0 (r : LeftIndex 3 2 3) : List ℤ := cols_right0Data.getD (leftPosition 3 2 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_4_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_5_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_6_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_7_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_4_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_5_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_6_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_7_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 2 3) : (tripleIndices 2 8 1).map (fun j => (right0Middle3 2 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_2_0
  · exact cols_right0_eq_0_3_0
  · exact cols_right0_eq_0_4_0
  · exact cols_right0_eq_0_5_0
  · exact cols_right0_eq_0_6_0
  · exact cols_right0_eq_0_7_0
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_2_0
  · exact cols_right0_eq_1_3_0
  · exact cols_right0_eq_1_4_0
  · exact cols_right0_eq_1_5_0
  · exact cols_right0_eq_1_6_0
  · exact cols_right0_eq_1_7_0

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523520,
    decodeIntegerRow 16 3 1 21523040,
    decodeIntegerRow 16 3 1 21523524,
    decodeIntegerRow 16 3 1 21523032,
    decodeIntegerRow 16 3 1 20447356,
    decodeIntegerRow 16 3 1 23675368,
    decodeIntegerRow 16 3 1 22573120,
    decodeIntegerRow 16 3 1 19423840,
    decodeIntegerRow 16 3 1 21526312,
    decodeIntegerRow 16 3 1 21521884,
    decodeIntegerRow 16 3 1 21520480,
    decodeIntegerRow 16 3 1 21524800,
    decodeIntegerRow 16 3 1 2627680,
    decodeIntegerRow 16 3 1 30971200,
    decodeIntegerRow 16 3 1 2155288,
    decodeIntegerRow 16 3 1 31207396]

def cols_right1 (r : LeftIndex 3 2 3) : List ℤ := cols_right1Data.getD (leftPosition 3 2 3 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 3 2 3) : (tripleIndices 4 4 1).map (fun j => (right1Middle3 2 3) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_2_0
  · exact cols_right1_eq_0_3_0
  · exact cols_right1_eq_0_4_0
  · exact cols_right1_eq_0_5_0
  · exact cols_right1_eq_0_6_0
  · exact cols_right1_eq_0_7_0
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_2_0
  · exact cols_right1_eq_1_3_0
  · exact cols_right1_eq_1_4_0
  · exact cols_right1_eq_1_5_0
  · exact cols_right1_eq_1_6_0
  · exact cols_right1_eq_1_7_0

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21520444,
    decodeIntegerRow 16 3 1 21521902,
    decodeIntegerRow 16 3 1 21497116,
    decodeIntegerRow 16 3 1 21510238,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 2391484,
    decodeIntegerRow 16 3 1 21523362,
    decodeIntegerRow 16 3 1 21523356,
    decodeIntegerRow 16 3 1 21523378,
    decodeIntegerRow 16 3 1 21523324,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21523036,
    decodeIntegerRow 16 3 1 21523198]

def cols_left0 (r : LeftIndex 3 2 3) : List ℤ := cols_left0Data.getD (leftPosition 3 2 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_4_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_5_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_6_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_7_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_4_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_5_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_6_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_7_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 2 3) : (tripleIndices 2 8 1).map (fun j => (left0Middle3 2 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_2_0
  · exact cols_left0_eq_0_3_0
  · exact cols_left0_eq_0_4_0
  · exact cols_left0_eq_0_5_0
  · exact cols_left0_eq_0_6_0
  · exact cols_left0_eq_0_7_0
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_2_0
  · exact cols_left0_eq_1_3_0
  · exact cols_left0_eq_1_4_0
  · exact cols_left0_eq_1_5_0
  · exact cols_left0_eq_1_6_0
  · exact cols_left0_eq_1_7_0

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523520,
    decodeIntegerRow 16 3 1 21523040,
    decodeIntegerRow 16 3 1 21523524,
    decodeIntegerRow 16 3 1 21523032,
    decodeIntegerRow 16 3 1 20447356,
    decodeIntegerRow 16 3 1 23675368,
    decodeIntegerRow 16 3 1 22573120,
    decodeIntegerRow 16 3 1 19423840,
    decodeIntegerRow 16 3 1 21526312,
    decodeIntegerRow 16 3 1 21521884,
    decodeIntegerRow 16 3 1 21520480,
    decodeIntegerRow 16 3 1 21524800,
    decodeIntegerRow 16 3 1 2627680,
    decodeIntegerRow 16 3 1 30971200,
    decodeIntegerRow 16 3 1 2155288,
    decodeIntegerRow 16 3 1 31207396]

def cols_left1 (r : LeftIndex 3 2 3) : List ℤ := cols_left1Data.getD (leftPosition 3 2 3 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 3 2 3) : (tripleIndices 4 4 1).map (fun j => (left1Middle3 2 3) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_2_0
  · exact cols_left1_eq_0_3_0
  · exact cols_left1_eq_0_4_0
  · exact cols_left1_eq_0_5_0
  · exact cols_left1_eq_0_6_0
  · exact cols_left1_eq_0_7_0
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_2_0
  · exact cols_left1_eq_1_3_0
  · exact cols_left1_eq_1_4_0
  · exact cols_left1_eq_1_5_0
  · exact cols_left1_eq_1_6_0
  · exact cols_left1_eq_1_7_0

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 927639640384960,
    decodeIntegerRow 16 9 4 936676008057280,
    decodeIntegerRow 16 9 4 926510092299832,
    decodeIntegerRow 16 9 4 926510113560712,
    decodeIntegerRow 16 9 4 1750200147042952,
    decodeIntegerRow 16 9 4 1018031211383368,
    decodeIntegerRow 16 9 4 926510094189760,
    decodeIntegerRow 16 9 4 926510094452160,
    decodeIntegerRow 16 9 4 926510094189688,
    decodeIntegerRow 16 9 4 926510094452168,
    decodeIntegerRow 16 9 4 1749949098566080,
    decodeIntegerRow 16 9 4 1018003317108160,
    decodeIntegerRow 16 9 4 926510096551360,
    decodeIntegerRow 16 9 4 926510075296960,
    decodeIntegerRow 16 9 4 925380204093112,
    decodeIntegerRow 16 9 4 916341081430648]

def cols_right2 (r : LeftIndex 3 2 3) : List ℤ := cols_right2Data.getD (leftPosition 3 2 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 2 3) : (tripleIndices 4 4 1).map (fun j => (right2Middle3 2 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_2_0
  · exact cols_right2_eq_0_3_0
  · exact cols_right2_eq_0_4_0
  · exact cols_right2_eq_0_5_0
  · exact cols_right2_eq_0_6_0
  · exact cols_right2_eq_0_7_0
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_2_0
  · exact cols_right2_eq_1_3_0
  · exact cols_right2_eq_1_4_0
  · exact cols_right2_eq_1_5_0
  · exact cols_right2_eq_1_6_0
  · exact cols_right2_eq_1_7_0

theorem product0_eq : HexagonAtoms323.outerABC * HexagonAtoms323.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms323.assocBAC * HexagonAtoms323.innerABC = HexagonAtoms323.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 4 × Fin 1) (n := Fin 2 × Fin 8 × Fin 1) _

theorem product2_eq : HexagonAtoms323.innerRightABC * HexagonAtoms323.assocABC = HexagonAtoms323.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 2 × Fin 8 × Fin 1) _

theorem product3_eq : HexagonAtoms323.inverseACB * right0Middle3 2 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms323.innerACB * right1Middle3 2 3 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms323.assocBAC * left0Middle3 2 3 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms323.innerRightBAC * left1Middle3 2 3 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms323.assocCAB * right2Middle3 2 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn323
