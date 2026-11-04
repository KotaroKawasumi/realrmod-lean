import RMod.BrundanEllis.StackingReferenceHexagonAtoms655
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn655
open Superfusion

theorem innerACB_alias : HexagonAtoms655.innerACB = HexagonAtoms655.innerABC :=
  HexagonAtoms655.innerACB_eq.symm.trans HexagonAtoms655.innerABC_eq

theorem assocCAB_alias : HexagonAtoms655.assocCAB = HexagonAtoms655.assocBAC :=
  HexagonAtoms655.assocCAB_eq.symm.trans HexagonAtoms655.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 20431336,
    decodeIntegerRow 16 3 1 23634508,
    decodeIntegerRow 16 3 1 40773176,
    decodeIntegerRow 16 3 1 30853428,
    decodeIntegerRow 16 3 1 19409224,
    decodeIntegerRow 16 3 1 20437132,
    decodeIntegerRow 16 3 1 30852776,
    decodeIntegerRow 16 3 1 2273228,
    decodeIntegerRow 16 3 1 31325816,
    decodeIntegerRow 16 3 1 2509748,
    decodeIntegerRow 16 3 1 23660824,
    decodeIntegerRow 16 3 1 22562932,
    decodeIntegerRow 16 3 1 2509416,
    decodeIntegerRow 16 3 1 11721548,
    decodeIntegerRow 16 3 1 20489656,
    decodeIntegerRow 16 3 1 23663668]

def rows_innerRightABC (r : RightIndex 6 5 5) : List ℤ := rows_innerRightABCData.getD (rightPosition 6 5 5 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 6 5 5) : (tripleIndices 4 4 1).map ((HexagonAtoms655.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_2_0
  · exact rows_innerRightABC_eq_0_3_0
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_2_0
  · exact rows_innerRightABC_eq_1_3_0
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_1_0
  · exact rows_innerRightABC_eq_2_2_0
  · exact rows_innerRightABC_eq_2_3_0
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_1_0
  · exact rows_innerRightABC_eq_3_2_0
  · exact rows_innerRightABC_eq_3_3_0

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 6997060,
    decodeIntegerRow 16 3 1 26247200,
    decodeIntegerRow 16 3 1 6997552,
    decodeIntegerRow 16 3 1 16799360,
    decodeIntegerRow 16 3 1 19950880,
    decodeIntegerRow 16 3 1 22062100,
    decodeIntegerRow 16 3 1 23100160,
    decodeIntegerRow 16 3 1 22060624,
    decodeIntegerRow 16 3 1 19907140,
    decodeIntegerRow 16 3 1 22047520,
    decodeIntegerRow 16 3 1 23135152,
    decodeIntegerRow 16 3 1 22048960,
    decodeIntegerRow 16 3 1 7351840,
    decodeIntegerRow 16 3 1 26365460,
    decodeIntegerRow 16 3 1 7351360,
    decodeIntegerRow 16 3 1 16681424]

def rows_inverseACB (r : LeftIndex 6 5 5) : List ℤ := rows_inverseACBData.getD (leftPosition 6 5 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 5 5) : (tripleIndices 4 4 1).map ((HexagonAtoms655.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_4_0
  · exact rows_inverseACB_eq_0_5_0
  · exact rows_inverseACB_eq_0_6_0
  · exact rows_inverseACB_eq_0_7_0
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_1_4_0
  · exact rows_inverseACB_eq_1_5_0
  · exact rows_inverseACB_eq_1_6_0
  · exact rows_inverseACB_eq_1_7_0

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 19420960,
    decodeIntegerRow 16 3 1 20448832,
    decodeIntegerRow 16 3 1 20445880,
    decodeIntegerRow 16 3 1 23620000,
    decodeIntegerRow 16 3 1 2627360,
    decodeIntegerRow 16 3 1 31207232,
    decodeIntegerRow 16 3 1 11839160,
    decodeIntegerRow 16 3 1 2628000,
    decodeIntegerRow 16 3 1 2155616,
    decodeIntegerRow 16 3 1 30971360,
    decodeIntegerRow 16 3 1 30971040,
    decodeIntegerRow 16 3 1 40891760,
    decodeIntegerRow 16 3 1 23672416,
    decodeIntegerRow 16 3 1 22574560,
    decodeIntegerRow 16 3 1 20475040,
    decodeIntegerRow 16 3 1 23678320]

def rows_assocBCA (r : RightIndex 5 5 6) : List ℤ := rows_assocBCAData.getD (rightPosition 5 5 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 5 6) : (tripleIndices 4 4 1).map ((HexagonAtoms655.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_2_0
  · exact rows_assocBCA_eq_0_3_0
  · exact rows_assocBCA_eq_0_4_0
  · exact rows_assocBCA_eq_0_5_0
  · exact rows_assocBCA_eq_0_6_0
  · exact rows_assocBCA_eq_0_7_0
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_2_0
  · exact rows_assocBCA_eq_1_3_0
  · exact rows_assocBCA_eq_1_4_0
  · exact rows_assocBCA_eq_1_5_0
  · exact rows_assocBCA_eq_1_6_0
  · exact rows_assocBCA_eq_1_7_0

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21701236,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21503758,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 21462124,
    decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 21529678]

def rows_assocBAC (r : RightIndex 5 6 5) : List ℤ := rows_assocBACData.getD (rightPosition 5 6 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 5 6 5) : (tripleIndices 2 8 1).map ((HexagonAtoms655.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_2_0
  · exact rows_assocBAC_eq_0_3_0
  · exact rows_assocBAC_eq_0_4_0
  · exact rows_assocBAC_eq_0_5_0
  · exact rows_assocBAC_eq_0_6_0
  · exact rows_assocBAC_eq_0_7_0
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_2_0
  · exact rows_assocBAC_eq_1_3_0
  · exact rows_assocBAC_eq_1_4_0
  · exact rows_assocBAC_eq_1_5_0
  · exact rows_assocBAC_eq_1_6_0
  · exact rows_assocBAC_eq_1_7_0

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 6997060,
    decodeIntegerRow 16 3 1 26247200,
    decodeIntegerRow 16 3 1 6997552,
    decodeIntegerRow 16 3 1 16799360,
    decodeIntegerRow 16 3 1 19950880,
    decodeIntegerRow 16 3 1 22062100,
    decodeIntegerRow 16 3 1 23100160,
    decodeIntegerRow 16 3 1 22060624,
    decodeIntegerRow 16 3 1 19907140,
    decodeIntegerRow 16 3 1 22047520,
    decodeIntegerRow 16 3 1 23135152,
    decodeIntegerRow 16 3 1 22048960,
    decodeIntegerRow 16 3 1 7351840,
    decodeIntegerRow 16 3 1 26365460,
    decodeIntegerRow 16 3 1 7351360,
    decodeIntegerRow 16 3 1 16681424]

def cols_assocABC (r : LeftIndex 6 5 5) : List ℤ := cols_assocABCData.getD (leftPosition 6 5 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 5 5) : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms655.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 5 2 79219132512,
    decodeIntegerRow 16 5 2 78250070112,
    decodeIntegerRow 16 5 2 78250320512,
    decodeIntegerRow 16 5 2 73369132512,
    decodeIntegerRow 16 5 2 149418952800,
    decodeIntegerRow 16 5 2 27387700320,
    decodeIntegerRow 16 5 2 125200200320,
    decodeIntegerRow 16 5 2 149418937824,
    decodeIntegerRow 16 5 2 2934577824,
    decodeIntegerRow 16 5 2 125043950304,
    decodeIntegerRow 16 5 2 125043940320,
    decodeIntegerRow 16 5 2 149653327824,
    decodeIntegerRow 16 5 2 79228132512,
    decodeIntegerRow 16 5 2 78244070112,
    decodeIntegerRow 16 5 2 74344070112,
    decodeIntegerRow 16 5 2 79228508112]

def cols_right0 (r : LeftIndex 6 5 5) : List ℤ := cols_right0Data.getD (leftPosition 6 5 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 5 5) : (tripleIndices 4 4 1).map (fun j => (right0Middle6 5 5) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 6997060,
    decodeIntegerRow 16 3 1 26247200,
    decodeIntegerRow 16 3 1 6997552,
    decodeIntegerRow 16 3 1 16799360,
    decodeIntegerRow 16 3 1 19950880,
    decodeIntegerRow 16 3 1 22062100,
    decodeIntegerRow 16 3 1 23100160,
    decodeIntegerRow 16 3 1 22060624,
    decodeIntegerRow 16 3 1 19907140,
    decodeIntegerRow 16 3 1 22047520,
    decodeIntegerRow 16 3 1 23135152,
    decodeIntegerRow 16 3 1 22048960,
    decodeIntegerRow 16 3 1 7351840,
    decodeIntegerRow 16 3 1 26365460,
    decodeIntegerRow 16 3 1 7351360,
    decodeIntegerRow 16 3 1 16681424]

def cols_left0 (r : LeftIndex 6 5 5) : List ℤ := cols_left0Data.getD (leftPosition 6 5 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 5 5) : (tripleIndices 4 4 1).map (fun j => (left0Middle6 5 5) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 17 8 24330870113196995856,
    decodeIntegerRow 16 17 8 24330612062501928448,
    decodeIntegerRow 16 17 8 24330595882016015856,
    decodeIntegerRow 16 17 8 24330594989131090432,
    decodeIntegerRow 16 17 8 22983573325358187504,
    decodeIntegerRow 16 17 8 1431211525754910208,
    decodeIntegerRow 16 17 8 24251359313570186736,
    decodeIntegerRow 16 17 8 24325934959935596288,
    decodeIntegerRow 16 17 8 47229980349911962896,
    decodeIntegerRow 16 17 8 22983573325358266112,
    decodeIntegerRow 16 17 8 24325934959935596016,
    decodeIntegerRow 16 17 8 24409832562096681728,
    decodeIntegerRow 16 17 8 24330612069067347216,
    decodeIntegerRow 16 17 8 24330321762856073728,
    decodeIntegerRow 16 17 8 24330596886537114384,
    decodeIntegerRow 16 17 8 24330595882038733568]

def cols_right2 (r : LeftIndex 6 5 5) : List ℤ := cols_right2Data.getD (leftPosition 6 5 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_4_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_5_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_6_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_7_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_4_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_5_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_6_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_7_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 5 5) : (tripleIndices 2 8 1).map (fun j => (right2Middle6 5 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms655.outerABC * HexagonAtoms655.assocABC = HexagonAtoms655.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 4 × Fin 1) (n := Fin 2 × Fin 8 × Fin 1) _

theorem product1_eq : HexagonAtoms655.assocBAC * HexagonAtoms655.innerABC = HexagonAtoms655.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 2 × Fin 8 × Fin 1) _

theorem product2_eq : HexagonAtoms655.innerRightABC * HexagonAtoms655.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms655.inverseACB * right0Middle6 5 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms655.innerABC * right1Middle6 5 5 = right1Middle6 5 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 2 × Fin 8 × Fin 1) _

theorem product5_eq : HexagonAtoms655.assocBCA * left0Middle6 5 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms655.innerRightBAC * left1Middle6 5 5 = left1Middle6 5 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 2 × Fin 8 × Fin 1) _

theorem product7_eq : HexagonAtoms655.assocBAC * right2Middle6 5 5 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn655
