import RMod.BrundanEllis.StackingReferenceHexagonAtoms565
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn565
open Superfusion

theorem assocBCA_alias : HexagonAtoms565.assocBCA = HexagonAtoms565.assocBAC :=
  HexagonAtoms565.assocBCA_eq.symm.trans HexagonAtoms565.assocBAC_eq

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def rows_outerABC (r : LeftIndex 6 5 5) : List ℤ := rows_outerABCData.getD (leftPosition 6 5 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 6 5 5) : (tripleIndices 2 8 1).map ((HexagonAtoms565.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21666568,
    decodeIntegerRow 16 3 1 21743356,
    decodeIntegerRow 16 3 1 41718152,
    decodeIntegerRow 16 3 1 28963556,
    decodeIntegerRow 16 3 1 21749512,
    decodeIntegerRow 16 3 1 21668836,
    decodeIntegerRow 16 3 1 28963512,
    decodeIntegerRow 16 3 1 41718084,
    decodeIntegerRow 16 3 1 33215048,
    decodeIntegerRow 16 3 1 39592316,
    decodeIntegerRow 16 3 1 21775432,
    decodeIntegerRow 16 3 1 21616996,
    decodeIntegerRow 16 3 1 39592392,
    decodeIntegerRow 16 3 1 33215076,
    decodeIntegerRow 16 3 1 21613432,
    decodeIntegerRow 16 3 1 21769924]

def rows_inverseACB (r : LeftIndex 5 5 6) : List ℤ := rows_inverseACBData.getD (leftPosition 5 5 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_inverseACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 5 6) : (tripleIndices 2 8 1).map ((HexagonAtoms565.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 20431336,
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

def rows_innerACB (r : LeftIndex 5 5 6) : List ℤ := rows_innerACBData.getD (leftPosition 5 5 6 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 5 5 6) : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerACB) r) = rows_innerACB r := by
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

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 37466620,
    decodeIntegerRow 16 3 1 25774896,
    decodeIntegerRow 16 3 1 21363952,
    decodeIntegerRow 16 3 1 21456940,
    decodeIntegerRow 16 3 1 37466560,
    decodeIntegerRow 16 3 1 17271840,
    decodeIntegerRow 16 3 1 21678880,
    decodeIntegerRow 16 3 1 21458560,
    decodeIntegerRow 16 3 1 21328960,
    decodeIntegerRow 16 3 1 21575200,
    decodeIntegerRow 16 3 1 8768800,
    decodeIntegerRow 16 3 1 26837760,
    decodeIntegerRow 16 3 1 21722620,
    decodeIntegerRow 16 3 1 21576496,
    decodeIntegerRow 16 3 1 8768752,
    decodeIntegerRow 16 3 1 16208940]

def rows_assocBAC (r : RightIndex 6 5 5) : List ℤ := rows_assocBACData.getD (rightPosition 6 5 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocBAC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 6 5 5) : (tripleIndices 2 8 1).map ((HexagonAtoms565.assocBAC) r) = rows_assocBAC r := by
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

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 20431336,
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

def rows_innerRightBAC (r : RightIndex 6 5 5) : List ℤ := rows_innerRightBACData.getD (rightPosition 6 5 5 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_innerRightBAC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 6 5 5) : (tripleIndices 4 4 1).map ((HexagonAtoms565.innerRightBAC) r) = rows_innerRightBAC r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 19420960,
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

def rows_assocCAB (r : RightIndex 5 5 6) : List ℤ := rows_assocCABData.getD (rightPosition 5 5 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 5 6) : (tripleIndices 4 4 1).map ((HexagonAtoms565.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991916,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 23117684,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21516556]

def cols_assocABC (r : LeftIndex 5 6 5) : List ℤ := cols_assocABCData.getD (leftPosition 5 6 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_4_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_5_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_6_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_7_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_assocABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_4_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_5_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_6_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_7_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_assocABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 6 5) : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms565.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991916,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 23117684,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21516556]

def cols_right0 (r : LeftIndex 5 6 5) : List ℤ := cols_right0Data.getD (leftPosition 5 6 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_4_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_5_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_6_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_7_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right0 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_4_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_5_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_6_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_7_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right0 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 6 5) : (tripleIndices 2 8 1).map (fun j => (right0Middle5 6 5) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 137426764072,
    decodeIntegerRow 16 5 2 64106446560,
    decodeIntegerRow 16 5 2 137426751552,
    decodeIntegerRow 16 5 2 88481446560,
    decodeIntegerRow 16 5 2 78731289312,
    decodeIntegerRow 16 5 2 75804851512,
    decodeIntegerRow 16 5 2 73856289312,
    decodeIntegerRow 16 5 2 75804914112,
    decodeIntegerRow 16 5 2 78739414312,
    decodeIntegerRow 16 5 2 75806476512,
    decodeIntegerRow 16 5 2 73848789312,
    decodeIntegerRow 16 5 2 75806414112,
    decodeIntegerRow 16 5 2 137231439072,
    decodeIntegerRow 16 5 2 64067381560,
    decodeIntegerRow 16 5 2 137231451552,
    decodeIntegerRow 16 5 2 88520506560]

def cols_right1 (r : LeftIndex 5 6 5) : List ℤ := cols_right1Data.getD (leftPosition 5 6 5 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right1 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right1 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 5 6 5) : (tripleIndices 4 4 1).map (fun j => (right1Middle5 6 5) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21466498,
    decodeIntegerRow 16 3 1 21530164,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 26306356,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 23117684,
    decodeIntegerRow 16 3 1 22054798,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 21462124,
    decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 21529678]

def cols_left0 (r : LeftIndex 5 6 5) : List ℤ := cols_left0Data.getD (leftPosition 5 6 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_4_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_5_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_6_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_7_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left0 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_4_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_5_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_6_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_7_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left0 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 6 5) : (tripleIndices 2 8 1).map (fun j => (left0Middle5 6 5) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 6997060,
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

def cols_left1 (r : LeftIndex 5 6 5) : List ℤ := cols_left1Data.getD (leftPosition 5 6 5 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left1 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_left1 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 5 6 5) : (tripleIndices 4 4 1).map (fun j => (left1Middle5 6 5) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 915214613581120,
    decodeIntegerRow 16 9 4 917470988772160,
    decodeIntegerRow 16 9 4 917470954754752,
    decodeIntegerRow 16 9 4 937805532761920,
    decodeIntegerRow 16 9 4 11577867341120,
    decodeIntegerRow 16 9 4 1658679029875520,
    decodeIntegerRow 16 9 4 194341158556352,
    decodeIntegerRow 16 9 4 11577867865920,
    decodeIntegerRow 16 9 4 1841721263737920,
    decodeIntegerRow 16 9 4 194564312758080,
    decodeIntegerRow 16 9 4 194564313177920,
    decodeIntegerRow 16 9 4 11298924588960,
    decodeIntegerRow 16 9 4 915211212358720,
    decodeIntegerRow 16 9 4 917473709750080,
    decodeIntegerRow 16 9 4 935546445094720,
    decodeIntegerRow 16 9 4 915211169836960]

def cols_right2 (r : LeftIndex 5 6 5) : List ℤ := cols_right2Data.getD (leftPosition 5 6 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_4_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_5_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_6_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_7_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right2 ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_4_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_5_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_6_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_7_0 : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = cols_right2 ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 6 5) : (tripleIndices 4 4 1).map (fun j => (right2Middle5 6 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms565.outerABC * HexagonAtoms565.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms565.assocBAC * HexagonAtoms565.innerABC = HexagonAtoms565.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 4 × Fin 1) (n := Fin 2 × Fin 8 × Fin 1) _

theorem product2_eq : HexagonAtoms565.innerRightABC * HexagonAtoms565.assocABC = HexagonAtoms565.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 2 × Fin 8 × Fin 1) _

theorem product3_eq : HexagonAtoms565.inverseACB * right0Middle5 6 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms565.innerACB * right1Middle5 6 5 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms565.assocBAC * left0Middle5 6 5 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms565.innerRightBAC * left1Middle5 6 5 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms565.assocCAB * right2Middle5 6 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn565
