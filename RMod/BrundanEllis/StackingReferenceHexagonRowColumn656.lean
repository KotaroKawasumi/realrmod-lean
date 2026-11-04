import RMod.BrundanEllis.StackingReferenceHexagonAtoms656
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn656
open Superfusion

theorem assocBCA_alias : HexagonAtoms656.assocBCA = HexagonAtoms656.assocBAC :=
  HexagonAtoms656.assocBCA_eq.symm.trans HexagonAtoms656.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 5528476,
    decodeIntegerRow 16 3 1 26682728,
    decodeIntegerRow 16 3 1 37414888,
    decodeIntegerRow 16 3 1 16053924,
    decodeIntegerRow 16 3 1 17073048,
    decodeIntegerRow 16 3 1 8835004,
    decodeIntegerRow 16 3 1 25576124,
    decodeIntegerRow 16 3 1 34344232,
    decodeIntegerRow 16 3 1 26997672,
    decodeIntegerRow 16 3 1 37413316,
    decodeIntegerRow 16 3 1 26677884,
    decodeIntegerRow 16 3 1 37519912,
    decodeIntegerRow 16 3 1 34342876,
    decodeIntegerRow 16 3 1 17466728,
    decodeIntegerRow 16 3 1 34212952,
    decodeIntegerRow 16 3 1 17076956]

def rows_inverseACB (r : LeftIndex 6 6 5) : List ℤ := rows_inverseACBData.getD (leftPosition 6 6 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 6 5) : (tripleIndices 2 4 2).map ((HexagonAtoms656.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_2_1
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_3_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_2_1
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_1_3_1

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921]

def rows_innerACB (r : LeftIndex 6 6 5) : List ℤ := rows_innerACBData.getD (leftPosition 6 6 5 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 6 6 5) : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_2_0
  · exact rows_innerACB_eq_0_2_1
  · exact rows_innerACB_eq_0_3_0
  · exact rows_innerACB_eq_0_3_1
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_1_2_0
  · exact rows_innerACB_eq_1_2_1
  · exact rows_innerACB_eq_1_3_0
  · exact rows_innerACB_eq_1_3_1

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 34211716,
    decodeIntegerRow 16 3 1 17073048,
    decodeIntegerRow 16 3 1 8702488,
    decodeIntegerRow 16 3 1 25576124,
    decodeIntegerRow 16 3 1 16363992,
    decodeIntegerRow 16 3 1 5528476,
    decodeIntegerRow 16 3 1 26992796,
    decodeIntegerRow 16 3 1 37414888,
    decodeIntegerRow 16 3 1 17076956,
    decodeIntegerRow 16 3 1 8833768,
    decodeIntegerRow 16 3 1 25579992,
    decodeIntegerRow 16 3 1 34342876,
    decodeIntegerRow 16 3 1 5526808,
    decodeIntegerRow 16 3 1 26677884,
    decodeIntegerRow 16 3 1 37413316,
    decodeIntegerRow 16 3 1 16049048]

def rows_assocBAC (r : RightIndex 5 6 6) : List ℤ := rows_assocBACData.getD (rightPosition 5 6 6 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 5 6 6) : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_2_0
  · exact rows_assocBAC_eq_0_2_1
  · exact rows_assocBAC_eq_0_3_0
  · exact rows_assocBAC_eq_0_3_1
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_2_0
  · exact rows_assocBAC_eq_1_2_1
  · exact rows_assocBAC_eq_1_3_0
  · exact rows_assocBAC_eq_1_3_1

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921]

def rows_innerRightBAC (r : RightIndex 5 6 6) : List ℤ := rows_innerRightBACData.getD (rightPosition 5 6 6 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 5 6 6) : (tripleIndices 2 4 2).map ((HexagonAtoms656.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_2_0
  · exact rows_innerRightBAC_eq_0_2_1
  · exact rows_innerRightBAC_eq_0_3_0
  · exact rows_innerRightBAC_eq_0_3_1
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_1_2_0
  · exact rows_innerRightBAC_eq_1_2_1
  · exact rows_innerRightBAC_eq_1_3_0
  · exact rows_innerRightBAC_eq_1_3_1

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
    decodeIntegerRow 16 3 1 16014072,
    decodeIntegerRow 16 3 1 37532872,
    decodeIntegerRow 16 3 1 16407716,
    decodeIntegerRow 16 3 1 17426876,
    decodeIntegerRow 16 3 1 8717128,
    decodeIntegerRow 16 3 1 25934792,
    decodeIntegerRow 16 3 1 34224676,
    decodeIntegerRow 16 3 1 17116808,
    decodeIntegerRow 16 3 1 8820484,
    decodeIntegerRow 16 3 1 17431716,
    decodeIntegerRow 16 3 1 8715448,
    decodeIntegerRow 16 3 1 37531528,
    decodeIntegerRow 16 3 1 16403844,
    decodeIntegerRow 16 3 1 5646364,
    decodeIntegerRow 16 3 1 27036552]

def rows_assocCAB (r : RightIndex 6 6 5) : List ℤ := rows_assocCABData.getD (rightPosition 6 6 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 6 5) : (tripleIndices 2 4 2).map ((HexagonAtoms656.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 22072288,
    decodeIntegerRow 16 3 1 23111824,
    decodeIntegerRow 16 3 1 26128940,
    decodeIntegerRow 16 3 1 35931400,
    decodeIntegerRow 16 3 1 19921720,
    decodeIntegerRow 16 3 1 22032940,
    decodeIntegerRow 16 3 1 35813296,
    decodeIntegerRow 16 3 1 16563488,
    decodeIntegerRow 16 3 1 7115488,
    decodeIntegerRow 16 3 1 26129424,
    decodeIntegerRow 16 3 1 19936300,
    decodeIntegerRow 16 3 1 22076680,
    decodeIntegerRow 16 3 1 16563000,
    decodeIntegerRow 16 3 1 7233580,
    decodeIntegerRow 16 3 1 22037296,
    decodeIntegerRow 16 3 1 23123488]

def cols_right0 (r : LeftIndex 6 5 6) : List ℤ := cols_right0Data.getD (leftPosition 6 5 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 5 6) : (tripleIndices 2 4 2).map (fun j => (right0Middle6 5 6) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 17718915072,
    decodeIntegerRow 16 5 2 88106295360,
    decodeIntegerRow 16 5 2 134906475072,
    decodeIntegerRow 16 5 2 64669095360,
    decodeIntegerRow 16 5 2 88887532760,
    decodeIntegerRow 16 5 2 139790852552,
    decodeIntegerRow 16 5 2 89090657864,
    decodeIntegerRow 16 5 2 139750228072,
    decodeIntegerRow 16 5 2 63496907864,
    decodeIntegerRow 16 5 2 12837728072,
    decodeIntegerRow 16 5 2 88887857864,
    decodeIntegerRow 16 5 2 139790788072,
    decodeIntegerRow 16 5 2 134906415552,
    decodeIntegerRow 16 5 2 64668795264,
    decodeIntegerRow 16 5 2 134868915072,
    decodeIntegerRow 16 5 2 64481295360]

def cols_right1 (r : LeftIndex 6 5 6) : List ℤ := cols_right1Data.getD (leftPosition 6 5 6 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 6 5 6) : (tripleIndices 2 4 2).map (fun j => (right1Middle6 5 6) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 22072288,
    decodeIntegerRow 16 3 1 23111824,
    decodeIntegerRow 16 3 1 26128940,
    decodeIntegerRow 16 3 1 35931400,
    decodeIntegerRow 16 3 1 19921720,
    decodeIntegerRow 16 3 1 22032940,
    decodeIntegerRow 16 3 1 35813296,
    decodeIntegerRow 16 3 1 16563488,
    decodeIntegerRow 16 3 1 7115488,
    decodeIntegerRow 16 3 1 26129424,
    decodeIntegerRow 16 3 1 19936300,
    decodeIntegerRow 16 3 1 22076680,
    decodeIntegerRow 16 3 1 16563000,
    decodeIntegerRow 16 3 1 7233580,
    decodeIntegerRow 16 3 1 22037296,
    decodeIntegerRow 16 3 1 23123488]

def cols_left0 (r : LeftIndex 6 5 6) : List ℤ := cols_left0Data.getD (leftPosition 6 5 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 5 6) : (tripleIndices 2 4 2).map (fun j => (left0Middle6 5 6) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 34226128,
    decodeIntegerRow 16 3 1 17116304,
    decodeIntegerRow 16 3 1 8715664,
    decodeIntegerRow 16 3 1 25615472,
    decodeIntegerRow 16 3 1 16408220,
    decodeIntegerRow 16 3 1 5513740,
    decodeIntegerRow 16 3 1 16014540,
    decodeIntegerRow 16 3 1 5644900,
    decodeIntegerRow 16 3 1 27037020,
    decodeIntegerRow 16 3 1 37400140,
    decodeIntegerRow 16 3 1 16403340,
    decodeIntegerRow 16 3 1 5515300,
    decodeIntegerRow 16 3 1 8716912,
    decodeIntegerRow 16 3 1 25619376,
    decodeIntegerRow 16 3 1 8821936,
    decodeIntegerRow 16 3 1 25934288]

def cols_left1 (r : LeftIndex 6 5 6) : List ℤ := cols_left1Data.getD (leftPosition 6 5 6 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 6 5 6) : (tripleIndices 2 4 2).map (fun j => (left1Middle6 5 6) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 12837665552,
    decodeIntegerRow 16 5 2 89090670264,
    decodeIntegerRow 16 5 2 12797040072,
    decodeIntegerRow 16 5 2 88887545360,
    decodeIntegerRow 16 5 2 87919107760,
    decodeIntegerRow 16 5 2 134906412552,
    decodeIntegerRow 16 5 2 64481282760,
    decodeIntegerRow 16 5 2 17718977552,
    decodeIntegerRow 16 5 2 88106282760,
    decodeIntegerRow 16 5 2 134868977552,
    decodeIntegerRow 16 5 2 87918782864,
    decodeIntegerRow 16 5 2 134906478072,
    decodeIntegerRow 16 5 2 12797100552,
    decodeIntegerRow 16 5 2 88887845264,
    decodeIntegerRow 16 5 2 139750165552,
    decodeIntegerRow 16 5 2 63496920264]

def cols_right2 (r : LeftIndex 6 5 6) : List ℤ := cols_right2Data.getD (leftPosition 6 5 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 5 6) : (tripleIndices 2 4 2).map (fun j => (right2Middle6 5 6) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms656.outerABC * HexagonAtoms656.assocABC = HexagonAtoms656.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms656.assocBAC * HexagonAtoms656.innerABC = HexagonAtoms656.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product2_eq : HexagonAtoms656.innerRightABC * HexagonAtoms656.assocABC = HexagonAtoms656.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product3_eq : HexagonAtoms656.inverseACB * right0Middle6 5 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms656.innerACB * right1Middle6 5 6 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms656.assocBAC * left0Middle6 5 6 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms656.innerRightBAC * left1Middle6 5 6 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms656.assocCAB * right2Middle6 5 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn656
