import RMod.BrundanEllis.StackingReferenceHexagonAtoms575
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn575
open Superfusion

theorem assocBCA_alias : HexagonAtoms575.assocBCA = HexagonAtoms575.assocBAC :=
  HexagonAtoms575.assocBCA_eq.symm.trans HexagonAtoms575.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 34278592,
    decodeIntegerRow 16 3 1 17273776,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21470848,
    decodeIntegerRow 16 3 1 21365904,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37465780]

def rows_inverseACB (r : LeftIndex 5 5 7) : List ℤ := rows_inverseACBData.getD (leftPosition 5 5 7 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 5 7) : (tripleIndices 2 4 2).map ((HexagonAtoms575.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 36573820,
    decodeIntegerRow 16 3 1 18253740,
    decodeIntegerRow 16 3 1 27859152,
    decodeIntegerRow 16 3 1 35158096,
    decodeIntegerRow 16 3 1 35156140,
    decodeIntegerRow 16 3 1 15183300,
    decodeIntegerRow 16 3 1 18258224,
    decodeIntegerRow 16 3 1 6471952,
    decodeIntegerRow 16 3 1 27937940,
    decodeIntegerRow 16 3 1 35525500,
    decodeIntegerRow 16 3 1 6814096,
    decodeIntegerRow 16 3 1 24635568,
    decodeIntegerRow 16 3 1 18415740,
    decodeIntegerRow 16 3 1 6813100,
    decodeIntegerRow 16 3 1 7523152,
    decodeIntegerRow 16 3 1 27942096]

def rows_innerACB (r : LeftIndex 5 5 7) : List ℤ := rows_innerACBData.getD (leftPosition 5 5 7 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 5 5 7) : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_0_1
  · exact rows_innerACB_eq_2_1_0
  · exact rows_innerACB_eq_2_1_1
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_0_1
  · exact rows_innerACB_eq_3_1_0
  · exact rows_innerACB_eq_3_1_1

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 37414780,
    decodeIntegerRow 16 3 1 16053420,
    decodeIntegerRow 16 3 1 25580496,
    decodeIntegerRow 16 3 1 34342768,
    decodeIntegerRow 16 3 1 8702380,
    decodeIntegerRow 16 3 1 25575620,
    decodeIntegerRow 16 3 1 16049552,
    decodeIntegerRow 16 3 1 5633296,
    decodeIntegerRow 16 3 1 26682260,
    decodeIntegerRow 16 3 1 37518460,
    decodeIntegerRow 16 3 1 34213168,
    decodeIntegerRow 16 3 1 17077424,
    decodeIntegerRow 16 3 1 17072580,
    decodeIntegerRow 16 3 1 8835220,
    decodeIntegerRow 16 3 1 5527024,
    decodeIntegerRow 16 3 1 26678352]

def rows_assocBAC (r : RightIndex 7 5 5) : List ℤ := rows_assocBACData.getD (rightPosition 7 5 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 7 5 5) : (tripleIndices 2 4 2).map ((HexagonAtoms575.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_1_1
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_1_1

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 36573820,
    decodeIntegerRow 16 3 1 18253740,
    decodeIntegerRow 16 3 1 27859152,
    decodeIntegerRow 16 3 1 35158096,
    decodeIntegerRow 16 3 1 35156140,
    decodeIntegerRow 16 3 1 15183300,
    decodeIntegerRow 16 3 1 18258224,
    decodeIntegerRow 16 3 1 6471952,
    decodeIntegerRow 16 3 1 27937940,
    decodeIntegerRow 16 3 1 35525500,
    decodeIntegerRow 16 3 1 6814096,
    decodeIntegerRow 16 3 1 24635568,
    decodeIntegerRow 16 3 1 18415740,
    decodeIntegerRow 16 3 1 6813100,
    decodeIntegerRow 16 3 1 7523152,
    decodeIntegerRow 16 3 1 27942096]

def rows_innerRightBAC (r : RightIndex 7 5 5) : List ℤ := rows_innerRightBACData.getD (rightPosition 7 5 5 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 7 5 5) : (tripleIndices 4 2 2).map ((HexagonAtoms575.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_0_1
  · exact rows_innerRightBAC_eq_2_1_0
  · exact rows_innerRightBAC_eq_2_1_1
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_0_1
  · exact rows_innerRightBAC_eq_3_1_0
  · exact rows_innerRightBAC_eq_3_1_1

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 19909436,
    decodeIntegerRow 16 3 1 22061608,
    decodeIntegerRow 16 3 1 23137448,
    decodeIntegerRow 16 3 1 20985604,
    decodeIntegerRow 16 3 1 7352320,
    decodeIntegerRow 16 3 1 26249440,
    decodeIntegerRow 16 3 1 7350880,
    decodeIntegerRow 16 3 1 26245120,
    decodeIntegerRow 16 3 1 22048480,
    decodeIntegerRow 16 3 1 23097920,
    decodeIntegerRow 16 3 1 20998720,
    decodeIntegerRow 16 3 1 19948640,
    decodeIntegerRow 16 3 1 26367592,
    decodeIntegerRow 16 3 1 36048676,
    decodeIntegerRow 16 3 1 26363164,
    decodeIntegerRow 16 3 1 36050152]

def rows_assocCAB (r : RightIndex 5 5 7) : List ℤ := rows_assocCABData.getD (rightPosition 5 5 7 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 5 7) : (tripleIndices 4 2 2).map ((HexagonAtoms575.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 21529192,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21530650,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 22054792,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 21346456]

def cols_right0 (r : LeftIndex 5 7 5) : List ℤ := cols_right0Data.getD (leftPosition 5 7 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 7 5) : (tripleIndices 2 4 2).map (fun j => (right0Middle5 7 5) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 36219040,
    decodeIntegerRow 16 3 1 18372000,
    decodeIntegerRow 16 3 1 35510920,
    decodeIntegerRow 16 3 1 15065040,
    decodeIntegerRow 16 3 1 15069632,
    decodeIntegerRow 16 3 1 7534816,
    decodeIntegerRow 16 3 1 24670560,
    decodeIntegerRow 16 3 1 36220960,
    decodeIntegerRow 16 3 1 15227040,
    decodeIntegerRow 16 3 1 7876000,
    decodeIntegerRow 16 3 1 24749240,
    decodeIntegerRow 16 3 1 36588400,
    decodeIntegerRow 16 3 1 6460288,
    decodeIntegerRow 16 3 1 24753504,
    decodeIntegerRow 16 3 1 7876960,
    decodeIntegerRow 16 3 1 27824160]

def cols_right1 (r : LeftIndex 5 7 5) : List ℤ := cols_right1Data.getD (leftPosition 5 7 5 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 5 7 5) : (tripleIndices 4 2 2).map (fun j => (right1Middle5 7 5) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 21529192,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21530650,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 22054792,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 21346456]

def cols_left0 (r : LeftIndex 5 7 5) : List ℤ := cols_left0Data.getD (leftPosition 5 7 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 7 5) : (tripleIndices 2 4 2).map (fun j => (left0Middle5 7 5) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 6827680,
    decodeIntegerRow 16 3 1 24674720,
    decodeIntegerRow 16 3 1 7535800,
    decodeIntegerRow 16 3 1 27981680,
    decodeIntegerRow 16 3 1 27977088,
    decodeIntegerRow 16 3 1 35511904,
    decodeIntegerRow 16 3 1 18376160,
    decodeIntegerRow 16 3 1 6825760,
    decodeIntegerRow 16 3 1 27819680,
    decodeIntegerRow 16 3 1 35170720,
    decodeIntegerRow 16 3 1 18297480,
    decodeIntegerRow 16 3 1 6458320,
    decodeIntegerRow 16 3 1 36586432,
    decodeIntegerRow 16 3 1 18293216,
    decodeIntegerRow 16 3 1 35169760,
    decodeIntegerRow 16 3 1 15222560]

def cols_left1 (r : LeftIndex 5 7 5) : List ℤ := cols_left1Data.getD (leftPosition 5 7 5 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 5 7 5) : (tripleIndices 4 2 2).map (fun j => (left1Middle5 7 5) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 916341081456896,
    decodeIntegerRow 16 9 4 927639984994960,
    decodeIntegerRow 16 9 4 936679107447440,
    decodeIntegerRow 16 9 4 925380204329344,
    decodeIntegerRow 16 9 4 103071092411200,
    decodeIntegerRow 16 9 4 1018003336237120,
    decodeIntegerRow 16 9 4 103071088160320,
    decodeIntegerRow 16 9 4 1018003297979200,
    decodeIntegerRow 16 9 4 927639640621120,
    decodeIntegerRow 16 9 4 936676008031040,
    decodeIntegerRow 16 9 4 925380548703040,
    decodeIntegerRow 16 9 4 916344180768320,
    decodeIntegerRow 16 9 4 1018031230518160,
    decodeIntegerRow 16 9 4 1750200144916864,
    decodeIntegerRow 16 9 4 1018031192248576,
    decodeIntegerRow 16 9 4 1750200149169040]

def cols_right2 (r : LeftIndex 5 7 5) : List ℤ := cols_right2Data.getD (leftPosition 5 7 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 7 5) : (tripleIndices 4 2 2).map (fun j => (right2Middle5 7 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms575.outerABC * HexagonAtoms575.assocABC = HexagonAtoms575.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms575.assocBAC * HexagonAtoms575.innerABC = HexagonAtoms575.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product2_eq : HexagonAtoms575.innerRightABC * HexagonAtoms575.assocABC = HexagonAtoms575.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product3_eq : HexagonAtoms575.inverseACB * right0Middle5 7 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms575.innerACB * right1Middle5 7 5 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms575.assocBAC * left0Middle5 7 5 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms575.innerRightBAC * left1Middle5 7 5 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms575.assocCAB * right2Middle5 7 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn575
