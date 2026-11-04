import RMod.BrundanEllis.StackingReferenceHexagonAtoms676
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn676
open Superfusion

theorem assocBCA_alias : HexagonAtoms676.assocBCA = HexagonAtoms676.assocBAC :=
  HexagonAtoms676.assocBCA_eq.symm.trans HexagonAtoms676.assocBAC_eq

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 20932654,
    decodeIntegerRow 16 3 1 23294758,
    decodeIntegerRow 16 3 1 26315074,
    decodeIntegerRow 16 3 1 7155498,
    decodeIntegerRow 16 3 1 16749142,
    decodeIntegerRow 16 3 1 35853314,
    decodeIntegerRow 16 3 1 21995482,
    decodeIntegerRow 16 3 1 20106094,
    decodeIntegerRow 16 3 1 26310706,
    decodeIntegerRow 16 3 1 35892678,
    decodeIntegerRow 16 3 1 22113634,
    decodeIntegerRow 16 3 1 23294902,
    decodeIntegerRow 16 3 1 21996022,
    decodeIntegerRow 16 3 1 22940446,
    decodeIntegerRow 16 3 1 26301958,
    decodeIntegerRow 16 3 1 35851854]

def rows_assocBAC (r : RightIndex 7 6 6) : List ℤ := rows_assocBACData.getD (rightPosition 7 6 6 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 7 6 6) : (tripleIndices 1 2 8).map ((HexagonAtoms676.assocBAC) r) = rows_assocBAC r := by
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

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21522416,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21525472,
    decodeIntegerRow 16 3 1 21523872,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525460,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 35301460,
    decodeIntegerRow 16 3 1 36482440,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 36324976]

def rows_innerRightABC (r : RightIndex 6 6 7) : List ℤ := rows_innerRightABCData.getD (rightPosition 6 6 7 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 6 6 7) : (tripleIndices 1 2 8).map ((HexagonAtoms676.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_0_4
  · exact rows_innerRightABC_eq_0_0_5
  · exact rows_innerRightABC_eq_0_0_6
  · exact rows_innerRightABC_eq_0_0_7
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_1_2
  · exact rows_innerRightABC_eq_0_1_3
  · exact rows_innerRightABC_eq_0_1_4
  · exact rows_innerRightABC_eq_0_1_5
  · exact rows_innerRightABC_eq_0_1_6
  · exact rows_innerRightABC_eq_0_1_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562754]

def rows_inverseACB (r : LeftIndex 6 6 7) : List ℤ := rows_inverseACBData.getD (leftPosition 6 6 7 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 6 7) : (tripleIndices 1 2 8).map ((HexagonAtoms676.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21464311]

def rows_innerACB (r : LeftIndex 6 6 7) : List ℤ := rows_innerACBData.getD (leftPosition 6 6 7 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 6 6 7) : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerACB) r) = rows_innerACB r := by
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

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21464311]

def rows_innerRightBAC (r : RightIndex 7 6 6) : List ℤ := rows_innerRightBACData.getD (rightPosition 7 6 6 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 7 6 6) : (tripleIndices 2 1 8).map ((HexagonAtoms676.innerRightBAC) r) = rows_innerRightBAC r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21484480]

def rows_assocCAB (r : RightIndex 6 6 7) : List ℤ := rows_assocCABData.getD (rightPosition 6 6 7 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 6 7) : (tripleIndices 2 1 8).map ((HexagonAtoms676.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_0_1_4
  · exact rows_assocCAB_eq_0_1_5
  · exact rows_assocCAB_eq_0_1_6
  · exact rows_assocCAB_eq_0_1_7

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21522416,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21525472,
    decodeIntegerRow 16 3 1 21523872,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525460,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 35301460,
    decodeIntegerRow 16 3 1 36482440,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 36324976]

def cols_innerABC (r : LeftIndex 6 7 6) : List ℤ := cols_innerABCData.getD (leftPosition 6 7 6 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 6 7 6) : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_0_4
  · exact cols_innerABC_eq_0_0_5
  · exact cols_innerABC_eq_0_0_6
  · exact cols_innerABC_eq_0_0_7
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_1_2
  · exact cols_innerABC_eq_0_1_3
  · exact cols_innerABC_eq_0_1_4
  · exact cols_innerABC_eq_0_1_5
  · exact cols_innerABC_eq_0_1_6
  · exact cols_innerABC_eq_0_1_7

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562754]

def cols_assocABC (r : LeftIndex 6 7 6) : List ℤ := cols_assocABCData.getD (leftPosition 6 7 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 7 6) : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms676.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_0_4
  · exact cols_assocABC_eq_0_0_5
  · exact cols_assocABC_eq_0_0_6
  · exact cols_assocABC_eq_0_0_7
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_0_1_4
  · exact cols_assocABC_eq_0_1_5
  · exact cols_assocABC_eq_0_1_6
  · exact cols_assocABC_eq_0_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 5 2 15278351312,
    decodeIntegerRow 16 5 2 88403476512,
    decodeIntegerRow 16 5 2 73851759072,
    decodeIntegerRow 16 5 2 76786139064,
    decodeIntegerRow 16 5 2 88598476512,
    decodeIntegerRow 16 5 2 15239226312,
    decodeIntegerRow 16 5 2 75809576560,
    decodeIntegerRow 16 5 2 78734571552,
    decodeIntegerRow 16 5 2 88598789112,
    decodeIntegerRow 16 5 2 137348601312,
    decodeIntegerRow 16 5 2 76778326560,
    decodeIntegerRow 16 5 2 78734569072,
    decodeIntegerRow 16 5 2 137309601312,
    decodeIntegerRow 16 5 2 88403164112,
    decodeIntegerRow 16 5 2 73851756552,
    decodeIntegerRow 16 5 2 75801764064]

def cols_right0 (r : LeftIndex 6 7 6) : List ℤ := cols_right0Data.getD (leftPosition 6 7 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 7 6) : (tripleIndices 1 2 8).map (fun j => (right0Middle6 7 6) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_0_1_4
  · exact cols_right0_eq_0_1_5
  · exact cols_right0_eq_0_1_6
  · exact cols_right0_eq_0_1_7

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 9 4 926522491878656,
    decodeIntegerRow 16 9 4 926384742374080,
    decodeIntegerRow 16 9 4 926384398000960,
    decodeIntegerRow 16 9 4 926525591248400,
    decodeIntegerRow 16 9 4 1007849781826816,
    decodeIntegerRow 16 9 4 104075282303680,
    decodeIntegerRow 16 9 4 101815850263360,
    decodeIntegerRow 16 9 4 1028184746717200,
    decodeIntegerRow 16 9 4 926384742374656,
    decodeIntegerRow 16 9 4 926497696967360,
    decodeIntegerRow 16 9 4 926525591242560,
    decodeIntegerRow 16 9 4 926635790851600,
    decodeIntegerRow 16 9 4 104075286082816,
    decodeIntegerRow 16 9 4 845170368813760,
    decodeIntegerRow 16 9 4 1028184708400960,
    decodeIntegerRow 16 9 4 1751204343312400]

def cols_right1 (r : LeftIndex 6 7 6) : List ℤ := cols_right1Data.getD (leftPosition 6 7 6 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 6 7 6) : (tripleIndices 2 1 8).map (fun j => (right1Middle6 7 6) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_0_4
  · exact cols_right1_eq_0_0_5
  · exact cols_right1_eq_0_0_6
  · exact cols_right1_eq_0_0_7
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_1_2
  · exact cols_right1_eq_0_1_3
  · exact cols_right1_eq_0_1_4
  · exact cols_right1_eq_0_1_5
  · exact cols_right1_eq_0_1_6
  · exact cols_right1_eq_0_1_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562754]

def cols_left0 (r : LeftIndex 6 7 6) : List ℤ := cols_left0Data.getD (leftPosition 6 7 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 7 6) : (tripleIndices 1 2 8).map (fun j => (left0Middle6 7 6) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_0_1_4
  · exact cols_left0_eq_0_1_5
  · exact cols_left0_eq_0_1_6
  · exact cols_left0_eq_0_1_7

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 76309570064,
    decodeIntegerRow 16 5 2 76197070272,
    decodeIntegerRow 16 5 2 76195507872,
    decodeIntegerRow 16 5 2 76317383064,
    decodeIntegerRow 16 5 2 86059415312,
    decodeIntegerRow 16 5 2 15747045312,
    decodeIntegerRow 16 5 2 14770545312,
    decodeIntegerRow 16 5 2 90942540312,
    decodeIntegerRow 16 5 2 76197070352,
    decodeIntegerRow 16 5 2 76278320064,
    decodeIntegerRow 16 5 2 76317382560,
    decodeIntegerRow 16 5 2 76392382872,
    decodeIntegerRow 16 5 2 15747095312,
    decodeIntegerRow 16 5 2 66528165312,
    decodeIntegerRow 16 5 2 90942225312,
    decodeIntegerRow 16 5 2 137817420312]

def cols_left1 (r : LeftIndex 6 7 6) : List ℤ := cols_left1Data.getD (leftPosition 6 7 6 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 6 7 6) : (tripleIndices 2 1 8).map (fun j => (left1Middle6 7 6) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_0_4
  · exact cols_left1_eq_0_0_5
  · exact cols_left1_eq_0_0_6
  · exact cols_left1_eq_0_0_7
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_1_2
  · exact cols_left1_eq_0_1_3
  · exact cols_left1_eq_0_1_4
  · exact cols_left1_eq_0_1_5
  · exact cols_left1_eq_0_1_6
  · exact cols_left1_eq_0_1_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 101815847898480,
    decodeIntegerRow 16 9 4 1028184727558720,
    decodeIntegerRow 16 9 4 1007849800932160,
    decodeIntegerRow 16 9 4 104075284190336,
    decodeIntegerRow 16 9 4 926635771693120,
    decodeIntegerRow 16 9 4 926494595244400,
    decodeIntegerRow 16 9 4 926497695080704,
    decodeIntegerRow 16 9 4 926635427371840,
    decodeIntegerRow 16 9 4 1028184727559440,
    decodeIntegerRow 16 9 4 1751204340947520,
    decodeIntegerRow 16 9 4 104075284196160,
    decodeIntegerRow 16 9 4 845170387919104,
    decodeIntegerRow 16 9 4 926494599968320,
    decodeIntegerRow 16 9 4 926384378842480,
    decodeIntegerRow 16 9 4 926635465583104,
    decodeIntegerRow 16 9 4 926522489992000]

def cols_right2 (r : LeftIndex 6 7 6) : List ℤ := cols_right2Data.getD (leftPosition 6 7 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 7 6) : (tripleIndices 2 1 8).map (fun j => (right2Middle6 7 6) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_0_1_4
  · exact cols_right2_eq_0_1_5
  · exact cols_right2_eq_0_1_6
  · exact cols_right2_eq_0_1_7

theorem product0_eq : HexagonAtoms676.outerABC * HexagonAtoms676.assocABC = HexagonAtoms676.assocABC :=
  Matrix.one_mul (m := Fin 1 × Fin 2 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms676.assocBAC * HexagonAtoms676.innerABC = rowColumnMul rows_assocBAC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms676.innerRightABC * HexagonAtoms676.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms676.inverseACB * right0Middle6 7 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms676.innerACB * right1Middle6 7 6 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms676.assocBAC * left0Middle6 7 6 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms676.innerRightBAC * left1Middle6 7 6 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms676.assocCAB * right2Middle6 7 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn676
