import RMod.BrundanEllis.StackingReferenceHexagonAtoms373
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn373
open Superfusion

theorem assocBCA_alias : HexagonAtoms373.assocBCA = HexagonAtoms373.assocBAC :=
  HexagonAtoms373.assocBCA_eq.symm.trans HexagonAtoms373.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 928205880143908,
    decodeIntegerRow 32 3 1 918601824004960,
    decodeIntegerRow 32 3 1 919167456854560,
    decodeIntegerRow 32 3 1 923122052827708,
    decodeIntegerRow 32 3 1 1063868479158308,
    decodeIntegerRow 32 3 1 285938985164320,
    decodeIntegerRow 32 3 1 331755332180320,
    decodeIntegerRow 32 3 1 652079241282108,
    decodeIntegerRow 32 3 1 928203469522996,
    decodeIntegerRow 32 3 1 918602340564640,
    decodeIntegerRow 32 3 1 919166423735200,
    decodeIntegerRow 32 3 1 923119814394004,
    decodeIntegerRow 32 3 1 1063673219231796,
    decodeIntegerRow 32 3 1 285980826577120,
    decodeIntegerRow 32 3 1 331671649354720,
    decodeIntegerRow 32 3 1 651897928493204,
    decodeIntegerRow 32 3 1 1063868479079520,
    decodeIntegerRow 32 3 1 1567081204054948,
    decodeIntegerRow 32 3 1 1521264857012668,
    decodeIntegerRow 32 3 1 652079241439520,
    decodeIntegerRow 32 3 1 928205873762080,
    decodeIntegerRow 32 3 1 934418394608548,
    decodeIntegerRow 32 3 1 933852759630268,
    decodeIntegerRow 32 3 1 923122065578080,
    decodeIntegerRow 32 3 1 1063673219153120,
    decodeIntegerRow 32 3 1 1567039362642124,
    decodeIntegerRow 32 3 1 1521348539838316,
    decodeIntegerRow 32 3 1 651897928650720,
    decodeIntegerRow 32 3 1 928203463150240,
    decodeIntegerRow 32 3 1 934417878046924,
    decodeIntegerRow 32 3 1 933853792753516,
    decodeIntegerRow 32 3 1 923119827152800]

def rows_inverseACB (r : LeftIndex 3 3 7) : List ℤ := rows_inverseACBData.getD (leftPosition 3 3 7 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 3 7) : (tripleIndices 2 2 8).map ((HexagonAtoms373.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 919168045652788,
    decodeIntegerRow 32 3 1 929898732486776,
    decodeIntegerRow 32 3 1 928204413535092,
    decodeIntegerRow 32 3 1 934416916217944,
    decodeIntegerRow 32 3 1 331804143802228,
    decodeIntegerRow 32 3 1 1200989777355256,
    decodeIntegerRow 32 3 1 1063749942268852,
    decodeIntegerRow 32 3 1 1566962659579864,
    decodeIntegerRow 32 3 1 933852143120308,
    decodeIntegerRow 32 3 1 923121456732536,
    decodeIntegerRow 32 3 1 924815775657972,
    decodeIntegerRow 32 3 1 918603272791384,
    decodeIntegerRow 32 3 1 1521216038671348,
    decodeIntegerRow 32 3 1 652030441261816,
    decodeIntegerRow 32 3 1 789270274222132,
    decodeIntegerRow 32 3 1 286057542028504,
    decodeIntegerRow 32 3 1 929899765608024,
    decodeIntegerRow 32 3 1 919165807223308,
    decodeIntegerRow 32 3 1 934419326834296,
    decodeIntegerRow 32 3 1 928204930095692,
    decodeIntegerRow 32 3 1 1201073460176344,
    decodeIntegerRow 32 3 1 331622831014348,
    decodeIntegerRow 32 3 1 1567157919504376,
    decodeIntegerRow 32 3 1 1063791783677452,
    decodeIntegerRow 32 3 1 929899765240664,
    decodeIntegerRow 32 3 1 919165807302028,
    decodeIntegerRow 32 3 1 934419326676856,
    decodeIntegerRow 32 3 1 928204929754572,
    decodeIntegerRow 32 3 1 1201073430420184,
    decodeIntegerRow 32 3 1 331622837390668,
    decodeIntegerRow 32 3 1 1567157906751736,
    decodeIntegerRow 32 3 1 1063791756046732]

def rows_innerACB (r : LeftIndex 3 3 7) : List ℤ := rows_innerACBData.getD (leftPosition 3 3 7 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 3 3 7) : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerACB) r) = rows_innerACB r := by
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

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 781243955833280,
    decodeIntegerRow 32 3 1 287632360265920,
    decodeIntegerRow 32 3 1 328365052152640,
    decodeIntegerRow 32 3 1 1193597276877120,
    decodeIntegerRow 32 3 1 284285040863680,
    decodeIntegerRow 32 3 1 1055764948809920,
    decodeIntegerRow 32 3 1 644555290923840,
    decodeIntegerRow 32 3 1 335059690957120,
    decodeIntegerRow 32 3 1 781438699198056,
    decodeIntegerRow 32 3 1 287676612290584,
    decodeIntegerRow 32 3 1 328283607752272,
    decodeIntegerRow 32 3 1 1193779622789168,
    decodeIntegerRow 32 3 1 284245610062696,
    decodeIntegerRow 32 3 1 1055960725297944,
    decodeIntegerRow 32 3 1 644735570589392,
    decodeIntegerRow 32 3 1 335145612208048,
    decodeIntegerRow 32 3 1 1517874589735360,
    decodeIntegerRow 32 3 1 1208284645737920,
    decodeIntegerRow 32 3 1 1055960695457600,
    decodeIntegerRow 32 3 1 284245616077120,
    decodeIntegerRow 32 3 1 659240593856960,
    decodeIntegerRow 32 3 1 1524736568681920,
    decodeIntegerRow 32 3 1 287676605550400,
    decodeIntegerRow 32 3 1 781438669517120,
    decodeIntegerRow 32 3 1 1517960510994664,
    decodeIntegerRow 32 3 1 1208464925407464,
    decodeIntegerRow 32 3 1 1055764918971408,
    decodeIntegerRow 32 3 1 284285046869008,
    decodeIntegerRow 32 3 1 659422939765224,
    decodeIntegerRow 32 3 1 1524655124290024,
    decodeIntegerRow 32 3 1 287632353516688,
    decodeIntegerRow 32 3 1 781243926150288]

def rows_assocBAC (r : RightIndex 7 3 3) : List ℤ := rows_assocBACData.getD (rightPosition 7 3 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 7 3 3) : (tripleIndices 2 2 8).map ((HexagonAtoms373.assocBAC) r) = rows_assocBAC r := by
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

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 720932729408176,
    decodeIntegerRow 32 3 1 309778002207472,
    decodeIntegerRow 32 3 1 951924883294580,
    decodeIntegerRow 32 3 1 1002754432290340,
    decodeIntegerRow 32 3 1 946841926465776,
    decodeIntegerRow 32 3 1 987505561882672,
    decodeIntegerRow 32 3 1 1132652232541300,
    decodeIntegerRow 32 3 1 1544936505228580,
    decodeIntegerRow 32 3 1 1132087458498736,
    decodeIntegerRow 32 3 1 1543242189479152,
    decodeIntegerRow 32 3 1 901095315137780,
    decodeIntegerRow 32 3 1 850265727819940,
    decodeIntegerRow 32 3 1 906178271940336,
    decodeIntegerRow 32 3 1 865514598306352,
    decodeIntegerRow 32 3 1 720367957491700,
    decodeIntegerRow 32 3 1 308083680079780,
    decodeIntegerRow 32 3 1 951932631702900,
    decodeIntegerRow 32 3 1 850242511327780,
    decodeIntegerRow 32 3 1 720870053382544,
    decodeIntegerRow 32 3 1 1543430214722128,
    decodeIntegerRow 32 3 1 1132715080753780,
    decodeIntegerRow 32 3 1 307895138984740,
    decodeIntegerRow 32 3 1 946848125192144,
    decodeIntegerRow 32 3 1 865496030781328,
    decodeIntegerRow 32 3 1 951932622125300,
    decodeIntegerRow 32 3 1 850242482594980,
    decodeIntegerRow 32 3 1 720870054327184,
    decodeIntegerRow 32 3 1 1543430217556048,
    decodeIntegerRow 32 3 1 1132715079572980,
    decodeIntegerRow 32 3 1 307895135442340,
    decodeIntegerRow 32 3 1 946848115640784,
    decodeIntegerRow 32 3 1 865496002127248]

def rows_innerRightBAC (r : RightIndex 7 3 3) : List ℤ := rows_innerRightBACData.getD (rightPosition 7 3 3 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 7 3 3) : (tripleIndices 4 1 8).map ((HexagonAtoms373.innerRightBAC) r) = rows_innerRightBAC r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 919168059507520,
    decodeIntegerRow 32 3 1 929898738679360,
    decodeIntegerRow 32 3 1 928204416552640,
    decodeIntegerRow 32 3 1 934416901261120,
    decodeIntegerRow 32 3 1 331804147161920,
    decodeIntegerRow 32 3 1 1200989762551360,
    decodeIntegerRow 32 3 1 1063749928488640,
    decodeIntegerRow 32 3 1 1566962653017920,
    decodeIntegerRow 32 3 1 924815255737576,
    decodeIntegerRow 32 3 1 934419311872960,
    decodeIntegerRow 32 3 1 933854367769600,
    decodeIntegerRow 32 3 1 929899771802608,
    decodeIntegerRow 32 3 1 789228418950376,
    decodeIntegerRow 32 3 1 1567157912944320,
    decodeIntegerRow 32 3 1 1521397354478720,
    decodeIntegerRow 32 3 1 1201073445377008,
    decodeIntegerRow 32 3 1 1521216042031040,
    decodeIntegerRow 32 3 1 1200989762393920,
    decodeIntegerRow 32 3 1 1063749928409920,
    decodeIntegerRow 32 3 1 286057535466560,
    decodeIntegerRow 32 3 1 933852156975040,
    decodeIntegerRow 32 3 1 929898725926720,
    decodeIntegerRow 32 3 1 928204410176320,
    decodeIntegerRow 32 3 1 918603257834560,
    decodeIntegerRow 32 3 1 789228419029120,
    decodeIntegerRow 32 3 1 285862275540048,
    decodeIntegerRow 32 3 1 331622834031896,
    decodeIntegerRow 32 3 1 1201073445219520,
    decodeIntegerRow 32 3 1 924815262115840,
    decodeIntegerRow 32 3 1 918600847213648,
    decodeIntegerRow 32 3 1 919165793443096,
    decodeIntegerRow 32 3 1 929899759046080]

def rows_assocCAB (r : RightIndex 3 3 7) : List ℤ := rows_assocCABData.getD (rightPosition 3 3 7 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 3 7) : (tripleIndices 4 1 8).map ((HexagonAtoms373.assocCAB) r) = rows_assocCAB r := by
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
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_1_1_4
  · exact rows_assocCAB_eq_1_1_5
  · exact rows_assocCAB_eq_1_1_6
  · exact rows_assocCAB_eq_1_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 926511256687468,
    decodeIntegerRow 32 3 1 926509707005188,
    decodeIntegerRow 32 3 1 926510223565354,
    decodeIntegerRow 32 3 1 926510051381386,
    decodeIntegerRow 32 3 1 926604237604748,
    decodeIntegerRow 32 3 1 926478713366308,
    decodeIntegerRow 32 3 1 926520554779114,
    decodeIntegerRow 32 3 1 926506607641546,
    decodeIntegerRow 32 3 1 1132401226500886,
    decodeIntegerRow 32 3 1 1544183490703306,
    decodeIntegerRow 32 3 1 903633301793812,
    decodeIntegerRow 32 3 1 857879717001988,
    decodeIntegerRow 32 3 1 929051958659926,
    decodeIntegerRow 32 3 1 934135691379466,
    decodeIntegerRow 32 3 1 926227650540532,
    decodeIntegerRow 32 3 1 925662801033508,
    decodeIntegerRow 32 3 1 926506607641492,
    decodeIntegerRow 32 3 1 926520554779132,
    decodeIntegerRow 32 3 1 926541475485526,
    decodeIntegerRow 32 3 1 926415951247094,
    decodeIntegerRow 32 3 1 926510051377012,
    decodeIntegerRow 32 3 1 926510223566812,
    decodeIntegerRow 32 3 1 926510481846166,
    decodeIntegerRow 32 3 1 926508932164534,
    decodeIntegerRow 32 3 1 927357378252394,
    decodeIntegerRow 32 3 1 926792509613494,
    decodeIntegerRow 32 3 1 934135692442348,
    decodeIntegerRow 32 3 1 929051961848572,
    decodeIntegerRow 32 3 1 995140471731754,
    decodeIntegerRow 32 3 1 949386886703734,
    decodeIntegerRow 32 3 1 1544183490716428,
    decodeIntegerRow 32 3 1 1132401226540252]

def cols_right0 (r : LeftIndex 3 7 3) : List ℤ := cols_right0Data.getD (leftPosition 3 7 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 7 3) : (tripleIndices 2 2 8).map (fun j => (right0Middle3 7 3) j r) = cols_right0 r := by
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
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_1_1_4
  · exact cols_right0_eq_1_1_5
  · exact cols_right0_eq_1_1_6
  · exact cols_right0_eq_1_1_7

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 32 5 2 2328330278396605664064,
    decodeIntegerRow 32 5 2 9778891801834102539072,
    decodeIntegerRow 32 5 2 12014060258865336914112,
    decodeIntegerRow 32 5 2 11716037797927758789312,
    decodeIntegerRow 32 5 2 11626631059646118165312,
    decodeIntegerRow 32 5 2 11638551958081665045312,
    decodeIntegerRow 32 5 2 11642128227603149445312,
    decodeIntegerRow 32 5 2 11641651391616821445312,
    decodeIntegerRow 32 5 2 11626630983353149415312,
    decodeIntegerRow 32 5 2 11644512422559204095312,
    decodeIntegerRow 32 5 2 11640936134707641570312,
    decodeIntegerRow 32 5 2 11641651392349243320312,
    decodeIntegerRow 32 5 2 2328282594680786914064,
    decodeIntegerRow 32 5 2 13504182100296016601552,
    decodeIntegerRow 32 5 2 11269002199172954101512,
    decodeIntegerRow 32 5 2 11716038179397680664312,
    decodeIntegerRow 32 5 2 11626631059647094725312,
    decodeIntegerRow 32 5 2 11644512407300415045312,
    decodeIntegerRow 32 5 2 11640936137759399445312,
    decodeIntegerRow 32 5 2 11641651391738891445312,
    decodeIntegerRow 32 5 2 2328330278396607226560,
    decodeIntegerRow 32 5 2 13504172563552852539072,
    decodeIntegerRow 32 5 2 11269004106521586914112,
    decodeIntegerRow 32 5 2 11716037797927954101312,
    decodeIntegerRow 32 5 2 2328282594680785351560,
    decodeIntegerRow 32 5 2 9778882265090938476552,
    decodeIntegerRow 32 5 2 12014062166213969726512,
    decodeIntegerRow 32 5 2 11716038179397485351312,
    decodeIntegerRow 32 5 2 11626630983352172850312,
    decodeIntegerRow 32 5 2 11638551942822875970312,
    decodeIntegerRow 32 5 2 11642128230654907195312,
    decodeIntegerRow 32 5 2 11641651392227172695312]

def cols_right1 (r : LeftIndex 3 7 3) : List ℤ := cols_right1Data.getD (leftPosition 3 7 3 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 3 7 3) : (tripleIndices 4 1 8).map (fun j => (right1Middle3 7 3) j r) = cols_right1 r := by
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
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_0_4
  · exact cols_right1_eq_1_0_5
  · exact cols_right1_eq_1_0_6
  · exact cols_right1_eq_1_0_7
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_1_1
  · exact cols_right1_eq_1_1_2
  · exact cols_right1_eq_1_1_3
  · exact cols_right1_eq_1_1_4
  · exact cols_right1_eq_1_1_5
  · exact cols_right1_eq_1_1_6
  · exact cols_right1_eq_1_1_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 926511256687468,
    decodeIntegerRow 32 3 1 926509707005188,
    decodeIntegerRow 32 3 1 926510223565354,
    decodeIntegerRow 32 3 1 926510051381386,
    decodeIntegerRow 32 3 1 926604237604748,
    decodeIntegerRow 32 3 1 926478713366308,
    decodeIntegerRow 32 3 1 926520554779114,
    decodeIntegerRow 32 3 1 926506607641546,
    decodeIntegerRow 32 3 1 1132401226500886,
    decodeIntegerRow 32 3 1 1544183490703306,
    decodeIntegerRow 32 3 1 903633301793812,
    decodeIntegerRow 32 3 1 857879717001988,
    decodeIntegerRow 32 3 1 929051958659926,
    decodeIntegerRow 32 3 1 934135691379466,
    decodeIntegerRow 32 3 1 926227650540532,
    decodeIntegerRow 32 3 1 925662801033508,
    decodeIntegerRow 32 3 1 926506607641492,
    decodeIntegerRow 32 3 1 926520554779132,
    decodeIntegerRow 32 3 1 926541475485526,
    decodeIntegerRow 32 3 1 926415951247094,
    decodeIntegerRow 32 3 1 926510051377012,
    decodeIntegerRow 32 3 1 926510223566812,
    decodeIntegerRow 32 3 1 926510481846166,
    decodeIntegerRow 32 3 1 926508932164534,
    decodeIntegerRow 32 3 1 927357378252394,
    decodeIntegerRow 32 3 1 926792509613494,
    decodeIntegerRow 32 3 1 934135692442348,
    decodeIntegerRow 32 3 1 929051961848572,
    decodeIntegerRow 32 3 1 995140471731754,
    decodeIntegerRow 32 3 1 949386886703734,
    decodeIntegerRow 32 3 1 1544183490716428,
    decodeIntegerRow 32 3 1 1132401226540252]

def cols_left0 (r : LeftIndex 3 7 3) : List ℤ := cols_left0Data.getD (leftPosition 3 7 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 7 3) : (tripleIndices 2 2 8).map (fun j => (left0Middle3 7 3) j r) = cols_left0 r := by
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
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_1_1_4
  · exact cols_left0_eq_1_1_5
  · exact cols_left0_eq_1_1_6
  · exact cols_left0_eq_1_1_7

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 32 3 1 282668901131840,
    decodeIntegerRow 32 3 1 796612323935680,
    decodeIntegerRow 32 3 1 1193082954535360,
    decodeIntegerRow 32 3 1 330109821492800,
    decodeIntegerRow 32 3 1 644123618520640,
    decodeIntegerRow 32 3 1 1519521716729280,
    decodeIntegerRow 32 3 1 289446170509760,
    decodeIntegerRow 32 3 1 781928196712000,
    decodeIntegerRow 32 3 1 644037497364976,
    decodeIntegerRow 32 3 1 333317663507192,
    decodeIntegerRow 32 3 1 1563768239111112,
    decodeIntegerRow 32 3 1 781884146787856,
    decodeIntegerRow 32 3 1 282472601365616,
    decodeIntegerRow 32 3 1 1056447497502712,
    decodeIntegerRow 32 3 1 659855989663432,
    decodeIntegerRow 32 3 1 329928005265296,
    decodeIntegerRow 32 3 1 644123590811200,
    decodeIntegerRow 32 3 1 333498459737280,
    decodeIntegerRow 32 3 1 1563574012306880,
    decodeIntegerRow 32 3 1 781928226625600,
    decodeIntegerRow 32 3 1 282668894414400,
    decodeIntegerRow 32 3 1 1056407894514880,
    decodeIntegerRow 32 3 1 659937261868480,
    decodeIntegerRow 32 3 1 330109834612800,
    decodeIntegerRow 32 3 1 282472608085104,
    decodeIntegerRow 32 3 1 796572720956872,
    decodeIntegerRow 32 3 1 1193164226748808,
    decodeIntegerRow 32 3 1 329927992141296,
    decodeIntegerRow 32 3 1 644037525082864,
    decodeIntegerRow 32 3 1 1519702512955592,
    decodeIntegerRow 32 3 1 289251943703688,
    decodeIntegerRow 32 3 1 781884116865136]

def cols_left1 (r : LeftIndex 3 7 3) : List ℤ := cols_left1Data.getD (leftPosition 3 7 3 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 3 7 3) : (tripleIndices 4 1 8).map (fun j => (left1Middle3 7 3) j r) = cols_left1 r := by
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
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_0_4
  · exact cols_left1_eq_1_0_5
  · exact cols_left1_eq_1_0_6
  · exact cols_left1_eq_1_0_7
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_1_1
  · exact cols_left1_eq_1_1_2
  · exact cols_left1_eq_1_1_3
  · exact cols_left1_eq_1_1_4
  · exact cols_left1_eq_1_1_5
  · exact cols_left1_eq_1_1_6
  · exact cols_left1_eq_1_1_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1716609630269413206804930125440,
    decodeIntegerRow 32 9 4 1716870626065096930839119463040,
    decodeIntegerRow 32 9 4 1716864882881328793137080479360,
    decodeIntegerRow 32 9 4 1717074828154629066412050816640,
    decodeIntegerRow 32 9 4 192853638173704174862307712640,
    decodeIntegerRow 32 9 4 1905247053659346470480791143040,
    decodeIntegerRow 32 9 4 1867566024956728424850417823360,
    decodeIntegerRow 32 9 4 3245016963085765870420449664640,
    decodeIntegerRow 32 9 4 1716818937410116351891986170368,
    decodeIntegerRow 32 9 4 1717074828165450704314907251840,
    decodeIntegerRow 32 9 4 1717074190033891267432753874560,
    decodeIntegerRow 32 9 4 1716870626066431105375097512480,
    decodeIntegerRow 32 9 4 1566117788332968755390640275968,
    decodeIntegerRow 32 9 4 3245017034086532151312913856640,
    decodeIntegerRow 32 9 4 3240830252925051943343094707840,
    decodeIntegerRow 32 9 4 1905247062412865601001779880480,
    decodeIntegerRow 32 9 4 3240830182118808310046245473920,
    decodeIntegerRow 32 9 4 1905247053659346470449797504640,
    decodeIntegerRow 32 9 4 1867566024956728424825622912640,
    decodeIntegerRow 32 9 4 188666857206746613986006579840,
    decodeIntegerRow 32 9 4 1717074190023100922722501217920,
    decodeIntegerRow 32 9 4 1716870626065096727489857920640,
    decodeIntegerRow 32 9 4 1716864882881328630457671245440,
    decodeIntegerRow 32 9 4 1716608992137881768857343539840,
    decodeIntegerRow 32 9 4 1566117788332968755415435187840,
    decodeIntegerRow 32 9 4 188666786205980333093542376160,
    decodeIntegerRow 32 9 4 192853567367460541064050272512,
    decodeIntegerRow 32 9 4 1905247062412865600970786240640,
    decodeIntegerRow 32 9 4 1716818937410116514571402962560,
    decodeIntegerRow 32 9 4 1716608992127060130954410472160,
    decodeIntegerRow 32 9 4 1716609630258619572355436538112,
    decodeIntegerRow 32 9 4 1716870626066430902025826522240]

def cols_right2 (r : LeftIndex 3 7 3) : List ℤ := cols_right2Data.getD (leftPosition 3 7 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 7 3) : (tripleIndices 4 1 8).map (fun j => (right2Middle3 7 3) j r) = cols_right2 r := by
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
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_1_1_4
  · exact cols_right2_eq_1_1_5
  · exact cols_right2_eq_1_1_6
  · exact cols_right2_eq_1_1_7

theorem product0_eq : HexagonAtoms373.outerABC * HexagonAtoms373.assocABC = HexagonAtoms373.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms373.assocBAC * HexagonAtoms373.innerABC = HexagonAtoms373.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms373.innerRightABC * HexagonAtoms373.assocABC = HexagonAtoms373.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms373.inverseACB * right0Middle3 7 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms373.innerACB * right1Middle3 7 3 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms373.assocBAC * left0Middle3 7 3 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms373.innerRightBAC * left1Middle3 7 3 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms373.assocCAB * right2Middle3 7 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn373
