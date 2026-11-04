import RMod.BrundanEllis.StackingReferenceHexagonAtoms343
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn343
open Superfusion

theorem assocBCA_alias : HexagonAtoms343.assocBCA = HexagonAtoms343.assocBAC :=
  HexagonAtoms343.assocBCA_eq.symm.trans HexagonAtoms343.assocBAC_eq

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

def rows_outerABC (r : LeftIndex 4 3 3) : List ℤ := rows_outerABCData.getD (leftPosition 4 3 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 4 3 3) : (tripleIndices 4 2 4).map ((HexagonAtoms343.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 308840184932908,
    decodeIntegerRow 32 3 1 720629422704148,
    decodeIntegerRow 32 3 1 995171852909464,
    decodeIntegerRow 32 3 1 949481030236856,
    decodeIntegerRow 32 3 1 1132390766187040,
    decodeIntegerRow 32 3 1 308840184919840,
    decodeIntegerRow 32 3 1 903539158969280,
    decodeIntegerRow 32 3 1 995171852791360,
    decodeIntegerRow 32 3 1 1544186977487680,
    decodeIntegerRow 32 3 1 1132411686854080,
    decodeIntegerRow 32 3 1 857911098061600,
    decodeIntegerRow 32 3 1 903727444972640,
    decodeIntegerRow 32 3 1 1132411686893464,
    decodeIntegerRow 32 3 1 308833211350984,
    decodeIntegerRow 32 3 1 903727445326932,
    decodeIntegerRow 32 3 1 995109090672148,
    decodeIntegerRow 32 3 1 926791376049760,
    decodeIntegerRow 32 3 1 927357000397600,
    decodeIntegerRow 32 3 1 929052087799360,
    decodeIntegerRow 32 3 1 934135734424000,
    decodeIntegerRow 32 3 1 927356990832148,
    decodeIntegerRow 32 3 1 926228841499732,
    decodeIntegerRow 32 3 1 934135735491256,
    decodeIntegerRow 32 3 1 923968097862376,
    decodeIntegerRow 32 3 1 926226488278984,
    decodeIntegerRow 32 3 1 925662413612776,
    decodeIntegerRow 32 3 1 923968359331348,
    decodeIntegerRow 32 3 1 918884540516908,
    decodeIntegerRow 32 3 1 927357765672640,
    decodeIntegerRow 32 3 1 926226516976960,
    decodeIntegerRow 32 3 1 934135649393440,
    decodeIntegerRow 32 3 1 923968356144160]

def rows_inverseACB (r : LeftIndex 3 3 4) : List ℤ := rows_inverseACBData.getD (leftPosition 3 3 4 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 3 4) : (tripleIndices 4 2 4).map ((HexagonAtoms343.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_1_2
  · exact rows_inverseACB_eq_2_1_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_1_2
  · exact rows_inverseACB_eq_3_1_3

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 919168030809544,
    decodeIntegerRow 32 3 1 924815769109096,
    decodeIntegerRow 32 3 1 929898729113908,
    decodeIntegerRow 32 3 1 934416902319628,
    decodeIntegerRow 32 3 1 1566962653372212,
    decodeIntegerRow 32 3 1 1200989762512012,
    decodeIntegerRow 32 3 1 1063749928370536,
    decodeIntegerRow 32 3 1 1521216041676744,
    decodeIntegerRow 32 3 1 933852128277064,
    decodeIntegerRow 32 3 1 928204406986216,
    decodeIntegerRow 32 3 1 923121453359668,
    decodeIntegerRow 32 3 1 918603258893068,
    decodeIntegerRow 32 3 1 286057535820852,
    decodeIntegerRow 32 3 1 652030426418572,
    decodeIntegerRow 32 3 1 789270260323816,
    decodeIntegerRow 32 3 1 331804146807624,
    decodeIntegerRow 32 3 1 331622834386188,
    decodeIntegerRow 32 3 1 789228419068468,
    decodeIntegerRow 32 3 1 1201073445337624,
    decodeIntegerRow 32 3 1 1567157913298616,
    decodeIntegerRow 32 3 1 934419312940216,
    decodeIntegerRow 32 3 1 929899762236184,
    decodeIntegerRow 32 3 1 928204936301452,
    decodeIntegerRow 32 3 1 933854396467252,
    decodeIntegerRow 32 3 1 331622834018828,
    decodeIntegerRow 32 3 1 789228418911028,
    decodeIntegerRow 32 3 1 1201073445258904,
    decodeIntegerRow 32 3 1 1567157912957496,
    decodeIntegerRow 32 3 1 934419340570936,
    decodeIntegerRow 32 3 1 929899768612504,
    decodeIntegerRow 32 3 1 928204923548812,
    decodeIntegerRow 32 3 1 933854366711092]

def rows_innerACB (r : LeftIndex 3 3 4) : List ℤ := rows_innerACBData.getD (leftPosition 3 3 4 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 3 3 4) : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_1_2
  · exact rows_innerACB_eq_0_1_3
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_0_2
  · exact rows_innerACB_eq_1_0_3
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_1_1_2
  · exact rows_innerACB_eq_1_1_3
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_0_1
  · exact rows_innerACB_eq_2_0_2
  · exact rows_innerACB_eq_2_0_3
  · exact rows_innerACB_eq_2_1_0
  · exact rows_innerACB_eq_2_1_1
  · exact rows_innerACB_eq_2_1_2
  · exact rows_innerACB_eq_2_1_3
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_0_1
  · exact rows_innerACB_eq_3_0_2
  · exact rows_innerACB_eq_3_0_3
  · exact rows_innerACB_eq_3_1_0
  · exact rows_innerACB_eq_3_1_1
  · exact rows_innerACB_eq_3_1_2
  · exact rows_innerACB_eq_3_1_3

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 659331767755876,
    decodeIntegerRow 32 3 1 1568754866931592,
    decodeIntegerRow 32 3 1 328324339531516,
    decodeIntegerRow 32 3 1 1055862835872952,
    decodeIntegerRow 32 3 1 926601267380484,
    decodeIntegerRow 32 3 1 926529809826232,
    decodeIntegerRow 32 3 1 926469372230116,
    decodeIntegerRow 32 3 1 926412206181368,
    decodeIntegerRow 32 3 1 644645402098168,
    decodeIntegerRow 32 3 1 1565365699739236,
    decodeIntegerRow 32 3 1 335102642029768,
    decodeIntegerRow 32 3 1 1071678862280956,
    decodeIntegerRow 32 3 1 926600234260152,
    decodeIntegerRow 32 3 1 926532220438396,
    decodeIntegerRow 32 3 1 926467133796088,
    decodeIntegerRow 32 3 1 926412722743964,
    decodeIntegerRow 32 3 1 1524695856065032,
    decodeIntegerRow 32 3 1 1055862808395484,
    decodeIntegerRow 32 3 1 659331738073912,
    decodeIntegerRow 32 3 1 284265335016004,
    decodeIntegerRow 32 3 1 926550816626248,
    decodeIntegerRow 32 3 1 926412206183364,
    decodeIntegerRow 32 3 1 926601267381512,
    decodeIntegerRow 32 3 1 926490379029796,
    decodeIntegerRow 32 3 1 335102648039644,
    decodeIntegerRow 32 3 1 781341298778488,
    decodeIntegerRow 32 3 1 1208374756914244,
    decodeIntegerRow 32 3 1 1565365712152648,
    decodeIntegerRow 32 3 1 926467133800636,
    decodeIntegerRow 32 3 1 926607466109768,
    decodeIntegerRow 32 3 1 926419954592604,
    decodeIntegerRow 32 3 1 926532220442632]

def rows_assocBAC (r : RightIndex 4 3 3) : List ℤ := rows_assocBACData.getD (rightPosition 4 3 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 4 3 3) : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_1_2
  · exact rows_assocBAC_eq_1_1_3
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_1_1
  · exact rows_assocBAC_eq_2_1_2
  · exact rows_assocBAC_eq_2_1_3
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_1_1
  · exact rows_assocBAC_eq_3_1_2
  · exact rows_assocBAC_eq_3_1_3

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 919168030809544,
    decodeIntegerRow 32 3 1 924815769109096,
    decodeIntegerRow 32 3 1 929898729113908,
    decodeIntegerRow 32 3 1 934416902319628,
    decodeIntegerRow 32 3 1 1566962653372212,
    decodeIntegerRow 32 3 1 1200989762512012,
    decodeIntegerRow 32 3 1 1063749928370536,
    decodeIntegerRow 32 3 1 1521216041676744,
    decodeIntegerRow 32 3 1 933852128277064,
    decodeIntegerRow 32 3 1 928204406986216,
    decodeIntegerRow 32 3 1 923121453359668,
    decodeIntegerRow 32 3 1 918603258893068,
    decodeIntegerRow 32 3 1 286057535820852,
    decodeIntegerRow 32 3 1 652030426418572,
    decodeIntegerRow 32 3 1 789270260323816,
    decodeIntegerRow 32 3 1 331804146807624,
    decodeIntegerRow 32 3 1 331622834386188,
    decodeIntegerRow 32 3 1 789228419068468,
    decodeIntegerRow 32 3 1 1201073445337624,
    decodeIntegerRow 32 3 1 1567157913298616,
    decodeIntegerRow 32 3 1 934419312940216,
    decodeIntegerRow 32 3 1 929899762236184,
    decodeIntegerRow 32 3 1 928204936301452,
    decodeIntegerRow 32 3 1 933854396467252,
    decodeIntegerRow 32 3 1 331622834018828,
    decodeIntegerRow 32 3 1 789228418911028,
    decodeIntegerRow 32 3 1 1201073445258904,
    decodeIntegerRow 32 3 1 1567157912957496,
    decodeIntegerRow 32 3 1 934419340570936,
    decodeIntegerRow 32 3 1 929899768612504,
    decodeIntegerRow 32 3 1 928204923548812,
    decodeIntegerRow 32 3 1 933854366711092]

def rows_innerRightBAC (r : RightIndex 4 3 3) : List ℤ := rows_innerRightBACData.getD (rightPosition 4 3 3 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 4 3 3) : (tripleIndices 4 2 4).map ((HexagonAtoms343.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_1_2
  · exact rows_innerRightBAC_eq_0_1_3
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_0_2
  · exact rows_innerRightBAC_eq_1_0_3
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_1_1_2
  · exact rows_innerRightBAC_eq_1_1_3
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_0_1
  · exact rows_innerRightBAC_eq_2_0_2
  · exact rows_innerRightBAC_eq_2_0_3
  · exact rows_innerRightBAC_eq_2_1_0
  · exact rows_innerRightBAC_eq_2_1_1
  · exact rows_innerRightBAC_eq_2_1_2
  · exact rows_innerRightBAC_eq_2_1_3
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_0_1
  · exact rows_innerRightBAC_eq_3_0_2
  · exact rows_innerRightBAC_eq_3_0_3
  · exact rows_innerRightBAC_eq_3_1_0
  · exact rows_innerRightBAC_eq_3_1_1
  · exact rows_innerRightBAC_eq_3_1_2
  · exact rows_innerRightBAC_eq_3_1_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510089820854,
    decodeIntegerRow 32 3 1 926510108831698,
    decodeIntegerRow 32 3 1 926510094937594,
    decodeIntegerRow 32 3 1 926510092825278,
    decodeIntegerRow 32 3 1 994847538854398,
    decodeIntegerRow 32 3 1 902789371005754,
    decodeIntegerRow 32 3 1 1541547094282222,
    decodeIntegerRow 32 3 1 713023583644426,
    decodeIntegerRow 32 3 1 926510092824794,
    decodeIntegerRow 32 3 1 926510094937762,
    decodeIntegerRow 32 3 1 926510080015786,
    decodeIntegerRow 32 3 1 926510099032498,
    decodeIntegerRow 32 3 1 1140057042803698,
    decodeIntegerRow 32 3 1 311284033370986,
    decodeIntegerRow 32 3 1 902782655717278,
    decodeIntegerRow 32 3 1 994868545654246,
    decodeIntegerRow 32 3 1 728277103137334,
    decodeIntegerRow 32 3 1 1546631600779858,
    decodeIntegerRow 32 3 1 948535982346874,
    decodeIntegerRow 32 3 1 857607704831038,
    decodeIntegerRow 32 3 1 926510092838402,
    decodeIntegerRow 32 3 1 926510094976966,
    decodeIntegerRow 32 3 1 926510080138258,
    decodeIntegerRow 32 3 1 926510099385334,
    decodeIntegerRow 32 3 1 857586870218074,
    decodeIntegerRow 32 3 1 948543214196002,
    decodeIntegerRow 32 3 1 306201076555306,
    decodeIntegerRow 32 3 1 1124808172356658,
    decodeIntegerRow 32 3 1 926510089465102,
    decodeIntegerRow 32 3 1 926510108717974,
    decodeIntegerRow 32 3 1 926510094977122,
    decodeIntegerRow 32 3 1 926510092837914]

def rows_assocCAB (r : RightIndex 3 3 4) : List ℤ := rows_assocCABData.getD (rightPosition 3 3 4 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 3 4) : (tripleIndices 4 2 4).map ((HexagonAtoms343.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_1_1
  · exact rows_assocCAB_eq_2_1_2
  · exact rows_assocCAB_eq_2_1_3
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_1_1
  · exact rows_assocCAB_eq_3_1_2
  · exact rows_assocCAB_eq_3_1_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 789248220404944,
    decodeIntegerRow 32 3 1 1521306440159260,
    decodeIntegerRow 32 3 1 1567060799555380,
    decodeIntegerRow 32 3 1 651989790316048,
    decodeIntegerRow 32 3 1 929801615711792,
    decodeIntegerRow 32 3 1 918560239809100,
    decodeIntegerRow 32 3 1 933832356548380,
    decodeIntegerRow 32 3 1 924724854435344,
    decodeIntegerRow 32 3 1 919187862064180,
    decodeIntegerRow 32 3 1 924724867189872,
    decodeIntegerRow 32 3 1 929801622089136,
    decodeIntegerRow 32 3 1 934459976677660,
    decodeIntegerRow 32 3 1 285959388956260,
    decodeIntegerRow 32 3 1 651989790233104,
    decodeIntegerRow 32 3 1 789248220557872,
    decodeIntegerRow 32 3 1 331713749061940,
    decodeIntegerRow 32 3 1 924906167224140,
    decodeIntegerRow 32 3 1 933874197961168,
    decodeIntegerRow 32 3 1 934376266217104,
    decodeIntegerRow 32 3 1 923023313213540,
    decodeIntegerRow 32 3 1 651987379695460,
    decodeIntegerRow 32 3 1 1567059766433104,
    decodeIntegerRow 32 3 1 331713232133872,
    decodeIntegerRow 32 3 1 1063769730021940,
    decodeIntegerRow 32 3 1 1521306956352496,
    decodeIntegerRow 32 3 1 1063769729859940,
    decodeIntegerRow 32 3 1 651987379620940,
    decodeIntegerRow 32 3 1 285960422076592,
    decodeIntegerRow 32 3 1 918643894999792,
    decodeIntegerRow 32 3 1 923023306836300,
    decodeIntegerRow 32 3 1 924906179978780,
    decodeIntegerRow 32 3 1 919146020651344]

def cols_assocABC (r : LeftIndex 3 4 3) : List ℤ := cols_assocABCData.getD (leftPosition 3 4 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 4 3) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms343.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_1_1
  · exact cols_assocABC_eq_2_1_2
  · exact cols_assocABC_eq_2_1_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_1_1
  · exact cols_assocABC_eq_3_1_2
  · exact cols_assocABC_eq_3_1_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 789248220404944,
    decodeIntegerRow 32 3 1 1521306440159260,
    decodeIntegerRow 32 3 1 1567060799555380,
    decodeIntegerRow 32 3 1 651989790316048,
    decodeIntegerRow 32 3 1 929801615711792,
    decodeIntegerRow 32 3 1 918560239809100,
    decodeIntegerRow 32 3 1 933832356548380,
    decodeIntegerRow 32 3 1 924724854435344,
    decodeIntegerRow 32 3 1 919187862064180,
    decodeIntegerRow 32 3 1 924724867189872,
    decodeIntegerRow 32 3 1 929801622089136,
    decodeIntegerRow 32 3 1 934459976677660,
    decodeIntegerRow 32 3 1 285959388956260,
    decodeIntegerRow 32 3 1 651989790233104,
    decodeIntegerRow 32 3 1 789248220557872,
    decodeIntegerRow 32 3 1 331713749061940,
    decodeIntegerRow 32 3 1 924906167224140,
    decodeIntegerRow 32 3 1 933874197961168,
    decodeIntegerRow 32 3 1 934376266217104,
    decodeIntegerRow 32 3 1 923023313213540,
    decodeIntegerRow 32 3 1 651987379695460,
    decodeIntegerRow 32 3 1 1567059766433104,
    decodeIntegerRow 32 3 1 331713232133872,
    decodeIntegerRow 32 3 1 1063769730021940,
    decodeIntegerRow 32 3 1 1521306956352496,
    decodeIntegerRow 32 3 1 1063769729859940,
    decodeIntegerRow 32 3 1 651987379620940,
    decodeIntegerRow 32 3 1 285960422076592,
    decodeIntegerRow 32 3 1 918643894999792,
    decodeIntegerRow 32 3 1 923023306836300,
    decodeIntegerRow 32 3 1 924906179978780,
    decodeIntegerRow 32 3 1 919146020651344]

def cols_right0 (r : LeftIndex 3 4 3) : List ℤ := cols_right0Data.getD (leftPosition 3 4 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 4 3) : (tripleIndices 4 2 4).map (fun j => (right0Middle3 4 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_1_2
  · exact cols_right0_eq_2_1_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_1_2
  · exact cols_right0_eq_3_1_3

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 32 5 2 10151419878066528475312,
    decodeIntegerRow 32 5 2 20880228471765747095312,
    decodeIntegerRow 32 5 2 21029239702210082970312,
    decodeIntegerRow 32 5 2 9406363725600707850312,
    decodeIntegerRow 32 5 2 2402788591375122095312,
    decodeIntegerRow 32 5 2 10151412248671996915312,
    decodeIntegerRow 32 5 2 13876712083878051600312,
    decodeIntegerRow 32 5 2 21029287767395629920312,
    decodeIntegerRow 32 5 2 11656314096755997070352,
    decodeIntegerRow 32 5 2 11643916362380884570064,
    decodeIntegerRow 32 5 2 11637955913162133007560,
    decodeIntegerRow 32 5 2 11626511850662254882872,
    decodeIntegerRow 32 5 2 11639147990799047070064,
    decodeIntegerRow 32 5 2 11656314172439590820272,
    decodeIntegerRow 32 5 2 11656552591629004882872,
    decodeIntegerRow 32 5 2 11637955894851586133064,
    decodeIntegerRow 32 5 2 21029287767424926720312,
    decodeIntegerRow 32 5 2 13876712083755005040312,
    decodeIntegerRow 32 5 2 13131652116836059415312,
    decodeIntegerRow 32 5 2 20880275773992309595312,
    decodeIntegerRow 32 5 2 13876700639663207850312,
    decodeIntegerRow 32 5 2 2253824663147582970312,
    decodeIntegerRow 32 5 2 20880228471746215795312,
    decodeIntegerRow 32 5 2 10151419877945434415312,
    decodeIntegerRow 32 5 2 11637955894851783007560,
    decodeIntegerRow 32 5 2 11656552591629051757752,
    decodeIntegerRow 32 5 2 11626750192947403320272,
    decodeIntegerRow 32 5 2 11643916374588109570064,
    decodeIntegerRow 32 5 2 11656552514724754882872,
    decodeIntegerRow 32 5 2 11645108452224633007560,
    decodeIntegerRow 32 5 2 11643916362381078320560,
    decodeIntegerRow 32 5 2 11656314096755965820272]

def cols_right1 (r : LeftIndex 3 4 3) : List ℤ := cols_right1Data.getD (leftPosition 3 4 3 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 3 4 3) : (tripleIndices 4 2 4).map (fun j => (right1Middle3 4 3) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_1_2
  · exact cols_right1_eq_0_1_3
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_1_1
  · exact cols_right1_eq_1_1_2
  · exact cols_right1_eq_1_1_3
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_0_2
  · exact cols_right1_eq_2_0_3
  · exact cols_right1_eq_2_1_0
  · exact cols_right1_eq_2_1_1
  · exact cols_right1_eq_2_1_2
  · exact cols_right1_eq_2_1_3
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_0_2
  · exact cols_right1_eq_3_0_3
  · exact cols_right1_eq_3_1_0
  · exact cols_right1_eq_3_1_1
  · exact cols_right1_eq_3_1_2
  · exact cols_right1_eq_3_1_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1063771968293968,
    decodeIntegerRow 32 3 1 331713749061940,
    decodeIntegerRow 32 3 1 285959388956260,
    decodeIntegerRow 32 3 1 1201030398618736,
    decodeIntegerRow 32 3 1 923218566762704,
    decodeIntegerRow 32 3 1 934459976677660,
    decodeIntegerRow 32 3 1 919187862064180,
    decodeIntegerRow 32 3 1 928295321661968,
    decodeIntegerRow 32 3 1 933832356548380,
    decodeIntegerRow 32 3 1 928295334416496,
    decodeIntegerRow 32 3 1 923218573140048,
    decodeIntegerRow 32 3 1 918560239809100,
    decodeIntegerRow 32 3 1 1567060799555380,
    decodeIntegerRow 32 3 1 1201030398535792,
    decodeIntegerRow 32 3 1 1063771968446896,
    decodeIntegerRow 32 3 1 1521306440159260,
    decodeIntegerRow 32 3 1 928114008873060,
    decodeIntegerRow 32 3 1 919146020651344,
    decodeIntegerRow 32 3 1 918643894999792,
    decodeIntegerRow 32 3 1 929996882015540,
    decodeIntegerRow 32 3 1 1201032809230900,
    decodeIntegerRow 32 3 1 285960422076592,
    decodeIntegerRow 32 3 1 1521306956352496,
    decodeIntegerRow 32 3 1 789250458991900,
    decodeIntegerRow 32 3 1 331713232133872,
    decodeIntegerRow 32 3 1 789250458829900,
    decodeIntegerRow 32 3 1 1201032809156380,
    decodeIntegerRow 32 3 1 1567059766433104,
    decodeIntegerRow 32 3 1 934376266217104,
    decodeIntegerRow 32 3 1 929996875638300,
    decodeIntegerRow 32 3 1 928114021627700,
    decodeIntegerRow 32 3 1 933874197961168]

def cols_left0 (r : LeftIndex 3 4 3) : List ℤ := cols_left0Data.getD (leftPosition 3 4 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 4 3) : (tripleIndices 4 2 4).map (fun j => (left0Middle3 4 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_1_2
  · exact cols_left0_eq_2_1_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_1_2
  · exact cols_left0_eq_3_1_3

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 32 3 1 789270274222132,
    decodeIntegerRow 32 3 1 1521216045049612,
    decodeIntegerRow 32 3 1 1566962646823336,
    decodeIntegerRow 32 3 1 652030411496584,
    decodeIntegerRow 32 3 1 331622831014348,
    decodeIntegerRow 32 3 1 789228432805108,
    decodeIntegerRow 32 3 1 1201073460176344,
    decodeIntegerRow 32 3 1 1567157906751736,
    decodeIntegerRow 32 3 1 933852143199052,
    decodeIntegerRow 32 3 1 928204413193868,
    decodeIntegerRow 32 3 1 923121456365064,
    decodeIntegerRow 32 3 1 918603272791384,
    decodeIntegerRow 32 3 1 924815259097268,
    decodeIntegerRow 32 3 1 933854381628532,
    decodeIntegerRow 32 3 1 934419326676856,
    decodeIntegerRow 32 3 1 923120423243816,
    decodeIntegerRow 32 3 1 1567157919504376,
    decodeIntegerRow 32 3 1 1201073430420184,
    decodeIntegerRow 32 3 1 1063791783677452,
    decodeIntegerRow 32 3 1 1521397351461172,
    decodeIntegerRow 32 3 1 1200989747590024,
    decodeIntegerRow 32 3 1 286057529271976,
    decodeIntegerRow 32 3 1 1521216038671348,
    decodeIntegerRow 32 3 1 789270246582988,
    decodeIntegerRow 32 3 1 923120423611176,
    decodeIntegerRow 32 3 1 934419326834296,
    decodeIntegerRow 32 3 1 919165807302028,
    decodeIntegerRow 32 3 1 928204930095692,
    decodeIntegerRow 32 3 1 934416916217944,
    decodeIntegerRow 32 3 1 929898732119304,
    decodeIntegerRow 32 3 1 928204413535092,
    decodeIntegerRow 32 3 1 933852143120308]

def cols_left1 (r : LeftIndex 3 4 3) : List ℤ := cols_left1Data.getD (leftPosition 3 4 3 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 3 4 3) : (tripleIndices 4 2 4).map (fun j => (left1Middle3 4 3) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_1_2
  · exact cols_left1_eq_0_1_3
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_1_1
  · exact cols_left1_eq_1_1_2
  · exact cols_left1_eq_1_1_3
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_0_2
  · exact cols_left1_eq_2_0_3
  · exact cols_left1_eq_2_1_0
  · exact cols_left1_eq_2_1_1
  · exact cols_left1_eq_2_1_2
  · exact cols_left1_eq_2_1_3
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_0_2
  · exact cols_left1_eq_3_0_3
  · exact cols_left1_eq_3_1_0
  · exact cols_left1_eq_3_1_1
  · exact cols_left1_eq_3_1_2
  · exact cols_left1_eq_3_1_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 17 8 1183955797380233622923399897097587230192,
    decodeIntegerRow 32 17 8 1183955797380233622899153748123728600816,
    decodeIntegerRow 32 17 8 1183955797380233622922048488631281465872,
    decodeIntegerRow 32 17 8 1183955797380233622922132385340533571856,
    decodeIntegerRow 32 17 8 1180100051519521721978810696075105552656,
    decodeIntegerRow 32 17 8 1184182652285035356083042935546478957072,
    decodeIntegerRow 32 17 8 69645243634494250324984351488525097744,
    decodeIntegerRow 32 17 8 1249516864867934506448101558715438973968,
    decodeIntegerRow 32 17 8 1183955797380233622922132385340556289552,
    decodeIntegerRow 32 17 8 1183955797380233622922048488631280129264,
    decodeIntegerRow 32 17 8 1183955797380233622944952549203788060688,
    decodeIntegerRow 32 17 8 1183955797380233622920706400222977737456,
    decodeIntegerRow 32 17 8 1118394729873743558530637325683124824816,
    decodeIntegerRow 32 17 8 2298266351445454322942225559756971057168,
    decodeIntegerRow 32 17 8 1184182652285100370549705106525449155856,
    decodeIntegerRow 32 17 8 1180100051518416250257623486338342421488,
    decodeIntegerRow 32 17 8 1118421413273691263567575917598348475408,
    decodeIntegerRow 32 17 8 2298267920736629379293920250479063573264,
    decodeIntegerRow 32 17 8 1184182559954996745272760682331970873328,
    decodeIntegerRow 32 17 8 1180100046088342980166441151768369783024,
    decodeIntegerRow 32 17 8 1183955797380233622921973912092029794576,
    decodeIntegerRow 32 17 8 1183955797380233622922057810587075805712,
    decodeIntegerRow 32 17 8 1183955797380233622899153780379631012624,
    decodeIntegerRow 32 17 8 1183955797380233622923400445447928230928,
    decodeIntegerRow 32 17 8 1180100046087237510002412082052946443248,
    decodeIntegerRow 32 17 8 1184182559955061786211111233673717525776,
    decodeIntegerRow 32 17 8 69643673704356989145784899084542478832,
    decodeIntegerRow 32 17 8 1249490181505572813459839717487385329424,
    decodeIntegerRow 32 17 8 1183955797380233622920705851872636893936,
    decodeIntegerRow 32 17 8 1183955797380233622944952516947885658128,
    decodeIntegerRow 32 17 8 1183955797380233622922057810587077141776,
    decodeIntegerRow 32 17 8 1183955797380233622921973912092007076848]

def cols_right2 (r : LeftIndex 3 4 3) : List ℤ := cols_right2Data.getD (leftPosition 3 4 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 4 3) : (tripleIndices 4 2 4).map (fun j => (right2Middle3 4 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_1_2
  · exact cols_right2_eq_2_1_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_1_2
  · exact cols_right2_eq_3_1_3

theorem product0_eq : HexagonAtoms343.outerABC * HexagonAtoms343.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms343.assocBAC * HexagonAtoms343.innerABC = HexagonAtoms343.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms343.innerRightABC * HexagonAtoms343.assocABC = HexagonAtoms343.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms343.inverseACB * right0Middle3 4 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms343.innerACB * right1Middle3 4 3 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms343.assocBAC * left0Middle3 4 3 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms343.innerRightBAC * left1Middle3 4 3 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms343.assocCAB * right2Middle3 4 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn343
