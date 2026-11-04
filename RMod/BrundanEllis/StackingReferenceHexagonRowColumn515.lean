import RMod.BrundanEllis.StackingReferenceHexagonAtoms515
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn515
open Superfusion

theorem assocBCA_alias : HexagonAtoms515.assocBCA = HexagonAtoms515.assocBAC :=
  HexagonAtoms515.assocBCA_eq.symm.trans HexagonAtoms515.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510051379118,
    decodeIntegerRow 32 3 1 926509965286000,
    decodeIntegerRow 32 3 1 926509707006160,
    decodeIntegerRow 32 3 1 926508932162266,
    decodeIntegerRow 32 3 1 926506607641520,
    decodeIntegerRow 32 3 1 926499634072714,
    decodeIntegerRow 32 3 1 926478713366302,
    decodeIntegerRow 32 3 1 926415951247120,
    decodeIntegerRow 32 3 1 949386886874320,
    decodeIntegerRow 32 3 1 857879717041354,
    decodeIntegerRow 32 3 1 720618962272222,
    decodeIntegerRow 32 3 1 1544183490532720,
    decodeIntegerRow 32 3 1 926227664357998,
    decodeIntegerRow 32 3 1 927357381441040,
    decodeIntegerRow 32 3 1 929051955471280,
    decodeIntegerRow 32 3 1 918884482592026,
    decodeIntegerRow 32 3 1 926506607641518,
    decodeIntegerRow 32 3 1 926520554779120,
    decodeIntegerRow 32 3 1 926541475485520,
    decodeIntegerRow 32 3 1 926415951247066,
    decodeIntegerRow 32 3 1 926510137472560,
    decodeIntegerRow 32 3 1 926509965285514,
    decodeIntegerRow 32 3 1 926509707004702,
    decodeIntegerRow 32 3 1 926511256685200,
    decodeIntegerRow 32 3 1 926792523430960,
    decodeIntegerRow 32 3 1 927357384629686,
    decodeIntegerRow 32 3 1 929051965037218,
    decodeIntegerRow 32 3 1 934135677562000,
    decodeIntegerRow 32 3 1 949386886887442,
    decodeIntegerRow 32 3 1 995140471771120,
    decodeIntegerRow 32 3 1 1132401226461520,
    decodeIntegerRow 32 3 1 1544183490887014]

def rows_inverseACB (r : LeftIndex 5 5 1) : List ℤ := rows_inverseACBData.getD (leftPosition 5 5 1 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 5 1) : (tripleIndices 2 2 8).map ((HexagonAtoms515.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 934419240583408,
    decodeIntegerRow 32 3 1 929899507327700,
    decodeIntegerRow 32 3 1 928204154913540,
    decodeIntegerRow 32 3 1 933852057105616,
    decodeIntegerRow 32 3 1 1567150933182448,
    decodeIntegerRow 32 3 1 1201052539470100,
    decodeIntegerRow 32 3 1 1063728993923140,
    decodeIntegerRow 32 3 1 1521209071481296,
    decodeIntegerRow 32 3 1 933852057026860,
    decodeIntegerRow 32 3 1 928204155254768,
    decodeIntegerRow 32 3 1 923120681891504,
    decodeIntegerRow 32 3 1 918600948110980,
    decodeIntegerRow 32 3 1 1521209065102060,
    decodeIntegerRow 32 3 1 1063729021562608,
    decodeIntegerRow 32 3 1 651967679138224,
    decodeIntegerRow 32 3 1 285869242915780,
    decodeIntegerRow 32 3 1 928205188034900,
    decodeIntegerRow 32 3 1 919165721129872,
    decodeIntegerRow 32 3 1 918603186697936,
    decodeIntegerRow 32 3 1 929898990767100,
    decodeIntegerRow 32 3 1 1063812676753300,
    decodeIntegerRow 32 3 1 331615857446032,
    decodeIntegerRow 32 3 1 286050568459216,
    decodeIntegerRow 32 3 1 1201010698061500,
    decodeIntegerRow 32 3 1 923121198452208,
    decodeIntegerRow 32 3 1 934417002311380,
    decodeIntegerRow 32 3 1 919165721208580,
    decodeIntegerRow 32 3 1 928205188376016,
    decodeIntegerRow 32 3 1 652009520555248,
    decodeIntegerRow 32 3 1 1566969633148180,
    decodeIntegerRow 32 3 1 331615863821380,
    decodeIntegerRow 32 3 1 1063812704383696]

def rows_innerACB (r : LeftIndex 5 5 1) : List ℤ := rows_innerACBData.getD (leftPosition 5 5 1 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 5 5 1) : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerACB) r) = rows_innerACB r := by
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

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 1193590532851412,
    decodeIntegerRow 32 3 1 1565408672777932,
    decodeIntegerRow 32 3 1 335124774056356,
    decodeIntegerRow 32 3 1 797066180024324,
    decodeIntegerRow 32 3 1 328304624131204,
    decodeIntegerRow 32 3 1 781431438611804,
    decodeIntegerRow 32 3 1 1208472128598092,
    decodeIntegerRow 32 3 1 1568714144735788,
    decodeIntegerRow 32 3 1 1071588722446724,
    decodeIntegerRow 32 3 1 1524715571461156,
    decodeIntegerRow 32 3 1 1568714131635508,
    decodeIntegerRow 32 3 1 1208472158435628,
    decodeIntegerRow 32 3 1 1565408660369068,
    decodeIntegerRow 32 3 1 1193590562535372,
    decodeIntegerRow 32 3 1 1055953981351076,
    decodeIntegerRow 32 3 1 1517895420809596,
    decodeIntegerRow 32 3 1 328344054931828,
    decodeIntegerRow 32 3 1 1071769029906668,
    decodeIntegerRow 32 3 1 644742803621444,
    decodeIntegerRow 32 3 1 1568795589127396,
    decodeIntegerRow 32 3 1 659233879511324,
    decodeIntegerRow 32 3 1 1565322751527364,
    decodeIntegerRow 32 3 1 335080522022932,
    decodeIntegerRow 32 3 1 1055771662918388,
    decodeIntegerRow 32 3 1 1565322739109404,
    decodeIntegerRow 32 3 1 659233849831356,
    decodeIntegerRow 32 3 1 797248553411948,
    decodeIntegerRow 32 3 1 1517939672834548,
    decodeIntegerRow 32 3 1 781251186736652,
    decodeIntegerRow 32 3 1 1524676140668908,
    decodeIntegerRow 32 3 1 1568795576036164,
    decodeIntegerRow 32 3 1 644742773780124]

def rows_assocBAC (r : RightIndex 1 5 5) : List ℤ := rows_assocBACData.getD (rightPosition 1 5 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 1 5 5) : (tripleIndices 2 2 8).map ((HexagonAtoms515.assocBAC) r) = rows_assocBAC r := by
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

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 1132714993479520,
    decodeIntegerRow 32 3 1 1545124795129228,
    decodeIntegerRow 32 3 1 951931856861924,
    decodeIntegerRow 32 3 1 1002775353001120,
    decodeIntegerRow 32 3 1 946841142070524,
    decodeIntegerRow 32 3 1 987503266022560,
    decodeIntegerRow 32 3 1 1132087373350240,
    decodeIntegerRow 32 3 1 1543241928363988,
    decodeIntegerRow 32 3 1 1132087372405276,
    decodeIntegerRow 32 3 1 1543241931198880,
    decodeIntegerRow 32 3 1 946841151624800,
    decodeIntegerRow 32 3 1 987503237359732,
    decodeIntegerRow 32 3 1 901088341567520,
    decodeIntegerRow 32 3 1 850244807117908,
    decodeIntegerRow 32 3 1 720305194191484,
    decodeIntegerRow 32 3 1 307895397265120,
    decodeIntegerRow 32 3 1 946848890481764,
    decodeIntegerRow 32 3 1 865493677604320,
    decodeIntegerRow 32 3 1 720869967289120,
    decodeIntegerRow 32 3 1 1543430473002508,
    decodeIntegerRow 32 3 1 720367871398240,
    decodeIntegerRow 32 3 1 1544936767052332,
    decodeIntegerRow 32 3 1 951925658135556,
    decodeIntegerRow 32 3 1 850263432038560,
    decodeIntegerRow 32 3 1 901094540296800,
    decodeIntegerRow 32 3 1 1002756785554828,
    decodeIntegerRow 32 3 1 1132652318634724,
    decodeIntegerRow 32 3 1 308083425342880,
    decodeIntegerRow 32 3 1 720869968233724,
    decodeIntegerRow 32 3 1 1543430475836320,
    decodeIntegerRow 32 3 1 946848900033120,
    decodeIntegerRow 32 3 1 865493706258388]

def rows_innerRightBAC (r : RightIndex 1 5 5) : List ℤ := rows_innerRightBACData.getD (rightPosition 1 5 5 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 1 5 5) : (tripleIndices 4 1 8).map ((HexagonAtoms515.innerRightBAC) r) = rows_innerRightBAC r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510051379280,
    decodeIntegerRow 32 3 1 926509965285514,
    decodeIntegerRow 32 3 1 926509707004702,
    decodeIntegerRow 32 3 1 926508932166640,
    decodeIntegerRow 32 3 1 926506607641518,
    decodeIntegerRow 32 3 1 926499634072720,
    decodeIntegerRow 32 3 1 926478713366320,
    decodeIntegerRow 32 3 1 926415951247066,
    decodeIntegerRow 32 3 1 949386886874320,
    decodeIntegerRow 32 3 1 857879717041354,
    decodeIntegerRow 32 3 1 720618962272222,
    decodeIntegerRow 32 3 1 1544183490532720,
    decodeIntegerRow 32 3 1 926227664357998,
    decodeIntegerRow 32 3 1 927357381441040,
    decodeIntegerRow 32 3 1 929051955471280,
    decodeIntegerRow 32 3 1 918884482592026,
    decodeIntegerRow 32 3 1 926513581210320,
    decodeIntegerRow 32 3 1 926499634072714,
    decodeIntegerRow 32 3 1 926478713366302,
    decodeIntegerRow 32 3 1 926604237604720,
    decodeIntegerRow 32 3 1 926510051379118,
    decodeIntegerRow 32 3 1 926510223565840,
    decodeIntegerRow 32 3 1 926510481845680,
    decodeIntegerRow 32 3 1 926508932162266,
    decodeIntegerRow 32 3 1 926792523430960,
    decodeIntegerRow 32 3 1 927357384629686,
    decodeIntegerRow 32 3 1 929051965037218,
    decodeIntegerRow 32 3 1 934135677562000,
    decodeIntegerRow 32 3 1 949386886887442,
    decodeIntegerRow 32 3 1 995140471771120,
    decodeIntegerRow 32 3 1 1132401226461520,
    decodeIntegerRow 32 3 1 1544183490887014]

def rows_assocCAB (r : RightIndex 5 5 1) : List ℤ := rows_assocCABData.getD (rightPosition 5 5 1 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 5 1) : (tripleIndices 4 1 8).map ((HexagonAtoms515.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 311408781167476,
    decodeIntegerRow 32 3 1 1124869384243040,
    decodeIntegerRow 32 3 1 857600917739680,
    decodeIntegerRow 32 3 1 950244683493892,
    decodeIntegerRow 32 3 1 1139932292894240,
    decodeIntegerRow 32 3 1 306262287404884,
    decodeIntegerRow 32 3 1 904491002924572,
    decodeIntegerRow 32 3 1 994861385491360,
    decodeIntegerRow 32 3 1 1140121355116388,
    decodeIntegerRow 32 3 1 1546692811629280,
    decodeIntegerRow 32 3 1 948550010620000,
    decodeIntegerRow 32 3 1 994854699018796,
    decodeIntegerRow 32 3 1 1541671842078880,
    decodeIntegerRow 32 3 1 1124681873828612,
    decodeIntegerRow 32 3 1 857593657310836,
    decodeIntegerRow 32 3 1 902796521369440,
    decodeIntegerRow 32 3 1 995426502962692,
    decodeIntegerRow 32 3 1 950223676698400,
    decodeIntegerRow 32 3 1 311348343571360,
    decodeIntegerRow 32 3 1 728338316125964,
    decodeIntegerRow 32 3 1 948550020535840,
    decodeIntegerRow 32 3 1 994854670201372,
    decodeIntegerRow 32 3 1 1140121354093356,
    decodeIntegerRow 32 3 1 1546692814804960,
    decodeIntegerRow 32 3 1 904491012849196,
    decodeIntegerRow 32 3 1 994861414305760,
    decodeIntegerRow 32 3 1 1139932293918240,
    decodeIntegerRow 32 3 1 306262290580252,
    decodeIntegerRow 32 3 1 995419299693280,
    decodeIntegerRow 32 3 1 902775514565236,
    decodeIntegerRow 32 3 1 1541611404482428,
    decodeIntegerRow 32 3 1 728150803507040]

def cols_right0 (r : LeftIndex 5 1 5) : List ℤ := cols_right0Data.getD (leftPosition 5 1 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 1 5) : (tripleIndices 2 2 8).map (fun j => (right0Middle5 1 5) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 32 3 1 287564349278372,
    decodeIntegerRow 32 3 1 1193708166174052,
    decodeIntegerRow 32 3 1 1055822086195156,
    decodeIntegerRow 32 3 1 335200013711724,
    decodeIntegerRow 32 3 1 1071721822910788,
    decodeIntegerRow 32 3 1 328226444544252,
    decodeIntegerRow 32 3 1 284356507971596,
    decodeIntegerRow 32 3 1 1208352660741196,
    decodeIntegerRow 32 3 1 1208352630897532,
    decodeIntegerRow 32 3 1 1568663693977028,
    decodeIntegerRow 32 3 1 328226451286964,
    decodeIntegerRow 32 3 1 781298338153204,
    decodeIntegerRow 32 3 1 1517820169128348,
    decodeIntegerRow 32 3 1 1055822113677148,
    decodeIntegerRow 32 3 1 659312052355564,
    decodeIntegerRow 32 3 1 287564336865876,
    decodeIntegerRow 32 3 1 797116658256028,
    decodeIntegerRow 32 3 1 335005270347812,
    decodeIntegerRow 32 3 1 287744628946836,
    decodeIntegerRow 32 3 1 659351453470036,
    decodeIntegerRow 32 3 1 1568846026791428,
    decodeIntegerRow 32 3 1 1208396912766148,
    decodeIntegerRow 32 3 1 1071635901651124,
    decodeIntegerRow 32 3 1 1524597967822476,
    decodeIntegerRow 32 3 1 1524597961075772,
    decodeIntegerRow 32 3 1 781384259403772,
    decodeIntegerRow 32 3 1 1208396882930956,
    decodeIntegerRow 32 3 1 284174148965684,
    decodeIntegerRow 32 3 1 1193668705695652,
    decodeIntegerRow 32 3 1 287744616532508,
    decodeIntegerRow 32 3 1 1518014912496044,
    decodeIntegerRow 32 3 1 797116630783084]

def cols_right1 (r : LeftIndex 5 1 5) : List ℤ := cols_right1Data.getD (leftPosition 5 1 5 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 5 1 5) : (tripleIndices 4 1 8).map (fun j => (right1Middle5 1 5) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 311408781167476,
    decodeIntegerRow 32 3 1 1124869384243040,
    decodeIntegerRow 32 3 1 857600917739680,
    decodeIntegerRow 32 3 1 950244683493892,
    decodeIntegerRow 32 3 1 1139932292894240,
    decodeIntegerRow 32 3 1 306262287404884,
    decodeIntegerRow 32 3 1 904491002924572,
    decodeIntegerRow 32 3 1 994861385491360,
    decodeIntegerRow 32 3 1 1140121355116388,
    decodeIntegerRow 32 3 1 1546692811629280,
    decodeIntegerRow 32 3 1 948550010620000,
    decodeIntegerRow 32 3 1 994854699018796,
    decodeIntegerRow 32 3 1 1541671842078880,
    decodeIntegerRow 32 3 1 1124681873828612,
    decodeIntegerRow 32 3 1 857593657310836,
    decodeIntegerRow 32 3 1 902796521369440,
    decodeIntegerRow 32 3 1 995426502962692,
    decodeIntegerRow 32 3 1 950223676698400,
    decodeIntegerRow 32 3 1 311348343571360,
    decodeIntegerRow 32 3 1 728338316125964,
    decodeIntegerRow 32 3 1 948550020535840,
    decodeIntegerRow 32 3 1 994854670201372,
    decodeIntegerRow 32 3 1 1140121354093356,
    decodeIntegerRow 32 3 1 1546692814804960,
    decodeIntegerRow 32 3 1 904491012849196,
    decodeIntegerRow 32 3 1 994861414305760,
    decodeIntegerRow 32 3 1 1139932293918240,
    decodeIntegerRow 32 3 1 306262290580252,
    decodeIntegerRow 32 3 1 995419299693280,
    decodeIntegerRow 32 3 1 902775514565236,
    decodeIntegerRow 32 3 1 1541611404482428,
    decodeIntegerRow 32 3 1 728150803507040]

def cols_left0 (r : LeftIndex 5 1 5) : List ℤ := cols_left0Data.getD (leftPosition 5 1 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 1 5) : (tripleIndices 2 2 8).map (fun j => (left0Middle5 1 5) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 32 3 1 333506217358760,
    decodeIntegerRow 32 3 1 1056384648266560,
    decodeIntegerRow 32 3 1 644060771410240,
    decodeIntegerRow 32 3 1 1570539842277240,
    decodeIntegerRow 32 3 1 1071154639354240,
    decodeIntegerRow 32 3 1 329921796617184,
    decodeIntegerRow 32 3 1 289439980993632,
    decodeIntegerRow 32 3 1 1193101551746560,
    decodeIntegerRow 32 3 1 1193101522139104,
    decodeIntegerRow 32 3 1 1563580220246400,
    decodeIntegerRow 32 3 1 329921803333760,
    decodeIntegerRow 32 3 1 781865521788448,
    decodeIntegerRow 32 3 1 282480359695680,
    decodeIntegerRow 32 3 1 644060741496280,
    decodeIntegerRow 32 3 1 796635568146040,
    decodeIntegerRow 32 3 1 333506211320640,
    decodeIntegerRow 32 3 1 1208919814454080,
    decodeIntegerRow 32 3 1 1570359046049960,
    decodeIntegerRow 32 3 1 333309924309000,
    decodeIntegerRow 32 3 1 796549447147840,
    decodeIntegerRow 32 3 1 1563762037208736,
    decodeIntegerRow 32 3 1 1193145631584640,
    decodeIntegerRow 32 3 1 1071073367140480,
    decodeIntegerRow 32 3 1 1522904165431392,
    decodeIntegerRow 32 3 1 1522904158711040,
    decodeIntegerRow 32 3 1 781946793993184,
    decodeIntegerRow 32 3 1 1193145601985632,
    decodeIntegerRow 32 3 1 289258139256960,
    decodeIntegerRow 32 3 1 1056470714152360,
    decodeIntegerRow 32 3 1 333309918274880,
    decodeIntegerRow 32 3 1 282661155924800,
    decodeIntegerRow 32 3 1 1208919844376440]

def cols_left1 (r : LeftIndex 5 1 5) : List ℤ := cols_left1Data.getD (leftPosition 5 1 5 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 5 1 5) : (tripleIndices 4 1 8).map (fun j => (left1Middle5 1 5) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 17 8 1183955797380233623311342683665809903360,
    decodeIntegerRow 32 17 8 1183955797380233629539975243751181095952,
    decodeIntegerRow 32 17 8 1183955797380233735426728765202468652304,
    decodeIntegerRow 32 17 8 1183955797380235535501538629867791691520,
    decodeIntegerRow 32 17 8 1183955797380266136773306329240654836496,
    decodeIntegerRow 32 17 8 1183955797380786358393357218523522241280,
    decodeIntegerRow 32 17 8 1183955797389630125934222336332268122880,
    decodeIntegerRow 32 17 8 1183955797539974174128929339080948188688,
    decodeIntegerRow 32 17 8 1183728988640418681314951307857353178880,
    decodeIntegerRow 32 17 8 1187811545957087630242784444210963209232,
    decodeIntegerRow 32 17 8 1249503523186751747374485173018764578064,
    decodeIntegerRow 32 17 8 69644458669425507230709282919904321280,
    decodeIntegerRow 32 17 8 1183955800095822993438953046786406398736,
    decodeIntegerRow 32 17 8 1183955751215214324134913353768178942720,
    decodeIntegerRow 32 17 8 1183955012574905543540676635491432047360,
    decodeIntegerRow 32 17 8 1183969139070810972451252641358373473808,
    decodeIntegerRow 32 17 8 1183955797380201109070799968080296410880,
    decodeIntegerRow 32 17 8 1183955797380786358393357218523522241552,
    decodeIntegerRow 32 17 8 1183955797389630125934222336332268127504,
    decodeIntegerRow 32 17 8 1183955797220493071715176958240003137280,
    decodeIntegerRow 32 17 8 1183955797380233623311342683665811239696,
    decodeIntegerRow 32 17 8 1183955797380233616304131053569792869120,
    decodeIntegerRow 32 17 8 1183955797380233510417377532118868796160,
    decodeIntegerRow 32 17 8 1183955797380235535501538629874357110288,
    decodeIntegerRow 32 17 8 1183955794664644252405162572490340524800,
    decodeIntegerRow 32 17 8 1183955751215214324134754880519652447728,
    decodeIntegerRow 32 17 8 1183955012574905543537982590266481632496,
    decodeIntegerRow 32 17 8 1183942455689656273438652424786734826240,
    decodeIntegerRow 32 17 8 1183728988640418681314951307745741059824,
    decodeIntegerRow 32 17 8 1180100048803379615601321855007394062080,
    decodeIntegerRow 32 17 8 1118408071573715498469621156558089076480,
    decodeIntegerRow 32 17 8 69644458669425507230708734569563399152]

def cols_right2 (r : LeftIndex 5 1 5) : List ℤ := cols_right2Data.getD (leftPosition 5 1 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 1 5) : (tripleIndices 4 1 8).map (fun j => (right2Middle5 1 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms515.outerABC * HexagonAtoms515.assocABC = HexagonAtoms515.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms515.assocBAC * HexagonAtoms515.innerABC = HexagonAtoms515.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms515.innerRightABC * HexagonAtoms515.assocABC = HexagonAtoms515.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms515.inverseACB * right0Middle5 1 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms515.innerACB * right1Middle5 1 5 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms515.assocBAC * left0Middle5 1 5 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms515.innerRightBAC * left1Middle5 1 5 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms515.assocCAB * right2Middle5 1 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn515
