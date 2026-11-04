import RMod.BrundanEllis.StackingReferenceHexagonAtoms652
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn652
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094426434,
    decodeIntegerRow 32 3 1 926510094428182,
    decodeIntegerRow 32 3 1 926510094428038,
    decodeIntegerRow 32 3 1 926510094424974,
    decodeIntegerRow 32 3 1 926510094428194,
    decodeIntegerRow 32 3 1 926510094425462,
    decodeIntegerRow 32 3 1 926510094426918,
    decodeIntegerRow 32 3 1 926510094428014,
    decodeIntegerRow 32 3 1 926510097798274,
    decodeIntegerRow 32 3 1 926510109266902,
    decodeIntegerRow 32 3 1 926510108322118,
    decodeIntegerRow 32 3 1 926510088219214,
    decodeIntegerRow 32 3 1 926510109345634,
    decodeIntegerRow 32 3 1 926510091420982,
    decodeIntegerRow 32 3 1 926510100973798,
    decodeIntegerRow 32 3 1 926510108164654,
    decodeIntegerRow 32 3 1 926532220440514,
    decodeIntegerRow 32 3 1 926607466108822,
    decodeIntegerRow 32 3 1 926601267380998,
    decodeIntegerRow 32 3 1 926469372227854,
    decodeIntegerRow 32 3 1 926607982669474,
    decodeIntegerRow 32 3 1 926490379027702,
    decodeIntegerRow 32 3 1 926553055053478,
    decodeIntegerRow 32 3 1 926600234259694,
    decodeIntegerRow 32 3 1 1071678876177154,
    decodeIntegerRow 32 3 1 1565365705945942,
    decodeIntegerRow 32 3 1 1524695852692678,
    decodeIntegerRow 32 3 1 659331752914894,
    decodeIntegerRow 32 3 1 1568754860383714,
    decodeIntegerRow 32 3 1 797157366717622,
    decodeIntegerRow 32 3 1 1208374771833958,
    decodeIntegerRow 32 3 1 1517917543817134]

def rows_outerABC (r : LeftIndex 5 2 6) : List ℤ := rows_outerABCData.getD (leftPosition 5 2 6 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 5 2 6) : (tripleIndices 4 1 8).map ((HexagonAtoms652.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_0_4
  · exact rows_outerABC_eq_0_0_5
  · exact rows_outerABC_eq_0_0_6
  · exact rows_outerABC_eq_0_0_7
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_0_4
  · exact rows_outerABC_eq_1_0_5
  · exact rows_outerABC_eq_1_0_6
  · exact rows_outerABC_eq_1_0_7
  · exact rows_outerABC_eq_2_0_0
  · exact rows_outerABC_eq_2_0_1
  · exact rows_outerABC_eq_2_0_2
  · exact rows_outerABC_eq_2_0_3
  · exact rows_outerABC_eq_2_0_4
  · exact rows_outerABC_eq_2_0_5
  · exact rows_outerABC_eq_2_0_6
  · exact rows_outerABC_eq_2_0_7
  · exact rows_outerABC_eq_3_0_0
  · exact rows_outerABC_eq_3_0_1
  · exact rows_outerABC_eq_3_0_2
  · exact rows_outerABC_eq_3_0_3
  · exact rows_outerABC_eq_3_0_4
  · exact rows_outerABC_eq_3_0_5
  · exact rows_outerABC_eq_3_0_6
  · exact rows_outerABC_eq_3_0_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 328422227774072,
    decodeIntegerRow 32 3 1 659351483152000,
    decodeIntegerRow 32 3 1 781298365945600,
    decodeIntegerRow 32 3 1 1565455839572552,
    decodeIntegerRow 32 3 1 644667557950072,
    decodeIntegerRow 32 3 1 1517820169130240,
    decodeIntegerRow 32 3 1 284174162061440,
    decodeIntegerRow 32 3 1 797116658260552,
    decodeIntegerRow 32 3 1 284174148964656,
    decodeIntegerRow 32 3 1 797116630778560,
    decodeIntegerRow 32 3 1 1208352660736960,
    decodeIntegerRow 32 3 1 335200013713616,
    decodeIntegerRow 32 3 1 781298338148656,
    decodeIntegerRow 32 3 1 1565455851986880,
    decodeIntegerRow 32 3 1 1524597967820480,
    decodeIntegerRow 32 3 1 1193668735377616,
    decodeIntegerRow 32 3 1 1071635929443520,
    decodeIntegerRow 32 3 1 1565275572318416,
    decodeIntegerRow 32 3 1 1524793744309584,
    decodeIntegerRow 32 3 1 659312022673600,
    decodeIntegerRow 32 3 1 1568663693976000,
    decodeIntegerRow 32 3 1 797198075179216,
    decodeIntegerRow 32 3 1 1208396912770384,
    decodeIntegerRow 32 3 1 1518014918505920,
    decodeIntegerRow 32 3 1 644623305925120,
    decodeIntegerRow 32 3 1 335005276357688,
    decodeIntegerRow 32 3 1 1568663680881272,
    decodeIntegerRow 32 3 1 797198102652160,
    decodeIntegerRow 32 3 1 328226451288960,
    decodeIntegerRow 32 3 1 1193708136492088,
    decodeIntegerRow 32 3 1 1071635901655672,
    decodeIntegerRow 32 3 1 1565275559905920]

def rows_inverseACB (r : LeftIndex 6 2 5) : List ℤ := rows_inverseACBData.getD (leftPosition 6 2 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 2 5) : (tripleIndices 4 1 8).map ((HexagonAtoms652.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 929048473464016,
    decodeIntegerRow 32 3 1 918894957276640,
    decodeIntegerRow 32 3 1 926823904962880,
    decodeIntegerRow 32 3 1 925568662460260,
    decodeIntegerRow 32 3 1 1132401182942416,
    decodeIntegerRow 32 3 1 308836825687840,
    decodeIntegerRow 32 3 1 949387269518400,
    decodeIntegerRow 32 3 1 857878540450660,
    decodeIntegerRow 32 3 1 949387279084340,
    decodeIntegerRow 32 3 1 857878569148480,
    decodeIntegerRow 32 3 1 720619004846560,
    decodeIntegerRow 32 3 1 1544183359975408,
    decodeIntegerRow 32 3 1 926823905081140,
    decodeIntegerRow 32 3 1 925568662815040,
    decodeIntegerRow 32 3 1 923971715376160,
    decodeIntegerRow 32 3 1 934125231540208,
    decodeIntegerRow 32 3 1 926259045890080,
    decodeIntegerRow 32 3 1 925756949172208,
    decodeIntegerRow 32 3 1 923964741805900,
    decodeIntegerRow 32 3 1 918874036609600,
    decodeIntegerRow 32 3 1 903633684608480,
    decodeIntegerRow 32 3 1 857880893671408,
    decodeIntegerRow 32 3 1 720618918753100,
    decodeIntegerRow 32 3 1 308836570596160,
    decodeIntegerRow 32 3 1 1132401269035840,
    decodeIntegerRow 32 3 1 1544183621444380,
    decodeIntegerRow 32 3 1 903633694174416,
    decodeIntegerRow 32 3 1 857880864973600,
    decodeIntegerRow 32 3 1 929055447031360,
    decodeIntegerRow 32 3 1 934146152285980,
    decodeIntegerRow 32 3 1 926259046008016,
    decodeIntegerRow 32 3 1 925756948818400]

def rows_assocBCA (r : RightIndex 5 2 6) : List ℤ := rows_assocBCAData.getD (rightPosition 5 2 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 2 6) : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_0_4
  · exact rows_assocBCA_eq_2_0_5
  · exact rows_assocBCA_eq_2_0_6
  · exact rows_assocBCA_eq_2_0_7
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_0_4
  · exact rows_assocBCA_eq_3_0_5
  · exact rows_assocBCA_eq_3_0_6
  · exact rows_assocBCA_eq_3_0_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 789291181187692,
    decodeIntegerRow 32 3 1 286050561910880,
    decodeIntegerRow 32 3 1 331615860817440,
    decodeIntegerRow 32 3 1 1201052524631236,
    decodeIntegerRow 32 3 1 924816040144492,
    decodeIntegerRow 32 3 1 918603172804000,
    decodeIntegerRow 32 3 1 919165736051680,
    decodeIntegerRow 32 3 1 929899510333636,
    decodeIntegerRow 32 3 1 1567150939729868,
    decodeIntegerRow 32 3 1 1063812690489760,
    decodeIntegerRow 32 3 1 652009505633440,
    decodeIntegerRow 32 3 1 1521209068107996,
    decodeIntegerRow 32 3 1 934419254481868,
    decodeIntegerRow 32 3 1 928205181827680,
    decodeIntegerRow 32 3 1 923121195080800,
    decodeIntegerRow 32 3 1 933852042187996,
    decodeIntegerRow 32 3 1 1521209068475360,
    decodeIntegerRow 32 3 1 1201010683139692,
    decodeIntegerRow 32 3 1 1063812690647236,
    decodeIntegerRow 32 3 1 285869249463200,
    decodeIntegerRow 32 3 1 933852071944480,
    decodeIntegerRow 32 3 1 929898987395692,
    decodeIntegerRow 32 3 1 928205194583236,
    decodeIntegerRow 32 3 1 918600962009440,
    decodeIntegerRow 32 3 1 651967664299360,
    decodeIntegerRow 32 3 1 331615860449972,
    decodeIntegerRow 32 3 1 1566969626599844,
    decodeIntegerRow 32 3 1 789291181030240,
    decodeIntegerRow 32 3 1 923120684897440,
    decodeIntegerRow 32 3 1 919165706286772,
    decodeIntegerRow 32 3 1 934416988417444,
    decodeIntegerRow 32 3 1 924816027390880]

def rows_assocCAB (r : RightIndex 2 6 5) : List ℤ := rows_assocCABData.getD (rightPosition 2 6 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 6 5) : (tripleIndices 4 1 8).map ((HexagonAtoms652.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 1002797407876984,
    decodeIntegerRow 32 3 1 901185448409096,
    decodeIntegerRow 32 3 1 309680107770388,
    decodeIntegerRow 32 3 1 1132107188698732,
    decodeIntegerRow 32 3 1 1545027684745144,
    decodeIntegerRow 32 3 1 720327220334536,
    decodeIntegerRow 32 3 1 987483450674068,
    decodeIntegerRow 32 3 1 906080894063852,
    decodeIntegerRow 32 3 1 946939291955096,
    decodeIntegerRow 32 3 1 865536739126936,
    decodeIntegerRow 32 3 1 720327249071572,
    decodeIntegerRow 32 3 1 1545027675165652,
    decodeIntegerRow 32 3 1 720913028811736,
    decodeIntegerRow 32 3 1 1543340071529176,
    decodeIntegerRow 32 3 1 901185451953492,
    decodeIntegerRow 32 3 1 1002797406700372,
    decodeIntegerRow 32 3 1 309687856179628,
    decodeIntegerRow 32 3 1 720889754923948,
    decodeIntegerRow 32 3 1 1002734731855576,
    decodeIntegerRow 32 3 1 952022768518616,
    decodeIntegerRow 32 3 1 987546298882348,
    decodeIntegerRow 32 3 1 946750750151468,
    decodeIntegerRow 32 3 1 1545033883472536,
    decodeIntegerRow 32 3 1 1132674372333976,
    decodeIntegerRow 32 3 1 720345845255188,
    decodeIntegerRow 32 3 1 307986314957932,
    decodeIntegerRow 32 3 1 946750747315656,
    decodeIntegerRow 32 3 1 987546297941944,
    decodeIntegerRow 32 3 1 900997423874708,
    decodeIntegerRow 32 3 1 850285458181612,
    decodeIntegerRow 32 3 1 720889783582216,
    decodeIntegerRow 32 3 1 309687865732984]

def cols_assocABC (r : LeftIndex 6 5 2) : List ℤ := cols_assocABCData.getD (leftPosition 6 5 2 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 5 2) : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms652.assocABC) j r) = cols_assocABC r := by
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
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_0_4
  · exact cols_assocABC_eq_1_0_5
  · exact cols_assocABC_eq_1_0_6
  · exact cols_assocABC_eq_1_0_7
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3
  · exact cols_assocABC_eq_1_1_4
  · exact cols_assocABC_eq_1_1_5
  · exact cols_assocABC_eq_1_1_6
  · exact cols_assocABC_eq_1_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1002797407876984,
    decodeIntegerRow 32 3 1 901185448409096,
    decodeIntegerRow 32 3 1 309680107770388,
    decodeIntegerRow 32 3 1 1132107188698732,
    decodeIntegerRow 32 3 1 1545027684745144,
    decodeIntegerRow 32 3 1 720327220334536,
    decodeIntegerRow 32 3 1 987483450674068,
    decodeIntegerRow 32 3 1 906080894063852,
    decodeIntegerRow 32 3 1 946939291955096,
    decodeIntegerRow 32 3 1 865536739126936,
    decodeIntegerRow 32 3 1 720327249071572,
    decodeIntegerRow 32 3 1 1545027675165652,
    decodeIntegerRow 32 3 1 720913028811736,
    decodeIntegerRow 32 3 1 1543340071529176,
    decodeIntegerRow 32 3 1 901185451953492,
    decodeIntegerRow 32 3 1 1002797406700372,
    decodeIntegerRow 32 3 1 309687856179628,
    decodeIntegerRow 32 3 1 720889754923948,
    decodeIntegerRow 32 3 1 1002734731855576,
    decodeIntegerRow 32 3 1 952022768518616,
    decodeIntegerRow 32 3 1 987546298882348,
    decodeIntegerRow 32 3 1 946750750151468,
    decodeIntegerRow 32 3 1 1545033883472536,
    decodeIntegerRow 32 3 1 1132674372333976,
    decodeIntegerRow 32 3 1 720345845255188,
    decodeIntegerRow 32 3 1 307986314957932,
    decodeIntegerRow 32 3 1 946750747315656,
    decodeIntegerRow 32 3 1 987546297941944,
    decodeIntegerRow 32 3 1 900997423874708,
    decodeIntegerRow 32 3 1 850285458181612,
    decodeIntegerRow 32 3 1 720889783582216,
    decodeIntegerRow 32 3 1 309687865732984]

def cols_right0 (r : LeftIndex 6 5 2) : List ℤ := cols_right0Data.getD (leftPosition 6 5 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 5 2) : (tripleIndices 4 1 8).map (fun j => (right0Middle6 5 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 5 2 13876710176407348475312,
    decodeIntegerRow 32 5 2 20880276155457153295312,
    decodeIntegerRow 32 5 2 2253824281682739295312,
    decodeIntegerRow 32 5 2 13131642580093871915312,
    decodeIntegerRow 32 5 2 11645108467483423632560,
    decodeIntegerRow 32 5 2 11656314173049903320272,
    decodeIntegerRow 32 5 2 11626511850051864257872,
    decodeIntegerRow 32 5 2 11643916359329322070064,
    decodeIntegerRow 32 5 2 11639148006057837695064,
    decodeIntegerRow 32 5 2 11656552515335067382872,
    decodeIntegerRow 32 5 2 11656314173049950195352,
    decodeIntegerRow 32 5 2 11645108467483617383064,
    decodeIntegerRow 32 5 2 10151421785416137540312,
    decodeIntegerRow 32 5 2 21029240083684692420312,
    decodeIntegerRow 32 5 2 20880276155486450220312,
    decodeIntegerRow 32 5 2 13876710176528442540312,
    decodeIntegerRow 32 5 2 2253776979436645470312,
    decodeIntegerRow 32 5 2 10151410341201293790312,
    decodeIntegerRow 32 5 2 13876702547012817540312,
    decodeIntegerRow 32 5 2 2402836275115356420312,
    decodeIntegerRow 32 5 2 11626511774368270507752,
    decodeIntegerRow 32 5 2 11639147987747093945064,
    decodeIntegerRow 32 5 2 11645108455276392383064,
    decodeIntegerRow 32 5 2 11626750269241356445272,
    decodeIntegerRow 32 5 2 11656314096145653320272,
    decodeIntegerRow 32 5 2 11637955910110376758064,
    decodeIntegerRow 32 5 2 11639147987747290820560,
    decodeIntegerRow 32 5 2 11626511774368301757872,
    decodeIntegerRow 32 5 2 20880228090300903295312,
    decodeIntegerRow 32 5 2 9406361818253051915312,
    decodeIntegerRow 32 5 2 10151410341324340975312,
    decodeIntegerRow 32 5 2 2253776979456176795312]

def cols_left0 (r : LeftIndex 6 5 2) : List ℤ := cols_left0Data.getD (leftPosition 6 5 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 5 2) : (tripleIndices 4 1 8).map (fun j => (left0Middle6 5 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1566117796211135972887424414224,
    decodeIntegerRow 32 9 4 188666857109485290313895523200,
    decodeIntegerRow 32 9 4 192853567270199217642643324800,
    decodeIntegerRow 32 9 4 1905247061537513687946581642896,
    decodeIntegerRow 32 9 4 1716818937411317291988701803024,
    decodeIntegerRow 32 9 4 1716608992137866946955269016960,
    decodeIntegerRow 32 9 4 1716609630258606395323020691840,
    decodeIntegerRow 32 9 4 1716870626066297667586573553296,
    decodeIntegerRow 32 9 4 3245017033989270827891506908944,
    decodeIntegerRow 32 9 4 1867566032834895642291413411200,
    decodeIntegerRow 32 9 4 1528436765757814101128058436480,
    decodeIntegerRow 32 9 4 3240830182021546986122741572464,
    decodeIntegerRow 32 9 4 1717074828165437527282491510544,
    decodeIntegerRow 32 9 4 1716864882882529367205116832640,
    decodeIntegerRow 32 9 4 1716813194227282156700058920320,
    decodeIntegerRow 32 9 4 1717074190023084451431971857264,
    decodeIntegerRow 32 9 4 3240830182021546986374134417280,
    decodeIntegerRow 32 9 4 1905247054534698383504995742224,
    decodeIntegerRow 32 9 4 1867566032834895642322407050896,
    decodeIntegerRow 32 9 4 188666786303241657017046289280,
    decodeIntegerRow 32 9 4 1717074190023086100820426695040,
    decodeIntegerRow 32 9 4 1716870626065230165278381879824,
    decodeIntegerRow 32 9 4 1716864882882529570554386878096,
    decodeIntegerRow 32 9 4 1716608992127076602245016360320,
    decodeIntegerRow 32 9 4 1528436758754998796736062358400,
    decodeIntegerRow 32 9 4 192853567270199217391250468336,
    decodeIntegerRow 32 9 4 3245016963183027194093249468816,
    decodeIntegerRow 32 9 4 1566117796211135972856430775680,
    decodeIntegerRow 32 9 4 1716813194226214979750693272960,
    decodeIntegerRow 32 9 4 1716609630258604745934489431536,
    decodeIntegerRow 32 9 4 1717074828154643892832997923216,
    decodeIntegerRow 32 9 4 1716818937411317088639439315840]

def cols_right2 (r : LeftIndex 6 5 2) : List ℤ := cols_right2Data.getD (leftPosition 6 5 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 5 2) : (tripleIndices 4 1 8).map (fun j => (right2Middle6 5 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms652.outerABC * HexagonAtoms652.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms652.assocBAC * HexagonAtoms652.innerABC = HexagonAtoms652.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms652.innerRightABC * HexagonAtoms652.assocABC = HexagonAtoms652.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms652.inverseACB * right0Middle6 5 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms652.innerACB * right1Middle6 5 2 = right1Middle6 5 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms652.assocBCA * left0Middle6 5 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms652.innerRightBAC * left1Middle6 5 2 = left1Middle6 5 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms652.assocCAB * right2Middle6 5 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn652
