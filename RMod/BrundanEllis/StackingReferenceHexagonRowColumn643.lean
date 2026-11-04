import RMod.BrundanEllis.StackingReferenceHexagonAtoms643
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn643
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

def rows_outerABC (r : LeftIndex 4 3 6) : List ℤ := rows_outerABCData.getD (leftPosition 4 3 6 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 4 3 6) : (tripleIndices 4 1 8).map ((HexagonAtoms643.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 713003782666720,
    decodeIntegerRow 32 3 1 311374946445556,
    decodeIntegerRow 32 3 1 948445062711764,
    decodeIntegerRow 32 3 1 995453134415200,
    decodeIntegerRow 32 3 1 306291473082400,
    decodeIntegerRow 32 3 1 1124765125082356,
    decodeIntegerRow 32 3 1 858129588868564,
    decodeIntegerRow 32 3 1 950140415125920,
    decodeIntegerRow 32 3 1 994890571167520,
    decodeIntegerRow 32 3 1 902879764513788,
    decodeIntegerRow 32 3 1 306291476256412,
    decodeIntegerRow 32 3 1 1124765126188960,
    decodeIntegerRow 32 3 1 904575116219360,
    decodeIntegerRow 32 3 1 857567083016188,
    decodeIntegerRow 32 3 1 713003781638812,
    decodeIntegerRow 32 3 1 311374949645920,
    decodeIntegerRow 32 3 1 306298188369364,
    decodeIntegerRow 32 3 1 728234056965280,
    decodeIntegerRow 32 3 1 994825513341280,
    decodeIntegerRow 32 3 1 950327926643084,
    decodeIntegerRow 32 3 1 712982948049364,
    decodeIntegerRow 32 3 1 1541638010558560,
    decodeIntegerRow 32 3 1 904386064940960,
    decodeIntegerRow 32 3 1 995392696819084,
    decodeIntegerRow 32 3 1 904386055021212,
    decodeIntegerRow 32 3 1 995392668239200,
    decodeIntegerRow 32 3 1 1140037241821600,
    decodeIntegerRow 32 3 1 311382181496452,
    decodeIntegerRow 32 3 1 994825484525212,
    decodeIntegerRow 32 3 1 950327935854240,
    decodeIntegerRow 32 3 1 1546721997305440,
    decodeIntegerRow 32 3 1 1124786132984452]

def rows_inverseACB (r : LeftIndex 6 3 4) : List ℤ := rows_inverseACBData.getD (leftPosition 6 3 4 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 3 4) : (tripleIndices 4 1 8).map ((HexagonAtoms643.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 720367871280160,
    decodeIntegerRow 32 3 1 308083422153748,
    decodeIntegerRow 32 3 1 946841142057404,
    decodeIntegerRow 32 3 1 987503266061920,
    decodeIntegerRow 32 3 1 901088332003040,
    decodeIntegerRow 32 3 1 850244835811348,
    decodeIntegerRow 32 3 1 720869967171004,
    decodeIntegerRow 32 3 1 309589716203680,
    decodeIntegerRow 32 3 1 1132150220500000,
    decodeIntegerRow 32 3 1 1543430476190668,
    decodeIntegerRow 32 3 1 901088341554396,
    decodeIntegerRow 32 3 1 850244807157280,
    decodeIntegerRow 32 3 1 906179037213920,
    decodeIntegerRow 32 3 1 865516951531468,
    decodeIntegerRow 32 3 1 720367870335196,
    decodeIntegerRow 32 3 1 308083424988640,
    decodeIntegerRow 32 3 1 901094530729404,
    decodeIntegerRow 32 3 1 1002756756852640,
    decodeIntegerRow 32 3 1 1132087373468320,
    decodeIntegerRow 32 3 1 309778260842092,
    decodeIntegerRow 32 3 1 720305195254204,
    decodeIntegerRow 32 3 1 1545124794774880,
    decodeIntegerRow 32 3 1 906171298383200,
    decodeIntegerRow 32 3 1 987526511286892,
    decodeIntegerRow 32 3 1 906171288805596,
    decodeIntegerRow 32 3 1 987526482554080,
    decodeIntegerRow 32 3 1 1132714994542240,
    decodeIntegerRow 32 3 1 307895396910772,
    decodeIntegerRow 32 3 1 1132087372287196,
    decodeIntegerRow 32 3 1 309778257298720,
    decodeIntegerRow 32 3 1 951925648568160,
    decodeIntegerRow 32 3 1 850263403336372]

def rows_assocBCA (r : RightIndex 4 3 6) : List ℤ := rows_assocBCAData.getD (rightPosition 4 3 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 4 3 6) : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 1544186977671416,
    decodeIntegerRow 32 3 1 1132390766108320,
    decodeIntegerRow 32 3 1 857848336021120,
    decodeIntegerRow 32 3 1 903727445143252,
    decodeIntegerRow 32 3 1 934135749306616,
    decodeIntegerRow 32 3 1 929051826331360,
    decodeIntegerRow 32 3 1 925662419991040,
    decodeIntegerRow 32 3 1 926228826621652,
    decodeIntegerRow 32 3 1 934135720608640,
    decodeIntegerRow 32 3 1 923968352955028,
    decodeIntegerRow 32 3 1 927357772050904,
    decodeIntegerRow 32 3 1 926228827680160,
    decodeIntegerRow 32 3 1 1544186977317120,
    decodeIntegerRow 32 3 1 720629422625428,
    decodeIntegerRow 32 3 1 995171852870104,
    decodeIntegerRow 32 3 1 903727445156320,
    decodeIntegerRow 32 3 1 926226502094344,
    decodeIntegerRow 32 3 1 925663194830560,
    decodeIntegerRow 32 3 1 923968104240640,
    decodeIntegerRow 32 3 1 918884525638828,
    decodeIntegerRow 32 3 1 903539158785544,
    decodeIntegerRow 32 3 1 857911098140320,
    decodeIntegerRow 32 3 1 720608502037120,
    decodeIntegerRow 32 3 1 308840184749228,
    decodeIntegerRow 32 3 1 949481030053120,
    decodeIntegerRow 32 3 1 857911098100972,
    decodeIntegerRow 32 3 1 720608501919016,
    decodeIntegerRow 32 3 1 1544180003748320,
    decodeIntegerRow 32 3 1 926793685690240,
    decodeIntegerRow 32 3 1 925663191643372,
    decodeIntegerRow 32 3 1 923968094674216,
    decodeIntegerRow 32 3 1 934135634515360]

def rows_assocCAB (r : RightIndex 3 6 4) : List ℤ := rows_assocCABData.getD (rightPosition 3 6 4 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 6 4) : (tripleIndices 4 1 8).map ((HexagonAtoms643.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 918884497472374,
    decodeIntegerRow 32 3 1 929051958659926,
    decodeIntegerRow 32 3 1 925662801033508,
    decodeIntegerRow 32 3 1 926792538311308,
    decodeIntegerRow 32 3 1 308836698148534,
    decodeIntegerRow 32 3 1 1132401226500886,
    decodeIntegerRow 32 3 1 857879717001988,
    decodeIntegerRow 32 3 1 949386887058028,
    decodeIntegerRow 32 3 1 926513581210294,
    decodeIntegerRow 32 3 1 926499634072726,
    decodeIntegerRow 32 3 1 926478713366308,
    decodeIntegerRow 32 3 1 926604237604748,
    decodeIntegerRow 32 3 1 926510137470454,
    decodeIntegerRow 32 3 1 926509965286486,
    decodeIntegerRow 32 3 1 926509707005188,
    decodeIntegerRow 32 3 1 926511256687468,
    decodeIntegerRow 32 3 1 925662810599446,
    decodeIntegerRow 32 3 1 926227679238346,
    decodeIntegerRow 32 3 1 918884496409492,
    decodeIntegerRow 32 3 1 923968227003268,
    decodeIntegerRow 32 3 1 857879717120086,
    decodeIntegerRow 32 3 1 903633302148106,
    decodeIntegerRow 32 3 1 308836698135412,
    decodeIntegerRow 32 3 1 720618962311588,
    decodeIntegerRow 32 3 1 926478713366314,
    decodeIntegerRow 32 3 1 926415951247094,
    decodeIntegerRow 32 3 1 926513581210348,
    decodeIntegerRow 32 3 1 926520554779132,
    decodeIntegerRow 32 3 1 926509707005674,
    decodeIntegerRow 32 3 1 926508932164534,
    decodeIntegerRow 32 3 1 926510137474828,
    decodeIntegerRow 32 3 1 926510223566812]

def cols_assocABC (r : LeftIndex 6 4 3) : List ℤ := cols_assocABCData.getD (leftPosition 6 4 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 4 3) : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms643.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 918884497472374,
    decodeIntegerRow 32 3 1 929051958659926,
    decodeIntegerRow 32 3 1 925662801033508,
    decodeIntegerRow 32 3 1 926792538311308,
    decodeIntegerRow 32 3 1 308836698148534,
    decodeIntegerRow 32 3 1 1132401226500886,
    decodeIntegerRow 32 3 1 857879717001988,
    decodeIntegerRow 32 3 1 949386887058028,
    decodeIntegerRow 32 3 1 926513581210294,
    decodeIntegerRow 32 3 1 926499634072726,
    decodeIntegerRow 32 3 1 926478713366308,
    decodeIntegerRow 32 3 1 926604237604748,
    decodeIntegerRow 32 3 1 926510137470454,
    decodeIntegerRow 32 3 1 926509965286486,
    decodeIntegerRow 32 3 1 926509707005188,
    decodeIntegerRow 32 3 1 926511256687468,
    decodeIntegerRow 32 3 1 925662810599446,
    decodeIntegerRow 32 3 1 926227679238346,
    decodeIntegerRow 32 3 1 918884496409492,
    decodeIntegerRow 32 3 1 923968227003268,
    decodeIntegerRow 32 3 1 857879717120086,
    decodeIntegerRow 32 3 1 903633302148106,
    decodeIntegerRow 32 3 1 308836698135412,
    decodeIntegerRow 32 3 1 720618962311588,
    decodeIntegerRow 32 3 1 926478713366314,
    decodeIntegerRow 32 3 1 926415951247094,
    decodeIntegerRow 32 3 1 926513581210348,
    decodeIntegerRow 32 3 1 926520554779132,
    decodeIntegerRow 32 3 1 926509707005674,
    decodeIntegerRow 32 3 1 926508932164534,
    decodeIntegerRow 32 3 1 926510137474828,
    decodeIntegerRow 32 3 1 926510223566812]

def cols_right0 (r : LeftIndex 6 4 3) : List ℤ := cols_right0Data.getD (leftPosition 6 4 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 4 3) : (tripleIndices 4 1 8).map (fun j => (right0Middle6 4 3) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 644080544088088,
    decodeIntegerRow 32 3 1 333408061622236,
    decodeIntegerRow 32 3 1 1563671125708996,
    decodeIntegerRow 32 3 1 781906186706728,
    decodeIntegerRow 32 3 1 282570747890008,
    decodeIntegerRow 32 3 1 1056427696008796,
    decodeIntegerRow 32 3 1 659896625765956,
    decodeIntegerRow 32 3 1 330018919939048,
    decodeIntegerRow 32 3 1 926419179750168,
    decodeIntegerRow 32 3 1 926469458319196,
    decodeIntegerRow 32 3 1 926490292936516,
    decodeIntegerRow 32 3 1 926608240949288,
    decodeIntegerRow 32 3 1 926488054502488,
    decodeIntegerRow 32 3 1 926607207828956,
    decodeIntegerRow 32 3 1 926600492539076,
    decodeIntegerRow 32 3 1 926553141144808,
    decodeIntegerRow 32 3 1 1563671131745116,
    decodeIntegerRow 32 3 1 1071114032063272,
    decodeIntegerRow 32 3 1 644080571801752,
    decodeIntegerRow 32 3 1 1519612114842436,
    decodeIntegerRow 32 3 1 659896598209756,
    decodeIntegerRow 32 3 1 1523001282034792,
    decodeIntegerRow 32 3 1 282570754608472,
    decodeIntegerRow 32 3 1 796592522446276,
    decodeIntegerRow 32 3 1 926490292932004,
    decodeIntegerRow 32 3 1 926411947901528,
    decodeIntegerRow 32 3 1 926419179752168,
    decodeIntegerRow 32 3 1 926550730528444,
    decodeIntegerRow 32 3 1 926600492540964,
    decodeIntegerRow 32 3 1 926467047702808,
    decodeIntegerRow 32 3 1 926488054507048,
    decodeIntegerRow 32 3 1 926412981023804]

def cols_left0 (r : LeftIndex 6 4 3) : List ℤ := cols_left0Data.getD (leftPosition 6 4 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 4 3) : (tripleIndices 4 1 8).map (fun j => (left0Middle6 4 3) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 20954758119583227539064,
    decodeIntegerRow 32 5 2 13504176378250102539072,
    decodeIntegerRow 32 5 2 11268998384475711914112,
    decodeIntegerRow 32 5 2 11567050218582152539312,
    decodeIntegerRow 32 5 2 11656433344253540040312,
    decodeIntegerRow 32 5 2 11644512413394165045312,
    decodeIntegerRow 32 5 2 11640936128618774445312,
    decodeIntegerRow 32 5 2 11641413011550415195312,
    decodeIntegerRow 32 5 2 11656433344131469725312,
    decodeIntegerRow 32 5 2 11638551951968383795312,
    decodeIntegerRow 32 5 2 11642128236773071320312,
    decodeIntegerRow 32 5 2 11641413011551391445312,
    decodeIntegerRow 32 5 2 20954758119583032226560,
    decodeIntegerRow 32 5 2 9778887987136821289072,
    decodeIntegerRow 32 5 2 12014065980911258789112,
    decodeIntegerRow 32 5 2 11567050218582154101312,
    decodeIntegerRow 32 5 2 11641412935256469570312,
    decodeIntegerRow 32 5 2 11640936143877563445312,
    decodeIntegerRow 32 5 2 11638551948941040045312,
    decodeIntegerRow 32 5 2 11626631021743774415312,
    decodeIntegerRow 32 5 2 11567002534866332226312,
    decodeIntegerRow 32 5 2 11269007921218875976512,
    decodeIntegerRow 32 5 2 9778886079788227539072,
    decodeIntegerRow 32 5 2 2328306627273461914064,
    decodeIntegerRow 32 5 2 11716061830520629101312,
    decodeIntegerRow 32 5 2 11269007921218868164112,
    decodeIntegerRow 32 5 2 9778886079788188476552,
    decodeIntegerRow 32 5 2 20954757738113305664064,
    decodeIntegerRow 32 5 2 11641651430129516445312,
    decodeIntegerRow 32 5 2 11640936143872680695312,
    decodeIntegerRow 32 5 2 11638551948916625970312,
    decodeIntegerRow 32 5 2 11656433343521118165312]

def cols_right2 (r : LeftIndex 6 4 3) : List ℤ := cols_right2Data.getD (leftPosition 6 4 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 4 3) : (tripleIndices 4 1 8).map (fun j => (right2Middle6 4 3) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms643.outerABC * HexagonAtoms643.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms643.assocBAC * HexagonAtoms643.innerABC = HexagonAtoms643.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms643.innerRightABC * HexagonAtoms643.assocABC = HexagonAtoms643.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms643.inverseACB * right0Middle6 4 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms643.innerACB * right1Middle6 4 3 = right1Middle6 4 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms643.assocBCA * left0Middle6 4 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms643.innerRightBAC * left1Middle6 4 3 = left1Middle6 4 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 2 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms643.assocCAB * right2Middle6 4 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn643
