import RMod.BrundanEllis.StackingReferenceHexagonAtoms625
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn625
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

def rows_outerABC (r : LeftIndex 2 5 6) : List ℤ := rows_outerABCData.getD (leftPosition 2 5 6 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 2 5 6) : (tripleIndices 4 1 8).map ((HexagonAtoms625.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 1002797407876984,
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

def rows_inverseACB (r : LeftIndex 6 5 2) : List ℤ := rows_inverseACBData.getD (leftPosition 6 5 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 5 2) : (tripleIndices 4 1 8).map ((HexagonAtoms625.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_1_4
  · exact rows_inverseACB_eq_0_1_5
  · exact rows_inverseACB_eq_0_1_6
  · exact rows_inverseACB_eq_0_1_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_1_1_4
  · exact rows_inverseACB_eq_1_1_5
  · exact rows_inverseACB_eq_1_1_6
  · exact rows_inverseACB_eq_1_1_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 651967678079716,
    decodeIntegerRow 32 3 1 331615867011484,
    decodeIntegerRow 32 3 1 1566969629958076,
    decodeIntegerRow 32 3 1 789291166230724,
    decodeIntegerRow 32 3 1 923120681878436,
    decodeIntegerRow 32 3 1 919165721247964,
    decodeIntegerRow 32 3 1 934417002271996,
    decodeIntegerRow 32 3 1 924816033584004,
    decodeIntegerRow 32 3 1 928204154900472,
    decodeIntegerRow 32 3 1 918603186658552,
    decodeIntegerRow 32 3 1 919165721090488,
    decodeIntegerRow 32 3 1 923120681537208,
    decodeIntegerRow 32 3 1 1063728992864632,
    decodeIntegerRow 32 3 1 286050565269112,
    decodeIntegerRow 32 3 1 331615854255928,
    decodeIntegerRow 32 3 1 651967650440248,
    decodeIntegerRow 32 3 1 1567150942748872,
    decodeIntegerRow 32 3 1 1063812705450952,
    decodeIntegerRow 32 3 1 652009519487992,
    decodeIntegerRow 32 3 1 1521209061914872,
    decodeIntegerRow 32 3 1 934419240701512,
    decodeIntegerRow 32 3 1 928205188389192,
    decodeIntegerRow 32 3 1 923121198439032,
    decodeIntegerRow 32 3 1 933852056987512,
    decodeIntegerRow 32 3 1 919168131706876,
    decodeIntegerRow 32 3 1 929898990753924,
    decodeIntegerRow 32 3 1 928205188021724,
    decodeIntegerRow 32 3 1 934419240622756,
    decodeIntegerRow 32 3 1 331811114183356,
    decodeIntegerRow 32 3 1 1201010696994244,
    decodeIntegerRow 32 3 1 1063812675686044,
    decodeIntegerRow 32 3 1 1567150936369636]

def rows_assocBCA (r : RightIndex 2 5 6) : List ℤ := rows_assocBCAData.getD (rightPosition 2 5 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 2 5 6) : (tripleIndices 4 1 8).map ((HexagonAtoms625.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_0_1_4
  · exact rows_assocBCA_eq_0_1_5
  · exact rows_assocBCA_eq_0_1_6
  · exact rows_assocBCA_eq_0_1_7
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3
  · exact rows_assocBCA_eq_1_1_4
  · exact rows_assocBCA_eq_1_1_5
  · exact rows_assocBCA_eq_1_1_6
  · exact rows_assocBCA_eq_1_1_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 929900454001288,
    decodeIntegerRow 32 3 1 919166668275848,
    decodeIntegerRow 32 3 1 934418638047432,
    decodeIntegerRow 32 3 1 928205791043272,
    decodeIntegerRow 32 3 1 1201129220030728,
    decodeIntegerRow 32 3 1 331692576270088,
    decodeIntegerRow 32 3 1 1567102127768392,
    decodeIntegerRow 32 3 1 1063861520431432,
    decodeIntegerRow 32 3 1 928203552246364,
    decodeIntegerRow 32 3 1 918602584004444,
    decodeIntegerRow 32 3 1 919167184679036,
    decodeIntegerRow 32 3 1 923122145125756,
    decodeIntegerRow 32 3 1 1063680177881884,
    decodeIntegerRow 32 3 1 286001750286364,
    decodeIntegerRow 32 3 1 331734404928316,
    decodeIntegerRow 32 3 1 652086201112636,
    decodeIntegerRow 32 3 1 1063861490668792,
    decodeIntegerRow 32 3 1 1567102121386888,
    decodeIntegerRow 32 3 1 1521327625340872,
    decodeIntegerRow 32 3 1 651890941185208,
    decodeIntegerRow 32 3 1 928205790675832,
    decodeIntegerRow 32 3 1 934418637968648,
    decodeIntegerRow 32 3 1 933853520733512,
    decodeIntegerRow 32 3 1 923119734509368,
    decodeIntegerRow 32 3 1 1200933960105244,
    decodeIntegerRow 32 3 1 1521285771173476,
    decodeIntegerRow 32 3 1 286001743913284,
    decodeIntegerRow 32 3 1 1063680207640636,
    decodeIntegerRow 32 3 1 929898043384924,
    decodeIntegerRow 32 3 1 933853004015396,
    decodeIntegerRow 32 3 1 918602583925764,
    decodeIntegerRow 32 3 1 928203552613756]

def rows_assocCAB (r : RightIndex 5 6 2) : List ℤ := rows_assocCABData.getD (rightPosition 5 6 2 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 6 2) : (tripleIndices 2 2 8).map ((HexagonAtoms625.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_0_4
  · exact rows_assocCAB_eq_2_0_5
  · exact rows_assocCAB_eq_2_0_6
  · exact rows_assocCAB_eq_2_0_7
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_0_4
  · exact rows_assocCAB_eq_3_0_5
  · exact rows_assocCAB_eq_3_0_6
  · exact rows_assocCAB_eq_3_0_7

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 328422227774072,
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

def cols_assocABC (r : LeftIndex 6 2 5) : List ℤ := cols_assocABCData.getD (leftPosition 6 2 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 2 5) : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms625.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_0_4
  · exact cols_assocABC_eq_0_0_5
  · exact cols_assocABC_eq_0_0_6
  · exact cols_assocABC_eq_0_0_7
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_0_4
  · exact cols_assocABC_eq_1_0_5
  · exact cols_assocABC_eq_1_0_6
  · exact cols_assocABC_eq_1_0_7
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_2_0_4
  · exact cols_assocABC_eq_2_0_5
  · exact cols_assocABC_eq_2_0_6
  · exact cols_assocABC_eq_2_0_7
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_3_0_4
  · exact cols_assocABC_eq_3_0_5
  · exact cols_assocABC_eq_3_0_6
  · exact cols_assocABC_eq_3_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 328422227774072,
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

def cols_right0 (r : LeftIndex 6 2 5) : List ℤ := cols_right0Data.getD (leftPosition 6 2 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 2 5) : (tripleIndices 4 1 8).map (fun j => (right0Middle6 2 5) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_0_4
  · exact cols_right0_eq_2_0_5
  · exact cols_right0_eq_2_0_6
  · exact cols_right0_eq_2_0_7
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_0_4
  · exact cols_right0_eq_3_0_5
  · exact cols_right0_eq_3_0_6
  · exact cols_right0_eq_3_0_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1716816065867329997472126592000,
    decodeIntegerRow 32 9 4 1717074508656592446043167218560,
    decodeIntegerRow 32 9 4 1716841587141400326118387323520,
    decodeIntegerRow 32 9 4 1716844817189959488474808483984,
    decodeIntegerRow 32 9 4 1547277277045398841482220364800,
    decodeIntegerRow 32 9 4 3242923608053972870284188784000,
    decodeIntegerRow 32 9 4 1714748519613546513146052321920,
    decodeIntegerRow 32 9 4 1735682424940645452103831306384,
    decodeIntegerRow 32 9 4 1714748519613546330131712682224,
    decodeIntegerRow 32 9 4 1735682424940643804974774549120,
    decodeIntegerRow 32 9 4 1886406543247113645435065015680,
    decodeIntegerRow 32 9 4 190760212238539634708586926080,
    decodeIntegerRow 32 9 4 1716841587141400326090492995824,
    decodeIntegerRow 32 9 4 1716844817189959488223759534720,
    decodeIntegerRow 32 9 4 1716867754425182487186062619520,
    decodeIntegerRow 32 9 4 1716609311635920038617742970880,
    decodeIntegerRow 32 9 4 1716842225272944941098466177920,
    decodeIntegerRow 32 9 4 1716844746286454531003751239680,
    decodeIntegerRow 32 9 4 1716867754522443810858522301456,
    decodeIntegerRow 32 9 4 1717074509531944359092166728320,
    decodeIntegerRow 32 9 4 1718935300677765397443760414080,
    decodeIntegerRow 32 9 4 1735682424929836991233390612480,
    decodeIntegerRow 32 9 4 1886406543247128469596575831056,
    decodeIntegerRow 32 9 4 3242923608054106267402859489920,
    decodeIntegerRow 32 9 4 1547277277045384017320709550720,
    decodeIntegerRow 32 9 4 190760212238406196920062966896,
    decodeIntegerRow 32 9 4 1718935300677765214429420774400,
    decodeIntegerRow 32 9 4 1735682424929838638362447369600,
    decodeIntegerRow 32 9 4 1716816065770068673799675413120,
    decodeIntegerRow 32 9 4 1716609310760568125562544733296,
    decodeIntegerRow 32 9 4 1716842225272944941070571955200,
    decodeIntegerRow 32 9 4 1716844746286454531254799244160]

def cols_left0 (r : LeftIndex 6 2 5) : List ℤ := cols_left0Data.getD (leftPosition 6 2 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 2 5) : (tripleIndices 4 1 8).map (fun j => (left0Middle6 2 5) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_0_4
  · exact cols_left0_eq_2_0_5
  · exact cols_left0_eq_2_0_6
  · exact cols_left0_eq_2_0_7
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_0_4
  · exact cols_left0_eq_3_0_5
  · exact cols_left0_eq_3_0_6
  · exact cols_left0_eq_3_0_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1716870626071174735258570678480,
    decodeIntegerRow 32 9 4 1716609630263482719781309929680,
    decodeIntegerRow 32 9 4 1717074828160707797338109680080,
    decodeIntegerRow 32 9 4 1716864882887258376527398179280,
    decodeIntegerRow 32 9 4 1905247093536488353737208668880,
    decodeIntegerRow 32 9 4 192853599269174807429435792080,
    decodeIntegerRow 32 9 4 3245017002962908657592598166480,
    decodeIntegerRow 32 9 4 1867566063861258718514441417680,
    decodeIntegerRow 32 9 4 1716864882876466386696132206656,
    decodeIntegerRow 32 9 4 1716608992133138861880507646016,
    decodeIntegerRow 32 9 4 1716609630264550059379094950976,
    decodeIntegerRow 32 9 4 1716813194232159387051469059136,
    decodeIntegerRow 32 9 4 1867565993055013435578395031616,
    decodeIntegerRow 32 9 4 188666826083123120265652672576,
    decodeIntegerRow 32 9 4 192853606271989908496960515136,
    decodeIntegerRow 32 9 4 1528436797756788766943484152896,
    decodeIntegerRow 32 9 4 1867566063861257069125943644720,
    decodeIntegerRow 32 9 4 3245017002962908494913146942160,
    decodeIntegerRow 32 9 4 3240830221023337880577717879760,
    decodeIntegerRow 32 9 4 1528436726756022486051016175920,
    decodeIntegerRow 32 9 4 1716864882887258376276005327920,
    decodeIntegerRow 32 9 4 1717074828160707797313314762960,
    decodeIntegerRow 32 9 4 1717074190029029764907532804560,
    decodeIntegerRow 32 9 4 1716813194221337749148574307120,
    decodeIntegerRow 32 9 4 1905247022535722072844748250176,
    decodeIntegerRow 32 9 4 3240830214020522372811660624064,
    decodeIntegerRow 32 9 4 188666826083122957586277870784,
    decodeIntegerRow 32 9 4 1867565993055015084966883356736,
    decodeIntegerRow 32 9 4 1716870626060353097355675927616,
    decodeIntegerRow 32 9 4 1717074190027962425247760505024,
    decodeIntegerRow 32 9 4 1716608992133138861855712740544,
    decodeIntegerRow 32 9 4 1716864882876466386947525056576]

def cols_right2 (r : LeftIndex 6 2 5) : List ℤ := cols_right2Data.getD (leftPosition 6 2 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 2 5) : (tripleIndices 2 2 8).map (fun j => (right2Middle6 2 5) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_0_4
  · exact cols_right2_eq_2_0_5
  · exact cols_right2_eq_2_0_6
  · exact cols_right2_eq_2_0_7
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_0_4
  · exact cols_right2_eq_3_0_5
  · exact cols_right2_eq_3_0_6
  · exact cols_right2_eq_3_0_7

theorem product0_eq : HexagonAtoms625.outerABC * HexagonAtoms625.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms625.assocBAC * HexagonAtoms625.innerABC = HexagonAtoms625.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms625.innerRightABC * HexagonAtoms625.assocABC = HexagonAtoms625.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms625.inverseACB * right0Middle6 2 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms625.innerACB * right1Middle6 2 5 = right1Middle6 2 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product5_eq : HexagonAtoms625.assocBCA * left0Middle6 2 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms625.innerRightBAC * left1Middle6 2 5 = left1Middle6 2 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product7_eq : HexagonAtoms625.assocCAB * right2Middle6 2 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn625
