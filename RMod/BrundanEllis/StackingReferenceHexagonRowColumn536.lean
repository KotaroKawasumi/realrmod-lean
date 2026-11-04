import RMod.BrundanEllis.StackingReferenceHexagonAtoms536
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn536
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425919,
    decodeIntegerRow 32 3 1 926510094425917,
    decodeIntegerRow 32 3 1 926510094425911,
    decodeIntegerRow 32 3 1 926510094425893,
    decodeIntegerRow 32 3 1 926510094425839,
    decodeIntegerRow 32 3 1 926510094425677,
    decodeIntegerRow 32 3 1 926510094425191,
    decodeIntegerRow 32 3 1 926510094423733,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094406237,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510094248773,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510089642951,
    decodeIntegerRow 32 3 1 926510080077013,
    decodeIntegerRow 32 3 1 926510137472641,
    decodeIntegerRow 32 3 1 926510223566083,
    decodeIntegerRow 32 3 1 926510481846409,
    decodeIntegerRow 32 3 1 926511256687387,
    decodeIntegerRow 32 3 1 926513581210321,
    decodeIntegerRow 32 3 1 926520554779123,
    decodeIntegerRow 32 3 1 926541475485529,
    decodeIntegerRow 32 3 1 926604237604747,
    decodeIntegerRow 32 3 1 926792523962401,
    decodeIntegerRow 32 3 1 927357383035363,
    decodeIntegerRow 32 3 1 929051960254249,
    decodeIntegerRow 32 3 1 934135691910907,
    decodeIntegerRow 32 3 1 949386886880881,
    decodeIntegerRow 32 3 1 995140471790803,
    decodeIntegerRow 32 3 1 1132401226520569,
    decodeIntegerRow 32 3 1 1544183490709867]

def rows_outerABC (r : LeftIndex 3 6 5) : List ℤ := rows_outerABCData.getD (leftPosition 3 6 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 3 6 5) : (tripleIndices 4 2 4).map ((HexagonAtoms536.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 789207498204604,
    decodeIntegerRow 32 3 1 1567150939729868,
    decodeIntegerRow 32 3 1 1521209068107996,
    decodeIntegerRow 32 3 1 1201010683139692,
    decodeIntegerRow 32 3 1 1063729007821600,
    decodeIntegerRow 32 3 1 286050561910880,
    decodeIntegerRow 32 3 1 331615860817440,
    decodeIntegerRow 32 3 1 651967664299360,
    decodeIntegerRow 32 3 1 928204161460960,
    decodeIntegerRow 32 3 1 918603172804000,
    decodeIntegerRow 32 3 1 919165736051680,
    decodeIntegerRow 32 3 1 923120684897440,
    decodeIntegerRow 32 3 1 928205194583236,
    decodeIntegerRow 32 3 1 918600934369972,
    decodeIntegerRow 32 3 1 919168146663844,
    decodeIntegerRow 32 3 1 923121201456148,
    decodeIntegerRow 32 3 1 1521404328401868,
    decodeIntegerRow 32 3 1 651967664220604,
    decodeIntegerRow 32 3 1 789291181187692,
    decodeIntegerRow 32 3 1 286050562251996,
    decodeIntegerRow 32 3 1 331811120376480,
    decodeIntegerRow 32 3 1 1201010683218400,
    decodeIntegerRow 32 3 1 1063812690489760,
    decodeIntegerRow 32 3 1 1567150939388640,
    decodeIntegerRow 32 3 1 933852071944480,
    decodeIntegerRow 32 3 1 923121195080800,
    decodeIntegerRow 32 3 1 924815007024160,
    decodeIntegerRow 32 3 1 918600962009440,
    decodeIntegerRow 32 3 1 933854482565068,
    decodeIntegerRow 32 3 1 923120678518204,
    decodeIntegerRow 32 3 1 924816040144492,
    decodeIntegerRow 32 3 1 918603200434396]

def rows_inverseACB (r : LeftIndex 5 6 3) : List ℤ := rows_inverseACBData.getD (leftPosition 5 6 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 6 3) : (tripleIndices 4 2 4).map ((HexagonAtoms536.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_2_1
  · exact rows_inverseACB_eq_0_2_2
  · exact rows_inverseACB_eq_0_2_3
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_3_1
  · exact rows_inverseACB_eq_0_3_2
  · exact rows_inverseACB_eq_0_3_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_2_1
  · exact rows_inverseACB_eq_1_2_2
  · exact rows_inverseACB_eq_1_2_3
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_1_3_1
  · exact rows_inverseACB_eq_1_3_2
  · exact rows_inverseACB_eq_1_3_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 926415822107660,
    decodeIntegerRow 32 3 1 926541432436624,
    decodeIntegerRow 32 3 1 926498471811340,
    decodeIntegerRow 32 3 1 926513193789616,
    decodeIntegerRow 32 3 1 926416080386528,
    decodeIntegerRow 32 3 1 926541518534440,
    decodeIntegerRow 32 3 1 926500796334112,
    decodeIntegerRow 32 3 1 926513968631080,
    decodeIntegerRow 32 3 1 1002766069866280,
    decodeIntegerRow 32 3 1 946845022469728,
    decodeIntegerRow 32 3 1 1545030784108840,
    decodeIntegerRow 32 3 1 1132118811313312,
    decodeIntegerRow 32 3 1 865505315018416,
    decodeIntegerRow 32 3 1 901091437914100,
    decodeIntegerRow 32 3 1 309683991527824,
    decodeIntegerRow 32 3 1 720336547163380,
    decodeIntegerRow 32 3 1 926478756410848,
    decodeIntegerRow 32 3 1 926604366745640,
    decodeIntegerRow 32 3 1 926506995061792,
    decodeIntegerRow 32 3 1 926521717040680,
    decodeIntegerRow 32 3 1 926478670321780,
    decodeIntegerRow 32 3 1 926604108463856,
    decodeIntegerRow 32 3 1 926506220221300,
    decodeIntegerRow 32 3 1 926519392517584,
    decodeIntegerRow 32 3 1 946845019635376,
    decodeIntegerRow 32 3 1 1002766068685300,
    decodeIntegerRow 32 3 1 1132118782654864,
    decodeIntegerRow 32 3 1 1545030774529780,
    decodeIntegerRow 32 3 1 901091434371160,
    decodeIntegerRow 32 3 1 865505314073632,
    decodeIntegerRow 32 3 1 720336518426200,
    decodeIntegerRow 32 3 1 309683981975008]

def rows_assocBCA (r : RightIndex 3 6 5) : List ℤ := rows_assocBCAData.getD (rightPosition 3 6 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 6 5) : (tripleIndices 4 2 4).map ((HexagonAtoms536.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_0_2_0
  · exact rows_assocBCA_eq_0_2_1
  · exact rows_assocBCA_eq_0_2_2
  · exact rows_assocBCA_eq_0_2_3
  · exact rows_assocBCA_eq_0_3_0
  · exact rows_assocBCA_eq_0_3_1
  · exact rows_assocBCA_eq_0_3_2
  · exact rows_assocBCA_eq_0_3_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3
  · exact rows_assocBCA_eq_1_2_0
  · exact rows_assocBCA_eq_1_2_1
  · exact rows_assocBCA_eq_1_2_2
  · exact rows_assocBCA_eq_1_2_3
  · exact rows_assocBCA_eq_1_3_0
  · exact rows_assocBCA_eq_1_3_1
  · exact rows_assocBCA_eq_1_3_2
  · exact rows_assocBCA_eq_1_3_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 994200187738192,
    decodeIntegerRow 32 3 1 949135455825620,
    decodeIntegerRow 32 3 1 1536547560400048,
    decodeIntegerRow 32 3 1 1129862804968660,
    decodeIntegerRow 32 3 1 1129855917491824,
    decodeIntegerRow 32 3 1 316451966030140,
    decodeIntegerRow 32 3 1 949073468547216,
    decodeIntegerRow 32 3 1 858634039279420,
    decodeIntegerRow 32 3 1 856937108839300,
    decodeIntegerRow 32 3 1 903382645638416,
    decodeIntegerRow 32 3 1 301200509586820,
    decodeIntegerRow 32 3 1 718080626858224,
    decodeIntegerRow 32 3 1 718073567197420,
    decodeIntegerRow 32 3 1 1551798500273968,
    decodeIntegerRow 32 3 1 903319108678380,
    decodeIntegerRow 32 3 1 995892469131472,
    decodeIntegerRow 32 3 1 1551798497129008,
    decodeIntegerRow 32 3 1 718073566146220,
    decodeIntegerRow 32 3 1 995892440788432,
    decodeIntegerRow 32 3 1 903319099230380,
    decodeIntegerRow 32 3 1 949637552661104,
    decodeIntegerRow 32 3 1 996083051668540,
    decodeIntegerRow 32 3 1 1134939563041936,
    decodeIntegerRow 32 3 1 1551819676111420,
    decodeIntegerRow 32 3 1 316451962797700,
    decodeIntegerRow 32 3 1 1129855916417296,
    decodeIntegerRow 32 3 1 858634010226820,
    decodeIntegerRow 32 3 1 949073458863344,
    decodeIntegerRow 32 3 1 903884742710420,
    decodeIntegerRow 32 3 1 858819972062032,
    decodeIntegerRow 32 3 1 723157384960660,
    decodeIntegerRow 32 3 1 316472625228208]

def rows_assocCAB (r : RightIndex 6 5 3) : List ℤ := rows_assocCABData.getD (rightPosition 6 5 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 5 3) : (tripleIndices 2 4 4).map ((HexagonAtoms536.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_4_0_0
  · exact rows_assocCAB_eq_4_0_1
  · exact rows_assocCAB_eq_4_0_2
  · exact rows_assocCAB_eq_4_0_3
  · exact rows_assocCAB_eq_5_0_0
  · exact rows_assocCAB_eq_5_0_1
  · exact rows_assocCAB_eq_5_0_2
  · exact rows_assocCAB_eq_5_0_3
  · exact rows_assocCAB_eq_6_0_0
  · exact rows_assocCAB_eq_6_0_1
  · exact rows_assocCAB_eq_6_0_2
  · exact rows_assocCAB_eq_6_0_3
  · exact rows_assocCAB_eq_7_0_0
  · exact rows_assocCAB_eq_7_0_1
  · exact rows_assocCAB_eq_7_0_2
  · exact rows_assocCAB_eq_7_0_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 289439455219880,
    decodeIntegerRow 32 3 1 1056387059906272,
    decodeIntegerRow 32 3 1 659876824272040,
    decodeIntegerRow 32 3 1 333310960606368,
    decodeIntegerRow 32 3 1 1523099428558160,
    decodeIntegerRow 32 3 1 644058504169216,
    decodeIntegerRow 32 3 1 781949233429840,
    decodeIntegerRow 32 3 1 282661669284224,
    decodeIntegerRow 32 3 1 1570358526288080,
    decodeIntegerRow 32 3 1 781949203507456,
    decodeIntegerRow 32 3 1 1208961656973520,
    decodeIntegerRow 32 3 1 1523099415437184,
    decodeIntegerRow 32 3 1 333310948220120,
    decodeIntegerRow 32 3 1 1193143392131488,
    decodeIntegerRow 32 3 1 1056387030298840,
    decodeIntegerRow 32 3 1 1563580727593952,
    decodeIntegerRow 32 3 1 644102611725184,
    decodeIntegerRow 32 3 1 1522903122388400,
    decodeIntegerRow 32 3 1 282479833216256,
    decodeIntegerRow 32 3 1 781863110069680,
    decodeIntegerRow 32 3 1 796551886339552,
    decodeIntegerRow 32 3 1 1563761523824040,
    decodeIntegerRow 32 3 1 1519515013827488,
    decodeIntegerRow 32 3 1 1193103789152680,
    decodeIntegerRow 32 3 1 659916427259872,
    decodeIntegerRow 32 3 1 1519515001439400,
    decodeIntegerRow 32 3 1 289258658993568,
    decodeIntegerRow 32 3 1 796551856740520,
    decodeIntegerRow 32 3 1 781863139983616,
    decodeIntegerRow 32 3 1 1570540348919120,
    decodeIntegerRow 32 3 1 1522903135511424,
    decodeIntegerRow 32 3 1 1208917604844880]

def cols_assocABC (r : LeftIndex 5 3 6) : List ℤ := cols_assocABCData.getD (leftPosition 5 3 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 3 6) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms536.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_4_0_0
  · exact cols_assocABC_eq_4_0_1
  · exact cols_assocABC_eq_4_0_2
  · exact cols_assocABC_eq_4_0_3
  · exact cols_assocABC_eq_5_0_0
  · exact cols_assocABC_eq_5_0_1
  · exact cols_assocABC_eq_5_0_2
  · exact cols_assocABC_eq_5_0_3
  · exact cols_assocABC_eq_6_0_0
  · exact cols_assocABC_eq_6_0_1
  · exact cols_assocABC_eq_6_0_2
  · exact cols_assocABC_eq_6_0_3
  · exact cols_assocABC_eq_7_0_0
  · exact cols_assocABC_eq_7_0_1
  · exact cols_assocABC_eq_7_0_2
  · exact cols_assocABC_eq_7_0_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 289439455219880,
    decodeIntegerRow 32 3 1 1056387059906272,
    decodeIntegerRow 32 3 1 659876824272040,
    decodeIntegerRow 32 3 1 333310960606368,
    decodeIntegerRow 32 3 1 1523099428558160,
    decodeIntegerRow 32 3 1 644058504169216,
    decodeIntegerRow 32 3 1 781949233429840,
    decodeIntegerRow 32 3 1 282661669284224,
    decodeIntegerRow 32 3 1 1570358526288080,
    decodeIntegerRow 32 3 1 781949203507456,
    decodeIntegerRow 32 3 1 1208961656973520,
    decodeIntegerRow 32 3 1 1523099415437184,
    decodeIntegerRow 32 3 1 333310948220120,
    decodeIntegerRow 32 3 1 1193143392131488,
    decodeIntegerRow 32 3 1 1056387030298840,
    decodeIntegerRow 32 3 1 1563580727593952,
    decodeIntegerRow 32 3 1 644102611725184,
    decodeIntegerRow 32 3 1 1522903122388400,
    decodeIntegerRow 32 3 1 282479833216256,
    decodeIntegerRow 32 3 1 781863110069680,
    decodeIntegerRow 32 3 1 796551886339552,
    decodeIntegerRow 32 3 1 1563761523824040,
    decodeIntegerRow 32 3 1 1519515013827488,
    decodeIntegerRow 32 3 1 1193103789152680,
    decodeIntegerRow 32 3 1 659916427259872,
    decodeIntegerRow 32 3 1 1519515001439400,
    decodeIntegerRow 32 3 1 289258658993568,
    decodeIntegerRow 32 3 1 796551856740520,
    decodeIntegerRow 32 3 1 781863139983616,
    decodeIntegerRow 32 3 1 1570540348919120,
    decodeIntegerRow 32 3 1 1522903135511424,
    decodeIntegerRow 32 3 1 1208917604844880]

def cols_right0 (r : LeftIndex 5 3 6) : List ℤ := cols_right0Data.getD (leftPosition 5 3 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 3 6) : (tripleIndices 4 2 4).map (fun j => (right0Middle5 3 6) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_4_0_0
  · exact cols_right0_eq_4_0_1
  · exact cols_right0_eq_4_0_2
  · exact cols_right0_eq_4_0_3
  · exact cols_right0_eq_5_0_0
  · exact cols_right0_eq_5_0_1
  · exact cols_right0_eq_5_0_2
  · exact cols_right0_eq_5_0_3
  · exact cols_right0_eq_6_0_0
  · exact cols_right0_eq_6_0_1
  · exact cols_right0_eq_6_0_2
  · exact cols_right0_eq_6_0_3
  · exact cols_right0_eq_7_0_0
  · exact cols_right0_eq_7_0_1
  · exact cols_right0_eq_7_0_2
  · exact cols_right0_eq_7_0_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 289439461257888,
    decodeIntegerRow 32 3 1 1056387030298840,
    decodeIntegerRow 32 3 1 659876796720352,
    decodeIntegerRow 32 3 1 333310948220120,
    decodeIntegerRow 32 3 1 1523099415437184,
    decodeIntegerRow 32 3 1 644058531878320,
    decodeIntegerRow 32 3 1 781949203507456,
    decodeIntegerRow 32 3 1 282661662563760,
    decodeIntegerRow 32 3 1 1570358519567616,
    decodeIntegerRow 32 3 1 781949233429840,
    decodeIntegerRow 32 3 1 1208961684682624,
    decodeIntegerRow 32 3 1 1523099428558160,
    decodeIntegerRow 32 3 1 333310960606368,
    decodeIntegerRow 32 3 1 1193143364579800,
    decodeIntegerRow 32 3 1 1056387059906272,
    decodeIntegerRow 32 3 1 1563580733631960,
    decodeIntegerRow 32 3 1 644102584006960,
    decodeIntegerRow 32 3 1 1522903135511424,
    decodeIntegerRow 32 3 1 282479839932720,
    decodeIntegerRow 32 3 1 781863139983616,
    decodeIntegerRow 32 3 1 796551856740520,
    decodeIntegerRow 32 3 1 1563761529858272,
    decodeIntegerRow 32 3 1 1519515001439400,
    decodeIntegerRow 32 3 1 1193103761591968,
    decodeIntegerRow 32 3 1 659916399699160,
    decodeIntegerRow 32 3 1 1519515013827488,
    decodeIntegerRow 32 3 1 289258665027800,
    decodeIntegerRow 32 3 1 796551886339552,
    decodeIntegerRow 32 3 1 781863110069680,
    decodeIntegerRow 32 3 1 1570540355635584,
    decodeIntegerRow 32 3 1 1522903122388400,
    decodeIntegerRow 32 3 1 1208917577126656]

def cols_left0 (r : LeftIndex 5 3 6) : List ℤ := cols_left0Data.getD (leftPosition 5 3 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 3 6) : (tripleIndices 4 2 4).map (fun j => (left0Middle5 3 6) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_4_0_0
  · exact cols_left0_eq_4_0_1
  · exact cols_left0_eq_4_0_2
  · exact cols_left0_eq_4_0_3
  · exact cols_left0_eq_5_0_0
  · exact cols_left0_eq_5_0_1
  · exact cols_left0_eq_5_0_2
  · exact cols_left0_eq_5_0_3
  · exact cols_left0_eq_6_0_0
  · exact cols_left0_eq_6_0_1
  · exact cols_left0_eq_6_0_2
  · exact cols_left0_eq_6_0_3
  · exact cols_left0_eq_7_0_0
  · exact cols_left0_eq_7_0_1
  · exact cols_left0_eq_7_0_2
  · exact cols_left0_eq_7_0_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1735679517896940558828891082240,
    decodeIntegerRow 32 9 4 1718934985551076698702113056016,
    decodeIntegerRow 32 9 4 3242691008668418150636517948160,
    decodeIntegerRow 32 9 4 1886380698968187400578271315216,
    decodeIntegerRow 32 9 4 1886380698870940901067322447360,
    decodeIntegerRow 32 9 4 190992810748875838422867869584,
    decodeIntegerRow 32 9 4 1718934977674110238315599133440,
    decodeIntegerRow 32 9 4 1698004231502873782350333648784,
    decodeIntegerRow 32 9 4 1697998488308163786659182320496,
    decodeIntegerRow 32 9 4 1714748204488058571458886629120,
    decodeIntegerRow 32 9 4 190527612852718080156782525296,
    decodeIntegerRow 32 9 4 1547251432766472596625078039040,
    decodeIntegerRow 32 9 4 1547251432669196448791116044784,
    decodeIntegerRow 32 9 4 3243156206564309073995332099840,
    decodeIntegerRow 32 9 4 1714748196608690596907620825584,
    decodeIntegerRow 32 9 4 1735685261070036927037273592320,
    decodeIntegerRow 32 9 4 3243156206564309053663543095040,
    decodeIntegerRow 32 9 4 1547251432669196446532019875824,
    decodeIntegerRow 32 9 4 1735685261070035280159265784320,
    decodeIntegerRow 32 9 4 1714748196608690413921175408624,
    decodeIntegerRow 32 9 4 1718935615804454096185407772160,
    decodeIntegerRow 32 9 4 1735685331984347051120658016144,
    decodeIntegerRow 32 9 4 1886432387526039890291858717440,
    decodeIntegerRow 32 9 4 3243156207439794384169201043344,
    decodeIntegerRow 32 9 4 190992810748875818084803609456,
    decodeIntegerRow 32 9 4 1886380698870940898807546033920,
    decodeIntegerRow 32 9 4 1698004231502872134970227942256,
    decodeIntegerRow 32 9 4 1718934977674110055273365271040,
    decodeIntegerRow 32 9 4 1714748834741435968997970000656,
    decodeIntegerRow 32 9 4 1698004302395570278448853245440,
    decodeIntegerRow 32 9 4 1547303121324325086339362691856,
    decodeIntegerRow 32 9 4 190992811624094313683343420160]

def cols_right2 (r : LeftIndex 5 3 6) : List ℤ := cols_right2Data.getD (leftPosition 5 3 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 3 6) : (tripleIndices 2 4 4).map (fun j => (right2Middle5 3 6) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_4_0_0
  · exact cols_right2_eq_4_0_1
  · exact cols_right2_eq_4_0_2
  · exact cols_right2_eq_4_0_3
  · exact cols_right2_eq_5_0_0
  · exact cols_right2_eq_5_0_1
  · exact cols_right2_eq_5_0_2
  · exact cols_right2_eq_5_0_3
  · exact cols_right2_eq_6_0_0
  · exact cols_right2_eq_6_0_1
  · exact cols_right2_eq_6_0_2
  · exact cols_right2_eq_6_0_3
  · exact cols_right2_eq_7_0_0
  · exact cols_right2_eq_7_0_1
  · exact cols_right2_eq_7_0_2
  · exact cols_right2_eq_7_0_3

theorem product0_eq : HexagonAtoms536.outerABC * HexagonAtoms536.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms536.assocBAC * HexagonAtoms536.innerABC = HexagonAtoms536.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms536.innerRightABC * HexagonAtoms536.assocABC = HexagonAtoms536.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms536.inverseACB * right0Middle5 3 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms536.innerACB * right1Middle5 3 6 = right1Middle5 3 6 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms536.assocBCA * left0Middle5 3 6 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms536.innerRightBAC * left1Middle5 3 6 = left1Middle5 3 6 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms536.assocCAB * right2Middle5 3 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn536
