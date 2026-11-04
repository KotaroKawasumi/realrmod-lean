import RMod.BrundanEllis.StackingReferenceHexagonAtoms365
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn365
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510080778548,
    decodeIntegerRow 32 3 1 926510100726776,
    decodeIntegerRow 32 3 1 926510097577332,
    decodeIntegerRow 32 3 1 926510109123544,
    decodeIntegerRow 32 3 1 926510108072308,
    decodeIntegerRow 32 3 1 926510088129656,
    decodeIntegerRow 32 3 1 926510091278772,
    decodeIntegerRow 32 3 1 926510079730264,
    decodeIntegerRow 32 3 1 926510100884184,
    decodeIntegerRow 32 3 1 926510080437388,
    decodeIntegerRow 32 3 1 926510109490936,
    decodeIntegerRow 32 3 1 926510097656012,
    decodeIntegerRow 32 3 1 926510100879704,
    decodeIntegerRow 32 3 1 926510080438348,
    decodeIntegerRow 32 3 1 926510109489016,
    decodeIntegerRow 32 3 1 926510097651852,
    decodeIntegerRow 32 3 1 1513984709293132,
    decodeIntegerRow 32 3 1 655278904132744,
    decodeIntegerRow 32 3 1 790852141305868,
    decodeIntegerRow 32 3 1 293825574735016,
    decodeIntegerRow 32 3 1 339077837532172,
    decodeIntegerRow 32 3 1 1197543614176264,
    decodeIntegerRow 32 3 1 1061984496327628,
    decodeIntegerRow 32 3 1 1559109898169896,
    decodeIntegerRow 32 3 1 648503005873576,
    decodeIntegerRow 32 3 1 1528670528629492,
    decodeIntegerRow 32 3 1 278010553813384,
    decodeIntegerRow 32 3 1 787465225297588,
    decodeIntegerRow 32 3 1 648695855183656,
    decodeIntegerRow 32 3 1 1528629203777332,
    decodeIntegerRow 32 3 1 278093203517704,
    decodeIntegerRow 32 3 1 787644299656948]

def rows_outerABC (r : LeftIndex 6 5 3) : List ℤ := rows_outerABCData.getD (leftPosition 6 5 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 6 5 3) : (tripleIndices 2 4 4).map ((HexagonAtoms365.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_1_1
  · exact rows_outerABC_eq_0_1_2
  · exact rows_outerABC_eq_0_1_3
  · exact rows_outerABC_eq_0_2_0
  · exact rows_outerABC_eq_0_2_1
  · exact rows_outerABC_eq_0_2_2
  · exact rows_outerABC_eq_0_2_3
  · exact rows_outerABC_eq_0_3_0
  · exact rows_outerABC_eq_0_3_1
  · exact rows_outerABC_eq_0_3_2
  · exact rows_outerABC_eq_0_3_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_1_1
  · exact rows_outerABC_eq_1_1_2
  · exact rows_outerABC_eq_1_1_3
  · exact rows_outerABC_eq_1_2_0
  · exact rows_outerABC_eq_1_2_1
  · exact rows_outerABC_eq_1_2_2
  · exact rows_outerABC_eq_1_2_3
  · exact rows_outerABC_eq_1_3_0
  · exact rows_outerABC_eq_1_3_1
  · exact rows_outerABC_eq_1_3_2
  · exact rows_outerABC_eq_1_3_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 293847267056684,
    decodeIntegerRow 32 3 1 1062172711655404,
    decodeIntegerRow 32 3 1 655467290572876,
    decodeIntegerRow 32 3 1 339097989855756,
    decodeIntegerRow 32 3 1 1514004861612452,
    decodeIntegerRow 32 3 1 655288188237412,
    decodeIntegerRow 32 3 1 791040356634628,
    decodeIntegerRow 32 3 1 293888598364868,
    decodeIntegerRow 32 3 1 324412686922532,
    decodeIntegerRow 32 3 1 1204328969066212,
    decodeIntegerRow 32 3 1 1065564276342148,
    decodeIntegerRow 32 3 1 1574989492320068,
    decodeIntegerRow 32 3 1 1574947128048044,
    decodeIntegerRow 32 3 1 787653612445804,
    decodeIntegerRow 32 3 1 1204512547578316,
    decodeIntegerRow 32 3 1 1528692230473356,
    decodeIntegerRow 32 3 1 787653583051564,
    decodeIntegerRow 32 3 1 1574947134351084,
    decodeIntegerRow 32 3 1 1528692217880396,
    decodeIntegerRow 32 3 1 1204512520286476,
    decodeIntegerRow 32 3 1 648691192489948,
    decodeIntegerRow 32 3 1 1528607514530588,
    decodeIntegerRow 32 3 1 278030702825852,
    decodeIntegerRow 32 3 1 787455941902012,
    decodeIntegerRow 32 3 1 655288216211548,
    decodeIntegerRow 32 3 1 1514004848704668,
    decodeIntegerRow 32 3 1 293888591904252,
    decodeIntegerRow 32 3 1 791040326505532,
    decodeIntegerRow 32 3 1 790847507323564,
    decodeIntegerRow 32 3 1 1559172915343724,
    decodeIntegerRow 32 3 1 1513922211912396,
    decodeIntegerRow 32 3 1 1197552926257036]

def rows_inverseACB (r : LeftIndex 3 5 6) : List ℤ := rows_inverseACBData.getD (leftPosition 3 5 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 5 6) : (tripleIndices 2 4 4).map ((HexagonAtoms365.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_4_0_0
  · exact rows_inverseACB_eq_4_0_1
  · exact rows_inverseACB_eq_4_0_2
  · exact rows_inverseACB_eq_4_0_3
  · exact rows_inverseACB_eq_5_0_0
  · exact rows_inverseACB_eq_5_0_1
  · exact rows_inverseACB_eq_5_0_2
  · exact rows_inverseACB_eq_5_0_3
  · exact rows_inverseACB_eq_6_0_0
  · exact rows_inverseACB_eq_6_0_1
  · exact rows_inverseACB_eq_6_0_2
  · exact rows_inverseACB_eq_6_0_3
  · exact rows_inverseACB_eq_7_0_0
  · exact rows_inverseACB_eq_7_0_1
  · exact rows_inverseACB_eq_7_0_2
  · exact rows_inverseACB_eq_7_0_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 994200187738192,
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

def rows_assocBCA (r : RightIndex 6 5 3) : List ℤ := rows_assocBCAData.getD (rightPosition 6 5 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 5 3) : (tripleIndices 2 4 4).map ((HexagonAtoms365.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_4_0_0
  · exact rows_assocBCA_eq_4_0_1
  · exact rows_assocBCA_eq_4_0_2
  · exact rows_assocBCA_eq_4_0_3
  · exact rows_assocBCA_eq_5_0_0
  · exact rows_assocBCA_eq_5_0_1
  · exact rows_assocBCA_eq_5_0_2
  · exact rows_assocBCA_eq_5_0_3
  · exact rows_assocBCA_eq_6_0_0
  · exact rows_assocBCA_eq_6_0_1
  · exact rows_assocBCA_eq_6_0_2
  · exact rows_assocBCA_eq_6_0_3
  · exact rows_assocBCA_eq_7_0_0
  · exact rows_assocBCA_eq_7_0_1
  · exact rows_assocBCA_eq_7_0_2
  · exact rows_assocBCA_eq_7_0_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 785881637237444,
    decodeIntegerRow 32 3 1 1574304698824972,
    decodeIntegerRow 32 3 1 1513309226564836,
    decodeIntegerRow 32 3 1 1199295457537388,
    decodeIntegerRow 32 3 1 1559813629231684,
    decodeIntegerRow 32 3 1 792618074939532,
    decodeIntegerRow 32 3 1 1202768267165796,
    decodeIntegerRow 32 3 1 1529306580642028,
    decodeIntegerRow 32 3 1 1199295429530772,
    decodeIntegerRow 32 3 1 339710975122276,
    decodeIntegerRow 32 3 1 1574304705045748,
    decodeIntegerRow 32 3 1 1067138581038404,
    decodeIntegerRow 32 3 1 323713595535892,
    decodeIntegerRow 32 3 1 1202768294429156,
    decodeIntegerRow 32 3 1 1060402083815028,
    decodeIntegerRow 32 3 1 1559813622697924,
    decodeIntegerRow 32 3 1 1529122869912652,
    decodeIntegerRow 32 3 1 650336093804804,
    decodeIntegerRow 32 3 1 792658913332908,
    decodeIntegerRow 32 3 1 293399587651876,
    decodeIntegerRow 32 3 1 653641593051828,
    decodeIntegerRow 32 3 1 1513488115903996,
    decodeIntegerRow 32 3 1 278517985451092,
    decodeIntegerRow 32 3 1 785838733283804,
    decodeIntegerRow 32 3 1 1559620607735716,
    decodeIntegerRow 32 3 1 792658883226452,
    decodeIntegerRow 32 3 1 1202684067775364,
    decodeIntegerRow 32 3 1 1529122857234868,
    decodeIntegerRow 32 3 1 785838762698844,
    decodeIntegerRow 32 3 1 1574502197181868,
    decodeIntegerRow 32 3 1 1513488128735356,
    decodeIntegerRow 32 3 1 1199378623798092]

def rows_assocCAB (r : RightIndex 5 3 6) : List ℤ := rows_assocCABData.getD (rightPosition 5 3 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 3 6) : (tripleIndices 8 1 4).map ((HexagonAtoms365.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926520683919368,
    decodeIntegerRow 32 3 1 926513624257288,
    decodeIntegerRow 32 3 1 926605399866952,
    decodeIntegerRow 32 3 1 926541862908232,
    decodeIntegerRow 32 3 1 926417113507840,
    decodeIntegerRow 32 3 1 926541088067200,
    decodeIntegerRow 32 3 1 926499763212800,
    decodeIntegerRow 32 3 1 926513538163840,
    decodeIntegerRow 32 3 1 1536557888500960,
    decodeIntegerRow 32 3 1 723160842331360,
    decodeIntegerRow 32 3 1 994293182656480,
    decodeIntegerRow 32 3 1 903915733082080,
    decodeIntegerRow 32 3 1 857032428989596,
    decodeIntegerRow 32 3 1 903350874048484,
    decodeIntegerRow 32 3 1 301211105499004,
    decodeIntegerRow 32 3 1 718077111028996,
    decodeIntegerRow 32 3 1 926506650688480,
    decodeIntegerRow 32 3 1 926499763212960,
    decodeIntegerRow 32 3 1 926479100788960,
    decodeIntegerRow 32 3 1 926417113509280,
    decodeIntegerRow 32 3 1 926478325948036,
    decodeIntegerRow 32 3 1 926605399865476,
    decodeIntegerRow 32 3 1 926506564595044,
    decodeIntegerRow 32 3 1 926520683919204,
    decodeIntegerRow 32 3 1 718077081976888,
    decodeIntegerRow 32 3 1 1551809093036872,
    decodeIntegerRow 32 3 1 903350870820472,
    decodeIntegerRow 32 3 1 995987760938248,
    decodeIntegerRow 32 3 1 903915729932800,
    decodeIntegerRow 32 3 1 858727005145600,
    decodeIntegerRow 32 3 1 723160813987840,
    decodeIntegerRow 32 3 1 316462290903040]

def cols_assocABC (r : LeftIndex 3 6 5) : List ℤ := cols_assocABCData.getD (leftPosition 3 6 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 6 5) : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms365.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 926520683919368,
    decodeIntegerRow 32 3 1 926513624257288,
    decodeIntegerRow 32 3 1 926605399866952,
    decodeIntegerRow 32 3 1 926541862908232,
    decodeIntegerRow 32 3 1 926417113507840,
    decodeIntegerRow 32 3 1 926541088067200,
    decodeIntegerRow 32 3 1 926499763212800,
    decodeIntegerRow 32 3 1 926513538163840,
    decodeIntegerRow 32 3 1 1536557888500960,
    decodeIntegerRow 32 3 1 723160842331360,
    decodeIntegerRow 32 3 1 994293182656480,
    decodeIntegerRow 32 3 1 903915733082080,
    decodeIntegerRow 32 3 1 857032428989596,
    decodeIntegerRow 32 3 1 903350874048484,
    decodeIntegerRow 32 3 1 301211105499004,
    decodeIntegerRow 32 3 1 718077111028996,
    decodeIntegerRow 32 3 1 926506650688480,
    decodeIntegerRow 32 3 1 926499763212960,
    decodeIntegerRow 32 3 1 926479100788960,
    decodeIntegerRow 32 3 1 926417113509280,
    decodeIntegerRow 32 3 1 926478325948036,
    decodeIntegerRow 32 3 1 926605399865476,
    decodeIntegerRow 32 3 1 926506564595044,
    decodeIntegerRow 32 3 1 926520683919204,
    decodeIntegerRow 32 3 1 718077081976888,
    decodeIntegerRow 32 3 1 1551809093036872,
    decodeIntegerRow 32 3 1 903350870820472,
    decodeIntegerRow 32 3 1 995987760938248,
    decodeIntegerRow 32 3 1 903915729932800,
    decodeIntegerRow 32 3 1 858727005145600,
    decodeIntegerRow 32 3 1 723160813987840,
    decodeIntegerRow 32 3 1 316462290903040]

def cols_right0 (r : LeftIndex 3 6 5) : List ℤ := cols_right0Data.getD (leftPosition 3 6 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 6 5) : (tripleIndices 2 4 4).map (fun j => (right0Middle3 6 5) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 5 2 11641508111648559545272,
    decodeIntegerRow 32 5 2 11641536003494262853064,
    decodeIntegerRow 32 5 2 11641526451492309725560,
    decodeIntegerRow 32 5 2 11641508493728637732872,
    decodeIntegerRow 32 5 2 2268821001062606445312,
    decodeIntegerRow 32 5 2 13129264116225806445312,
    decodeIntegerRow 32 5 2 9409934282242406445312,
    decodeIntegerRow 32 5 2 2417594194397606445312,
    decodeIntegerRow 32 5 2 11641555795974731482752,
    decodeIntegerRow 32 5 2 11641526469802856290560,
    decodeIntegerRow 32 5 2 11641528374099731602560,
    decodeIntegerRow 32 5 2 11641508188552856470272,
    decodeIntegerRow 32 5 2 2388030290618309570312,
    decodeIntegerRow 32 5 2 13880282640396509570312,
    decodeIntegerRow 32 5 2 13134032487930884570312,
    decodeIntegerRow 32 5 2 21044284105310684570312,
    decodeIntegerRow 32 5 2 20865470170960106445312,
    decodeIntegerRow 32 5 2 9409934282363306445312,
    decodeIntegerRow 32 5 2 10153800249038306445312,
    decodeIntegerRow 32 5 2 2268821001043106445312,
    decodeIntegerRow 32 5 2 11641555871658325232872,
    decodeIntegerRow 32 5 2 11641526451492309415064,
    decodeIntegerRow 32 5 2 11641528361892700353064,
    decodeIntegerRow 32 5 2 11641508111648559595352,
    decodeIntegerRow 32 5 2 21044284105291122070312,
    decodeIntegerRow 32 5 2 10149031877579322070312,
    decodeIntegerRow 32 5 2 13880282640517797070312,
    decodeIntegerRow 32 5 2 20895034074797997070312,
    decodeIntegerRow 32 5 2 11641508188552856420352,
    decodeIntegerRow 32 5 2 11641535991287231602560,
    decodeIntegerRow 32 5 2 11641526469802856600064,
    decodeIntegerRow 32 5 2 11641508569412231482752]

def cols_left0 (r : LeftIndex 3 6 5) : List ℤ := cols_left0Data.getD (leftPosition 3 6 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 6 5) : (tripleIndices 2 4 4).map (fun j => (left0Middle3 6 5) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 10147843608536158165064,
    decodeIntegerRow 32 5 2 21044021616277489232872,
    decodeIntegerRow 32 5 2 20865208139739395545352,
    decodeIntegerRow 32 5 2 13874316460097876913064,
    decodeIntegerRow 32 5 2 21014505777673973607752,
    decodeIntegerRow 32 5 2 10154988536391626915560,
    decodeIntegerRow 32 5 2 13879096275650611287560,
    decodeIntegerRow 32 5 2 20895296182922989295272,
    decodeIntegerRow 32 5 2 13874316459976585977560,
    decodeIntegerRow 32 5 2 2417856225676895545352,
    decodeIntegerRow 32 5 2 21044021616296973657752,
    decodeIntegerRow 32 5 2 13135220756973658165064,
    decodeIntegerRow 32 5 2 2387768182434708045272,
    decodeIntegerRow 32 5 2 13879096275771507853064,
    decodeIntegerRow 32 5 2 13128075828872095665560,
    decodeIntegerRow 32 5 2 21014505777654395532872,
    decodeIntegerRow 32 5 2 2387815561585098595352,
    decodeIntegerRow 32 5 2 13879084819472680037560,
    decodeIntegerRow 32 5 2 13128068217788110975064,
    decodeIntegerRow 32 5 2 21014457788152442357752,
    decodeIntegerRow 32 5 2 13874327891861351913064,
    decodeIntegerRow 32 5 2 2417809000335098595272,
    decodeIntegerRow 32 5 2 21044069757166114232872,
    decodeIntegerRow 32 5 2 13135228404678735975560,
    decodeIntegerRow 32 5 2 2268606577214942357752,
    decodeIntegerRow 32 5 2 13128068217911351915560,
    decodeIntegerRow 32 5 2 9403979546035180037560,
    decodeIntegerRow 32 5 2 2387815561614364295272,
    decodeIntegerRow 32 5 2 13135228404555883165064,
    decodeIntegerRow 32 5 2 2238994608240332982872,
    decodeIntegerRow 32 5 2 2417809000305770545352,
    decodeIntegerRow 32 5 2 9408736473404320663064]

def cols_right2 (r : LeftIndex 3 6 5) : List ℤ := cols_right2Data.getD (leftPosition 3 6 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 6 5) : (tripleIndices 8 1 4).map (fun j => (right2Middle3 6 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms365.outerABC * HexagonAtoms365.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms365.assocBAC * HexagonAtoms365.innerABC = HexagonAtoms365.assocBAC :=
  Matrix.mul_one (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms365.innerRightABC * HexagonAtoms365.assocABC = HexagonAtoms365.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms365.inverseACB * right0Middle3 6 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms365.innerACB * right1Middle3 6 5 = right1Middle3 6 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms365.assocBCA * left0Middle3 6 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms365.innerRightBAC * left1Middle3 6 5 = left1Middle3 6 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms365.assocCAB * right2Middle3 6 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn365
