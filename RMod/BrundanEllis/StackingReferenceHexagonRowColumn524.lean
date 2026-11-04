import RMod.BrundanEllis.StackingReferenceHexagonAtoms524
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn524
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 782003298929324,
    decodeIntegerRow 32 3 1 329978274257644,
    decodeIntegerRow 32 3 1 289327026762532,
    decodeIntegerRow 32 3 1 659987511703068,
    decodeIntegerRow 32 3 1 333365017737844,
    decodeIntegerRow 32 3 1 796690668026316,
    decodeIntegerRow 32 3 1 1208849247594948,
    decodeIntegerRow 32 3 1 1570469232902788,
    decodeIntegerRow 32 3 1 1193214506497356,
    decodeIntegerRow 32 3 1 1563649082242804,
    decodeIntegerRow 32 3 1 330059546462332,
    decodeIntegerRow 32 3 1 781809072122172,
    decodeIntegerRow 32 3 1 282590558936596,
    decodeIntegerRow 32 3 1 643990145029716,
    decodeIntegerRow 32 3 1 796494374976668,
    decodeIntegerRow 32 3 1 333451111175332,
    decodeIntegerRow 32 3 1 1570469245285732,
    decodeIntegerRow 32 3 1 644170970861148,
    decodeIntegerRow 32 3 1 796690640310764,
    decodeIntegerRow 32 3 1 1519655164400044,
    decodeIntegerRow 32 3 1 1193032647229692,
    decodeIntegerRow 32 3 1 289327013644732,
    decodeIntegerRow 32 3 1 1523041908562636,
    decodeIntegerRow 32 3 1 782003271371124,
    decodeIntegerRow 32 3 1 333451117898308,
    decodeIntegerRow 32 3 1 1056525841586948,
    decodeIntegerRow 32 3 1 643990174631924,
    decodeIntegerRow 32 3 1 1570429642306636,
    decodeIntegerRow 32 3 1 1071211144283868,
    decodeIntegerRow 32 3 1 330059552503012,
    decodeIntegerRow 32 3 1 289371093482836,
    decodeIntegerRow 32 3 1 1193214476580116]

def rows_inverseACB (r : LeftIndex 5 4 2) : List ℤ := rows_inverseACBData.getD (leftPosition 5 4 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 4 2) : (tripleIndices 2 2 8).map ((HexagonAtoms524.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 926792394763216,
    decodeIntegerRow 32 3 1 927357426259240,
    decodeIntegerRow 32 3 1 929050797999340,
    decodeIntegerRow 32 3 1 934136079311712,
    decodeIntegerRow 32 3 1 949376421746896,
    decodeIntegerRow 32 3 1 995143972924840,
    decodeIntegerRow 32 3 1 1132307083872940,
    decodeIntegerRow 32 3 1 1544214870175072,
    decodeIntegerRow 32 3 1 995136999354580,
    decodeIntegerRow 32 3 1 949397342448928,
    decodeIntegerRow 32 3 1 308868080795824,
    decodeIntegerRow 32 3 1 720524818620760,
    decodeIntegerRow 32 3 1 925662848686060,
    decodeIntegerRow 32 3 1 926227535808352,
    decodeIntegerRow 32 3 1 934135304470736,
    decodeIntegerRow 32 3 1 929053122522280,
    decodeIntegerRow 32 3 1 1544214873363880,
    decodeIntegerRow 32 3 1 720713106041296,
    decodeIntegerRow 32 3 1 995143944225568,
    decodeIntegerRow 32 3 1 903643757543380,
    decodeIntegerRow 32 3 1 918884109500760,
    decodeIntegerRow 32 3 1 929050797986224,
    decodeIntegerRow 32 3 1 925662762946912,
    decodeIntegerRow 32 3 1 926792394881260,
    decodeIntegerRow 32 3 1 929053122509152,
    decodeIntegerRow 32 3 1 918884884341740,
    decodeIntegerRow 32 3 1 926227535690200,
    decodeIntegerRow 32 3 1 927357339811504,
    decodeIntegerRow 32 3 1 1132495369167712,
    decodeIntegerRow 32 3 1 308868077607340,
    decodeIntegerRow 32 3 1 903622836832600,
    decodeIntegerRow 32 3 1 995136970658224]

def rows_assocBCA (r : RightIndex 2 4 5) : List ℤ := rows_assocBCAData.getD (rightPosition 2 4 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 2 4 5) : (tripleIndices 2 2 8).map ((HexagonAtoms524.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 1132087372405456,
    decodeIntegerRow 32 3 1 1543241931198340,
    decodeIntegerRow 32 3 1 946841151623340,
    decodeIntegerRow 32 3 1 987503237364112,
    decodeIntegerRow 32 3 1 901088341568976,
    decodeIntegerRow 32 3 1 850244807113540,
    decodeIntegerRow 32 3 1 720305194191340,
    decodeIntegerRow 32 3 1 307895397265552,
    decodeIntegerRow 32 3 1 1132714993479376,
    decodeIntegerRow 32 3 1 1545124795129660,
    decodeIntegerRow 32 3 1 951931856863380,
    decodeIntegerRow 32 3 1 1002775352996752,
    decodeIntegerRow 32 3 1 946841142071984,
    decodeIntegerRow 32 3 1 987503266018180,
    decodeIntegerRow 32 3 1 1132087373350060,
    decodeIntegerRow 32 3 1 1543241928364528,
    decodeIntegerRow 32 3 1 951925648556496,
    decodeIntegerRow 32 3 1 850263403301380,
    decodeIntegerRow 32 3 1 720367870217260,
    decodeIntegerRow 32 3 1 1544936763509392,
    decodeIntegerRow 32 3 1 1132150220617936,
    decodeIntegerRow 32 3 1 309589713014980,
    decodeIntegerRow 32 3 1 906171288817260,
    decodeIntegerRow 32 3 1 987526482589072,
    decodeIntegerRow 32 3 1 946848890480304,
    decodeIntegerRow 32 3 1 865493677599940,
    decodeIntegerRow 32 3 1 720869967288940,
    decodeIntegerRow 32 3 1 1543430473001968,
    decodeIntegerRow 32 3 1 720367871398096,
    decodeIntegerRow 32 3 1 1544936767051900,
    decodeIntegerRow 32 3 1 951925658134100,
    decodeIntegerRow 32 3 1 850263432034192]

def rows_assocCAB (r : RightIndex 4 5 2) : List ℤ := rows_assocCABData.getD (rightPosition 4 5 2 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 4 5 2) : (tripleIndices 4 1 8).map ((HexagonAtoms524.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 309652557866488,
    decodeIntegerRow 32 3 1 1132024510336604,
    decodeIntegerRow 32 3 1 865501439868472,
    decodeIntegerRow 32 3 1 946833397020796,
    decodeIntegerRow 32 3 1 1002762970502152,
    decodeIntegerRow 32 3 1 901082139822436,
    decodeIntegerRow 32 3 1 1544999446093768,
    decodeIntegerRow 32 3 1 720242533125444,
    decodeIntegerRow 32 3 1 906186788996872,
    decodeIntegerRow 32 3 1 987518748038044,
    decodeIntegerRow 32 3 1 1132024538993592,
    decodeIntegerRow 32 3 1 309652567423684,
    decodeIntegerRow 32 3 1 1132777684465032,
    decodeIntegerRow 32 3 1 308020752332764,
    decodeIntegerRow 32 3 1 901082136279352,
    decodeIntegerRow 32 3 1 1002762969321604,
    decodeIntegerRow 32 3 1 865509189223036,
    decodeIntegerRow 32 3 1 906163543767352,
    decodeIntegerRow 32 3 1 1543304773219876,
    decodeIntegerRow 32 3 1 1132213083633032,
    decodeIntegerRow 32 3 1 1545062112540484,
    decodeIntegerRow 32 3 1 1132589656386248,
    decodeIntegerRow 32 3 1 850251020802844,
    decodeIntegerRow 32 3 1 901100732462968,
    decodeIntegerRow 32 3 1 1132213054973124,
    decodeIntegerRow 32 3 1 1543304782768312,
    decodeIntegerRow 32 3 1 946856642249956,
    decodeIntegerRow 32 3 1 987511000573048,
    decodeIntegerRow 32 3 1 901100736005764,
    decodeIntegerRow 32 3 1 850251019621432,
    decodeIntegerRow 32 3 1 720430561201316,
    decodeIntegerRow 32 3 1 307958066727928]

def cols_right0 (r : LeftIndex 5 2 4) : List ℤ := cols_right0Data.getD (leftPosition 5 2 4 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 2 4) : (tripleIndices 2 2 8).map (fun j => (right0Middle5 2 4) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 309652557866488,
    decodeIntegerRow 32 3 1 1132024510336604,
    decodeIntegerRow 32 3 1 865501439868472,
    decodeIntegerRow 32 3 1 946833397020796,
    decodeIntegerRow 32 3 1 1002762970502152,
    decodeIntegerRow 32 3 1 901082139822436,
    decodeIntegerRow 32 3 1 1544999446093768,
    decodeIntegerRow 32 3 1 720242533125444,
    decodeIntegerRow 32 3 1 906186788996872,
    decodeIntegerRow 32 3 1 987518748038044,
    decodeIntegerRow 32 3 1 1132024538993592,
    decodeIntegerRow 32 3 1 309652567423684,
    decodeIntegerRow 32 3 1 1132777684465032,
    decodeIntegerRow 32 3 1 308020752332764,
    decodeIntegerRow 32 3 1 901082136279352,
    decodeIntegerRow 32 3 1 1002762969321604,
    decodeIntegerRow 32 3 1 865509189223036,
    decodeIntegerRow 32 3 1 906163543767352,
    decodeIntegerRow 32 3 1 1543304773219876,
    decodeIntegerRow 32 3 1 1132213083633032,
    decodeIntegerRow 32 3 1 1545062112540484,
    decodeIntegerRow 32 3 1 1132589656386248,
    decodeIntegerRow 32 3 1 850251020802844,
    decodeIntegerRow 32 3 1 901100732462968,
    decodeIntegerRow 32 3 1 1132213054973124,
    decodeIntegerRow 32 3 1 1543304782768312,
    decodeIntegerRow 32 3 1 946856642249956,
    decodeIntegerRow 32 3 1 987511000573048,
    decodeIntegerRow 32 3 1 901100736005764,
    decodeIntegerRow 32 3 1 850251019621432,
    decodeIntegerRow 32 3 1 720430561201316,
    decodeIntegerRow 32 3 1 307958066727928]

def cols_left0 (r : LeftIndex 5 2 4) : List ℤ := cols_left0Data.getD (leftPosition 5 2 4 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 2 4) : (tripleIndices 2 2 8).map (fun j => (left0Middle5 2 4) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1886406220242257726965091503360,
    decodeIntegerRow 32 9 4 3242920701010269624138304844656,
    decodeIntegerRow 32 9 4 1718909456301577828914162657264,
    decodeIntegerRow 32 9 4 1735449825544148874470148428800,
    decodeIntegerRow 32 9 4 1714722675238559701699179183360,
    decodeIntegerRow 32 9 4 1697768795976985729529021908336,
    decodeIntegerRow 32 9 4 1547276954040542922984352524784,
    decodeIntegerRow 32 9 4 190757305194836388813751936000,
    decodeIntegerRow 32 9 4 1886406866251969559386165945600,
    decodeIntegerRow 32 9 4 3242926515097676116430072723344,
    decodeIntegerRow 32 9 4 1718961145053952965973358170896,
    decodeIntegerRow 32 9 4 1735915024315525107996632796160,
    decodeIntegerRow 32 9 4 1718909456301577645900171642880,
    decodeIntegerRow 32 9 4 1735449825544150521596067558256,
    decodeIntegerRow 32 9 4 1886406220242257729196633466864,
    decodeIntegerRow 32 9 4 3242920701010269604054427173120,
    decodeIntegerRow 32 9 4 1718961144957892216368594720000,
    decodeIntegerRow 32 9 4 1697768796841530828839775108976,
    decodeIntegerRow 32 9 4 1547276961918695316291731624944,
    decodeIntegerRow 32 9 4 3242926444194304556077686184960,
    decodeIntegerRow 32 9 4 1886406228120439768595492128000,
    decodeIntegerRow 32 9 4 190763048378604485845937666416,
    decodeIntegerRow 32 9 4 1714774363892472574988850757104,
    decodeIntegerRow 32 9 4 1735449826430307601263592975360,
    decodeIntegerRow 32 9 4 1718909456400039726654998814720,
    decodeIntegerRow 32 9 4 1698233993862203236268260456816,
    decodeIntegerRow 32 9 4 1547277592172072713830814891504,
    decodeIntegerRow 32 9 4 3242920771913907978728032794880,
    decodeIntegerRow 32 9 4 1547276961918695318579062140160,
    decodeIntegerRow 32 9 4 3242926444194304576663660821904,
    decodeIntegerRow 32 9 4 1718961144957892399383274481936,
    decodeIntegerRow 32 9 4 1697768796841532475971892966400]

def cols_right2 (r : LeftIndex 5 2 4) : List ℤ := cols_right2Data.getD (leftPosition 5 2 4 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 2 4) : (tripleIndices 4 1 8).map (fun j => (right2Middle5 2 4) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms524.outerABC * HexagonAtoms524.assocABC = HexagonAtoms524.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms524.assocBAC * HexagonAtoms524.innerABC = HexagonAtoms524.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms524.innerRightABC * HexagonAtoms524.assocABC = HexagonAtoms524.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms524.inverseACB * right0Middle5 2 4 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms524.innerACB * right1Middle5 2 4 = right1Middle5 2 4 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product5_eq : HexagonAtoms524.assocBCA * left0Middle5 2 4 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms524.innerRightBAC * left1Middle5 2 4 = left1Middle5 2 4 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product7_eq : HexagonAtoms524.assocCAB * right2Middle5 2 4 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn524
