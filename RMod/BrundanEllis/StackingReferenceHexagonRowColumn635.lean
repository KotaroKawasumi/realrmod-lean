import RMod.BrundanEllis.StackingReferenceHexagonAtoms635
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn635
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 957017128647724,
    decodeIntegerRow 32 3 1 992608693252844,
    decodeIntegerRow 32 3 1 1133280024975436,
    decodeIntegerRow 32 3 1 1543995162959116,
    decodeIntegerRow 32 3 1 957007840082560,
    decodeIntegerRow 32 3 1 992588518676480,
    decodeIntegerRow 32 3 1 1133217005284480,
    decodeIntegerRow 32 3 1 1543806959388160,
    decodeIntegerRow 32 3 1 1131522685283200,
    decodeIntegerRow 32 3 1 308648453296000,
    decodeIntegerRow 32 3 1 941758960071040,
    decodeIntegerRow 32 3 1 855348684666240,
    decodeIntegerRow 32 3 1 1131585190539268,
    decodeIntegerRow 32 3 1 308460083915452,
    decodeIntegerRow 32 3 1 941763618722212,
    decodeIntegerRow 32 3 1 855327017803548,
    decodeIntegerRow 32 3 1 1133217004576000,
    decodeIntegerRow 32 3 1 309213226157440,
    decodeIntegerRow 32 3 1 957007830557440,
    decodeIntegerRow 32 3 1 860431641468800,
    decodeIntegerRow 32 3 1 719740163167708,
    decodeIntegerRow 32 3 1 1543995159651868,
    decodeIntegerRow 32 3 1 896003050676092,
    decodeIntegerRow 32 3 1 992608664537532,
    decodeIntegerRow 32 3 1 941763609115444,
    decodeIntegerRow 32 3 1 997693199737356,
    decodeIntegerRow 32 3 1 1131585189121876,
    decodeIntegerRow 32 3 1 1544560108007404,
    decodeIntegerRow 32 3 1 911261219176960,
    decodeIntegerRow 32 3 1 855348713346560,
    decodeIntegerRow 32 3 1 721497502151680,
    decodeIntegerRow 32 3 1 308648456366080]

def rows_inverseACB (r : LeftIndex 6 5 3) : List ℤ := rows_inverseACBData.getD (leftPosition 6 5 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 5 3) : (tripleIndices 8 1 4).map ((HexagonAtoms635.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 785902271320004,
    decodeIntegerRow 32 3 1 1574311595748172,
    decodeIntegerRow 32 3 1 1513495185250276,
    decodeIntegerRow 32 3 1 1199357445865388,
    decodeIntegerRow 32 3 1 785818099201244,
    decodeIntegerRow 32 3 1 1574495306477548,
    decodeIntegerRow 32 3 1 1513302157218556,
    decodeIntegerRow 32 3 1 1199316607472012,
    decodeIntegerRow 32 3 1 323706717508372,
    decodeIntegerRow 32 3 1 1202747603659556,
    decodeIntegerRow 32 3 1 1060340097586548,
    decodeIntegerRow 32 3 1 1559627657713924,
    decodeIntegerRow 32 3 1 323904209644492,
    decodeIntegerRow 32 3 1 1202704758544964,
    decodeIntegerRow 32 3 1 1060423291853868,
    decodeIntegerRow 32 3 1 1559806572719716,
    decodeIntegerRow 32 3 1 323706711286612,
    decodeIntegerRow 32 3 1 1202747633083236,
    decodeIntegerRow 32 3 1 1060340125584308,
    decodeIntegerRow 32 3 1 1559627670546244,
    decodeIntegerRow 32 3 1 1529115972989452,
    decodeIntegerRow 32 3 1 650315459722244,
    decodeIntegerRow 32 3 1 792596925004908,
    decodeIntegerRow 32 3 1 293213628966436,
    decodeIntegerRow 32 3 1 1067117890268804,
    decodeIntegerRow 32 3 1 278708605778572,
    decodeIntegerRow 32 3 1 339525010138276,
    decodeIntegerRow 32 3 1 653662773092588,
    decodeIntegerRow 32 3 1 785818071929244,
    decodeIntegerRow 32 3 1 1574495319154348,
    decodeIntegerRow 32 3 1 1513302163751356,
    decodeIntegerRow 32 3 1 1199316637569612]

def rows_assocBCA (r : RightIndex 3 5 6) : List ℤ := rows_assocBCAData.getD (rightPosition 3 5 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_2 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_3 : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 5 6) : (tripleIndices 8 1 4).map ((HexagonAtoms635.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 926411259154012,
    decodeIntegerRow 32 3 1 926531273414948,
    decodeIntegerRow 32 3 1 926467736454588,
    decodeIntegerRow 32 3 1 926418318817732,
    decodeIntegerRow 32 3 1 293867935857760,
    decodeIntegerRow 32 3 1 1062076257240160,
    decodeIntegerRow 32 3 1 655377725757280,
    decodeIntegerRow 32 3 1 339056652246880,
    decodeIntegerRow 32 3 1 926599631606560,
    decodeIntegerRow 32 3 1 926468769571680,
    decodeIntegerRow 32 3 1 926489432002080,
    decodeIntegerRow 32 3 1 926413669771360,
    decodeIntegerRow 32 3 1 324370329104452,
    decodeIntegerRow 32 3 1 1204420744335172,
    decodeIntegerRow 32 3 1 1065465441438628,
    decodeIntegerRow 32 3 1 1574968313414308,
    decodeIntegerRow 32 3 1 339056664844000,
    decodeIntegerRow 32 3 1 1197642435800800,
    decodeIntegerRow 32 3 1 1062076286633440,
    decodeIntegerRow 32 3 1 1559152259292640,
    decodeIntegerRow 32 3 1 926418318815764,
    decodeIntegerRow 32 3 1 926552452401516,
    decodeIntegerRow 32 3 1 926531273410356,
    decodeIntegerRow 32 3 1 926608929696844,
    decodeIntegerRow 32 3 1 278051881893556,
    decodeIntegerRow 32 3 1 1065465411310516,
    decodeIntegerRow 32 3 1 648599416540564,
    decodeIntegerRow 32 3 1 324370316192404,
    decodeIntegerRow 32 3 1 926606519081440,
    decodeIntegerRow 32 3 1 926489431997600,
    decodeIntegerRow 32 3 1 926551419276000,
    decodeIntegerRow 32 3 1 926599631604640]

def rows_assocCAB (r : RightIndex 5 6 3) : List ℤ := rows_assocCABData.getD (rightPosition 5 6 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 6 3) : (tripleIndices 2 4 4).map ((HexagonAtoms635.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 785881637237444,
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
    decodeIntegerRow 32 3 1 323897318939188,
    decodeIntegerRow 32 3 1 1202684095047036,
    decodeIntegerRow 32 3 1 1060361275518932,
    decodeIntegerRow 32 3 1 1559620601199964,
    decodeIntegerRow 32 3 1 1199378595800012,
    decodeIntegerRow 32 3 1 339532072947844,
    decodeIntegerRow 32 3 1 1574502203400748,
    decodeIntegerRow 32 3 1 1067181455568036,
    decodeIntegerRow 32 3 1 293399581116124,
    decodeIntegerRow 32 3 1 1060361305625388,
    decodeIntegerRow 32 3 1 650336121076476,
    decodeIntegerRow 32 3 1 323897331616972,
    decodeIntegerRow 32 3 1 1067181426152996,
    decodeIntegerRow 32 3 1 278517991669972,
    decodeIntegerRow 32 3 1 339532060116484,
    decodeIntegerRow 32 3 1 653641565053748]

def cols_right0 (r : LeftIndex 6 3 5) : List ℤ := cols_right0Data.getD (leftPosition 6 3 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 3 5) : (tripleIndices 8 1 4).map (fun j => (right0Middle6 3 5) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 785881637237444,
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
    decodeIntegerRow 32 3 1 323897318939188,
    decodeIntegerRow 32 3 1 1202684095047036,
    decodeIntegerRow 32 3 1 1060361275518932,
    decodeIntegerRow 32 3 1 1559620601199964,
    decodeIntegerRow 32 3 1 1199378595800012,
    decodeIntegerRow 32 3 1 339532072947844,
    decodeIntegerRow 32 3 1 1574502203400748,
    decodeIntegerRow 32 3 1 1067181455568036,
    decodeIntegerRow 32 3 1 293399581116124,
    decodeIntegerRow 32 3 1 1060361305625388,
    decodeIntegerRow 32 3 1 650336121076476,
    decodeIntegerRow 32 3 1 323897331616972,
    decodeIntegerRow 32 3 1 1067181426152996,
    decodeIntegerRow 32 3 1 278517991669972,
    decodeIntegerRow 32 3 1 339532060116484,
    decodeIntegerRow 32 3 1 653641565053748]

def cols_left0 (r : LeftIndex 6 3 5) : List ℤ := cols_left0Data.getD (leftPosition 6 3 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 3 5) : (tripleIndices 8 1 4).map (fun j => (left0Middle6 3 5) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1716841874640462282931243180144,
    decodeIntegerRow 32 9 4 1716841913648197564351728530576,
    decodeIntegerRow 32 9 4 1716841905768829589800462622064,
    decodeIntegerRow 32 9 4 1716841874737738430765213677456,
    decodeIntegerRow 32 9 4 188899739720148022721580968320,
    decodeIntegerRow 32 9 4 1867543055722529113195025115520,
    decodeIntegerRow 32 9 4 1528465478175913300726153025920,
    decodeIntegerRow 32 9 4 193085882652822109052764789120,
    decodeIntegerRow 32 9 4 1716841945543982064312767013760,
    decodeIntegerRow 32 9 4 1716841905770163764336397736320,
    decodeIntegerRow 32 9 4 1716841906645382259934937535360,
    decodeIntegerRow 32 9 4 1716841874651283920834141710720,
    decodeIntegerRow 32 9 4 192621322888342606904586840976,
    decodeIntegerRow 32 9 4 1905275773955612887269177217936,
    decodeIntegerRow 32 9 4 1867589001193743041149199460496,
    decodeIntegerRow 32 9 4 3245249916599933560073283162256,
    decodeIntegerRow 32 9 4 3240597937639690172286811672960,
    decodeIntegerRow 32 9 4 1528465478175914945345069388160,
    decodeIntegerRow 32 9 4 1566140764569981722325723775360,
    decodeIntegerRow 32 9 4 188899739720147860066962866560,
    decodeIntegerRow 32 9 4 1716841945554774053892640136464,
    decodeIntegerRow 32 9 4 1716841905768829589800424404976,
    decodeIntegerRow 32 9 4 1716841906644314920306158880784,
    decodeIntegerRow 32 9 4 1716841874640462282931246959856,
    decodeIntegerRow 32 9 4 3245249916599933397369075237904,
    decodeIntegerRow 32 9 4 1566094819098771093148535528464,
    decodeIntegerRow 32 9 4 1905275773955614532389501786384,
    decodeIntegerRow 32 9 4 3241062497404170081133522153744,
    decodeIntegerRow 32 9 4 1716841874651283920834137932160,
    decodeIntegerRow 32 9 4 1716841913647130224722949864320,
    decodeIntegerRow 32 9 4 1716841905770163764336435941760,
    decodeIntegerRow 32 9 4 1716841874748530420345086798720]

def cols_right2 (r : LeftIndex 6 3 5) : List ℤ := cols_right2Data.getD (leftPosition 6 3 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 3 5) : (tripleIndices 2 4 4).map (fun j => (right2Middle6 3 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms635.outerABC * HexagonAtoms635.assocABC = HexagonAtoms635.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product1_eq : HexagonAtoms635.assocBAC * HexagonAtoms635.innerABC = HexagonAtoms635.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms635.innerRightABC * HexagonAtoms635.assocABC = HexagonAtoms635.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms635.inverseACB * right0Middle6 3 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms635.innerACB * right1Middle6 3 5 = right1Middle6 3 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms635.assocBCA * left0Middle6 3 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms635.innerRightBAC * left1Middle6 3 5 = left1Middle6 3 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms635.assocCAB * right2Middle6 3 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn635
