import RMod.BrundanEllis.StackingReferenceHexagonAtoms337
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn337
open Superfusion

theorem assocBAC_alias : HexagonAtoms337.assocBAC = HexagonAtoms337.assocABC :=
  HexagonAtoms337.assocBAC_eq.symm.trans HexagonAtoms337.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms337.innerRightBAC = HexagonAtoms337.innerRightABC :=
  HexagonAtoms337.innerRightBAC_eq.symm.trans HexagonAtoms337.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 919168059507520,
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

def rows_assocABC (r : RightIndex 3 3 7) : List ℤ := rows_assocABCData.getD (rightPosition 3 3 7 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 3 3 7) : (tripleIndices 4 1 8).map ((HexagonAtoms337.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_0_2
  · exact rows_assocABC_eq_0_0_3
  · exact rows_assocABC_eq_0_0_4
  · exact rows_assocABC_eq_0_0_5
  · exact rows_assocABC_eq_0_0_6
  · exact rows_assocABC_eq_0_0_7
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_1_1
  · exact rows_assocABC_eq_0_1_2
  · exact rows_assocABC_eq_0_1_3
  · exact rows_assocABC_eq_0_1_4
  · exact rows_assocABC_eq_0_1_5
  · exact rows_assocABC_eq_0_1_6
  · exact rows_assocABC_eq_0_1_7
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_0_2
  · exact rows_assocABC_eq_1_0_3
  · exact rows_assocABC_eq_1_0_4
  · exact rows_assocABC_eq_1_0_5
  · exact rows_assocABC_eq_1_0_6
  · exact rows_assocABC_eq_1_0_7
  · exact rows_assocABC_eq_1_1_0
  · exact rows_assocABC_eq_1_1_1
  · exact rows_assocABC_eq_1_1_2
  · exact rows_assocABC_eq_1_1_3
  · exact rows_assocABC_eq_1_1_4
  · exact rows_assocABC_eq_1_1_5
  · exact rows_assocABC_eq_1_1_6
  · exact rows_assocABC_eq_1_1_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 926511256687468,
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

def rows_inverseACB (r : LeftIndex 3 7 3) : List ℤ := rows_inverseACBData.getD (leftPosition 3 7 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 7 3) : (tripleIndices 2 2 8).map ((HexagonAtoms337.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 926511256687468,
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

def rows_assocBCA (r : RightIndex 3 7 3) : List ℤ := rows_assocBCAData.getD (rightPosition 3 7 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 7 3) : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 781243955833280,
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

def rows_assocCAB (r : RightIndex 7 3 3) : List ℤ := rows_assocCABData.getD (rightPosition 7 3 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 7 3 3) : (tripleIndices 2 2 8).map ((HexagonAtoms337.assocCAB) r) = rows_assocCAB r := by
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

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 919168045652788,
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

def cols_innerABC (r : LeftIndex 3 3 7) : List ℤ := cols_innerABCData.getD (leftPosition 3 3 7 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 3 3 7) : (tripleIndices 4 1 8).map (fun j => (HexagonAtoms337.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_0_4
  · exact cols_innerABC_eq_0_0_5
  · exact cols_innerABC_eq_0_0_6
  · exact cols_innerABC_eq_0_0_7
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_0_2
  · exact cols_innerABC_eq_1_0_3
  · exact cols_innerABC_eq_1_0_4
  · exact cols_innerABC_eq_1_0_5
  · exact cols_innerABC_eq_1_0_6
  · exact cols_innerABC_eq_1_0_7
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_0_1
  · exact cols_innerABC_eq_2_0_2
  · exact cols_innerABC_eq_2_0_3
  · exact cols_innerABC_eq_2_0_4
  · exact cols_innerABC_eq_2_0_5
  · exact cols_innerABC_eq_2_0_6
  · exact cols_innerABC_eq_2_0_7
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_0_1
  · exact cols_innerABC_eq_3_0_2
  · exact cols_innerABC_eq_3_0_3
  · exact cols_innerABC_eq_3_0_4
  · exact cols_innerABC_eq_3_0_5
  · exact cols_innerABC_eq_3_0_6
  · exact cols_innerABC_eq_3_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 928205880143908,
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

def cols_right0 (r : LeftIndex 3 3 7) : List ℤ := cols_right0Data.getD (leftPosition 3 3 7 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 3 7) : (tripleIndices 2 2 8).map (fun j => (right0Middle3 3 7) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 928205880143908,
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

def cols_left0 (r : LeftIndex 3 3 7) : List ℤ := cols_left0Data.getD (leftPosition 3 3 7 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 3 7) : (tripleIndices 2 2 8).map (fun j => (left0Middle3 3 7) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 11641412782669555664064,
    decodeIntegerRow 32 5 2 11640937089917602539072,
    decodeIntegerRow 32 5 2 11638556718814086914112,
    decodeIntegerRow 32 5 2 11626607179702758789312,
    decodeIntegerRow 32 5 2 11567026376419068165312,
    decodeIntegerRow 32 5 2 11269003154373165045312,
    decodeIntegerRow 32 5 2 9778887041091899445312,
    decodeIntegerRow 32 5 2 2328306398391821445312,
    decodeIntegerRow 32 5 2 11641413164139282226560,
    decodeIntegerRow 32 5 2 11640935182568969726552,
    decodeIntegerRow 32 5 2 11638547182070922851512,
    decodeIntegerRow 32 5 2 11626654863418579101312,
    decodeIntegerRow 32 5 2 11567026377029419725312,
    decodeIntegerRow 32 5 2 11269003151321407220312,
    decodeIntegerRow 32 5 2 9778887025833110320312,
    decodeIntegerRow 32 5 2 2328306474685766445312,
    decodeIntegerRow 32 5 2 20954757890701391445312,
    decodeIntegerRow 32 5 2 13504177339553813445312,
    decodeIntegerRow 32 5 2 11269003151321415045312,
    decodeIntegerRow 32 5 2 11567026377029418165312,
    decodeIntegerRow 32 5 2 11656409502090454101312,
    decodeIntegerRow 32 5 2 11644517183291625976512,
    decodeIntegerRow 32 5 2 11640935182573852539072,
    decodeIntegerRow 32 5 2 11641413164138305664064,
    decodeIntegerRow 32 5 2 20954757966995337070312,
    decodeIntegerRow 32 5 2 13504177324295024445312,
    decodeIntegerRow 32 5 2 11269003154373172845312,
    decodeIntegerRow 32 5 2 11567026376419066600312,
    decodeIntegerRow 32 5 2 11656457185806274414312,
    decodeIntegerRow 32 5 2 11644507646548461914112,
    decodeIntegerRow 32 5 2 11640937089922485351552,
    decodeIntegerRow 32 5 2 11641412782668579101560]

def cols_right2 (r : LeftIndex 3 3 7) : List ℤ := cols_right2Data.getD (leftPosition 3 3 7 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 3 7) : (tripleIndices 2 2 8).map (fun j => (right2Middle3 3 7) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms337.outerABC * HexagonAtoms337.assocABC = HexagonAtoms337.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms337.assocABC * HexagonAtoms337.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms337.innerRightABC * HexagonAtoms337.assocABC = HexagonAtoms337.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms337.inverseACB * right0Middle3 3 7 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms337.innerACB * right1Middle3 3 7 = right1Middle3 3 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product5_eq : HexagonAtoms337.assocBCA * left0Middle3 3 7 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms337.innerRightABC * left1Middle3 3 7 = left1Middle3 3 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product7_eq : HexagonAtoms337.assocCAB * right2Middle3 3 7 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn337
