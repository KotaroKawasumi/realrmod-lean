import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 919168059507520,
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

def assocABC : Matrix (RightIndex 3 3 7) (LeftIndex 3 3 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 3 7 r) []).getD (leftPosition 3 3 7 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_4 : (associatorZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_5 : (associatorZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_6 : (associatorZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_7 : (associatorZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_4 : (associatorZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_5 : (associatorZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_6 : (associatorZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_7 : (associatorZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 3 7 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_0_2
  · exact assocABC_row_0_0_3
  · exact assocABC_row_0_0_4
  · exact assocABC_row_0_0_5
  · exact assocABC_row_0_0_6
  · exact assocABC_row_0_0_7
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_1_2
  · exact assocABC_row_0_1_3
  · exact assocABC_row_0_1_4
  · exact assocABC_row_0_1_5
  · exact assocABC_row_0_1_6
  · exact assocABC_row_0_1_7
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_0_4
  · exact assocABC_row_1_0_5
  · exact assocABC_row_1_0_6
  · exact assocABC_row_1_0_7
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_1_2
  · exact assocABC_row_1_1_3
  · exact assocABC_row_1_1_4
  · exact assocABC_row_1_1_5
  · exact assocABC_row_1_1_6
  · exact assocABC_row_1_1_7

def outerABC : Matrix (LeftIndex 3 7 3) (RightIndex 3 3 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_4 : (outerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_5 : (outerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_6 : (outerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_7 : (outerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_4 : (outerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_5 : (outerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_6 : (outerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_7 : (outerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 3 7 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_0_0_4
  · exact outerABC_row_0_0_5
  · exact outerABC_row_0_0_6
  · exact outerABC_row_0_0_7
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_1_2
  · exact outerABC_row_0_1_3
  · exact outerABC_row_0_1_4
  · exact outerABC_row_0_1_5
  · exact outerABC_row_0_1_6
  · exact outerABC_row_0_1_7
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_0_4
  · exact outerABC_row_1_0_5
  · exact outerABC_row_1_0_6
  · exact outerABC_row_1_0_7
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_1_1_4
  · exact outerABC_row_1_1_5
  · exact outerABC_row_1_1_6
  · exact outerABC_row_1_1_7

def assocBAC : Matrix (RightIndex 3 3 7) (LeftIndex 3 3 7) ℤ := assocABC

theorem assocBAC_eq : associatorZ 3 3 7 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 919168045652788,
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

def innerABC : Matrix (LeftIndex 3 3 7) (LeftIndex 3 3 7) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 3 3 7 r) []).getD (leftPosition 3 3 7 s) 0

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_4 : (innerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_5 : (innerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_6 : (innerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_7 : (innerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_4 : (innerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_5 : (innerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_6 : (innerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_7 : (innerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 3 7 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_0_0_4
  · exact innerABC_row_0_0_5
  · exact innerABC_row_0_0_6
  · exact innerABC_row_0_0_7
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_0_4
  · exact innerABC_row_1_0_5
  · exact innerABC_row_1_0_6
  · exact innerABC_row_1_0_7
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_2_0_4
  · exact innerABC_row_2_0_5
  · exact innerABC_row_2_0_6
  · exact innerABC_row_2_0_7
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_3_0_4
  · exact innerABC_row_3_0_5
  · exact innerABC_row_3_0_6
  · exact innerABC_row_3_0_7

def innerRightABC : Matrix (RightIndex 3 7 3) (RightIndex 3 3 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 3 3 7) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_4 : (innerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_5 : (innerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_6 : (innerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_7 : (innerRightZ 3 3 7) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 3 3 7) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_4 : (innerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_5 : (innerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_6 : (innerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_7 : (innerRightZ 3 3 7) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 3 7 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_0_2
  · exact innerRightABC_row_0_0_3
  · exact innerRightABC_row_0_0_4
  · exact innerRightABC_row_0_0_5
  · exact innerRightABC_row_0_0_6
  · exact innerRightABC_row_0_0_7
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_1_2
  · exact innerRightABC_row_0_1_3
  · exact innerRightABC_row_0_1_4
  · exact innerRightABC_row_0_1_5
  · exact innerRightABC_row_0_1_6
  · exact innerRightABC_row_0_1_7
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_0_4
  · exact innerRightABC_row_1_0_5
  · exact innerRightABC_row_1_0_6
  · exact innerRightABC_row_1_0_7
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_1_2
  · exact innerRightABC_row_1_1_3
  · exact innerRightABC_row_1_1_4
  · exact innerRightABC_row_1_1_5
  · exact innerRightABC_row_1_1_6
  · exact innerRightABC_row_1_1_7

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926511256687468,
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

def inverseACB : Matrix (LeftIndex 3 7 3) (RightIndex 3 7 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 7 3 r) []).getD (rightPosition 3 7 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_4 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_5 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_6 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_7 : (associatorInverseZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_4 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_5 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_6 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_7 : (associatorInverseZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 7 3 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_0_0_4
  · exact inverseACB_row_0_0_5
  · exact inverseACB_row_0_0_6
  · exact inverseACB_row_0_0_7
  · exact inverseACB_row_0_1_0
  · exact inverseACB_row_0_1_1
  · exact inverseACB_row_0_1_2
  · exact inverseACB_row_0_1_3
  · exact inverseACB_row_0_1_4
  · exact inverseACB_row_0_1_5
  · exact inverseACB_row_0_1_6
  · exact inverseACB_row_0_1_7
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_0_4
  · exact inverseACB_row_1_0_5
  · exact inverseACB_row_1_0_6
  · exact inverseACB_row_1_0_7
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_1_2
  · exact inverseACB_row_1_1_3
  · exact inverseACB_row_1_1_4
  · exact inverseACB_row_1_1_5
  · exact inverseACB_row_1_1_6
  · exact inverseACB_row_1_1_7

def innerACB : Matrix (LeftIndex 7 3 3) (LeftIndex 3 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_0 : (innerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_1 : (innerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_2 : (innerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_3 : (innerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_4 : (innerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_5 : (innerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_6 : (innerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_7 : (innerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_0 : (innerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_1 : (innerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_2 : (innerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_3 : (innerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_4 : (innerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_5 : (innerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_6 : (innerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_7 : (innerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 7 3 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_0_0_4
  · exact innerACB_row_0_0_5
  · exact innerACB_row_0_0_6
  · exact innerACB_row_0_0_7
  · exact innerACB_row_0_1_0
  · exact innerACB_row_0_1_1
  · exact innerACB_row_0_1_2
  · exact innerACB_row_0_1_3
  · exact innerACB_row_0_1_4
  · exact innerACB_row_0_1_5
  · exact innerACB_row_0_1_6
  · exact innerACB_row_0_1_7
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_1_0_4
  · exact innerACB_row_1_0_5
  · exact innerACB_row_1_0_6
  · exact innerACB_row_1_0_7
  · exact innerACB_row_1_1_0
  · exact innerACB_row_1_1_1
  · exact innerACB_row_1_1_2
  · exact innerACB_row_1_1_3
  · exact innerACB_row_1_1_4
  · exact innerACB_row_1_1_5
  · exact innerACB_row_1_1_6
  · exact innerACB_row_1_1_7

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 926511256687468,
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

def assocBCA : Matrix (RightIndex 3 7 3) (LeftIndex 3 7 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 3 7 3 r) []).getD (leftPosition 3 7 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_4 : (associatorZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_5 : (associatorZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_6 : (associatorZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_7 : (associatorZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_0 : (associatorZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_1 : (associatorZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_2 : (associatorZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_3 : (associatorZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_4 : (associatorZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_5 : (associatorZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_6 : (associatorZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_7 : (associatorZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_4 : (associatorZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_5 : (associatorZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_6 : (associatorZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_7 : (associatorZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_0 : (associatorZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_1 : (associatorZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_2 : (associatorZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_3 : (associatorZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_4 : (associatorZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_5 : (associatorZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_6 : (associatorZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_7 : (associatorZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 3 7 3 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_0_0_4
  · exact assocBCA_row_0_0_5
  · exact assocBCA_row_0_0_6
  · exact assocBCA_row_0_0_7
  · exact assocBCA_row_0_1_0
  · exact assocBCA_row_0_1_1
  · exact assocBCA_row_0_1_2
  · exact assocBCA_row_0_1_3
  · exact assocBCA_row_0_1_4
  · exact assocBCA_row_0_1_5
  · exact assocBCA_row_0_1_6
  · exact assocBCA_row_0_1_7
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_0_4
  · exact assocBCA_row_1_0_5
  · exact assocBCA_row_1_0_6
  · exact assocBCA_row_1_0_7
  · exact assocBCA_row_1_1_0
  · exact assocBCA_row_1_1_1
  · exact assocBCA_row_1_1_2
  · exact assocBCA_row_1_1_3
  · exact assocBCA_row_1_1_4
  · exact assocBCA_row_1_1_5
  · exact assocBCA_row_1_1_6
  · exact assocBCA_row_1_1_7

def innerRightBAC : Matrix (RightIndex 3 7 3) (RightIndex 3 3 7) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 3 7 = innerRightBAC := innerRightABC_eq

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 781243955833280,
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

def assocCAB : Matrix (RightIndex 7 3 3) (LeftIndex 7 3 3) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 3 3 r) []).getD (leftPosition 7 3 3 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_4 : (associatorZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_5 : (associatorZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_6 : (associatorZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_7 : (associatorZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_4 : (associatorZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_5 : (associatorZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_6 : (associatorZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_7 : (associatorZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_0 : (associatorZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_1 : (associatorZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_2 : (associatorZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_3 : (associatorZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_4 : (associatorZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_5 : (associatorZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_6 : (associatorZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_7 : (associatorZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_0 : (associatorZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_1 : (associatorZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_2 : (associatorZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_3 : (associatorZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_4 : (associatorZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_5 : (associatorZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_6 : (associatorZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_7 : (associatorZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 7 3 3 = assocCAB := by
  funext r
  fin_cases r
  · exact assocCAB_row_0_0_0
  · exact assocCAB_row_0_0_1
  · exact assocCAB_row_0_0_2
  · exact assocCAB_row_0_0_3
  · exact assocCAB_row_0_0_4
  · exact assocCAB_row_0_0_5
  · exact assocCAB_row_0_0_6
  · exact assocCAB_row_0_0_7
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_1_0_4
  · exact assocCAB_row_1_0_5
  · exact assocCAB_row_1_0_6
  · exact assocCAB_row_1_0_7
  · exact assocCAB_row_2_0_0
  · exact assocCAB_row_2_0_1
  · exact assocCAB_row_2_0_2
  · exact assocCAB_row_2_0_3
  · exact assocCAB_row_2_0_4
  · exact assocCAB_row_2_0_5
  · exact assocCAB_row_2_0_6
  · exact assocCAB_row_2_0_7
  · exact assocCAB_row_3_0_0
  · exact assocCAB_row_3_0_1
  · exact assocCAB_row_3_0_2
  · exact assocCAB_row_3_0_3
  · exact assocCAB_row_3_0_4
  · exact assocCAB_row_3_0_5
  · exact assocCAB_row_3_0_6
  · exact assocCAB_row_3_0_7

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094426434,
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

def outerLeftABC : Matrix (RightIndex 7 3 3) (LeftIndex 3 3 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 3 3 r) []).getD (leftPosition 3 3 7 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 3 7 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_0_0_4
  · exact outerLeftABC_row_0_0_5
  · exact outerLeftABC_row_0_0_6
  · exact outerLeftABC_row_0_0_7
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_0_4
  · exact outerLeftABC_row_1_0_5
  · exact outerLeftABC_row_1_0_6
  · exact outerLeftABC_row_1_0_7
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_0_4
  · exact outerLeftABC_row_2_0_5
  · exact outerLeftABC_row_2_0_6
  · exact outerLeftABC_row_2_0_7
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_0_4
  · exact outerLeftABC_row_3_0_5
  · exact outerLeftABC_row_3_0_6
  · exact outerLeftABC_row_3_0_7

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337
