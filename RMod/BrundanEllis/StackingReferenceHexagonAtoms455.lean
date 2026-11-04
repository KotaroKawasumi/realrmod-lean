import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms455
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926513452070914,
    decodeIntegerRow 32 3 1 926520511730206,
    decodeIntegerRow 32 3 1 926540313224146,
    decodeIntegerRow 32 3 1 926603850184014,
    decodeIntegerRow 32 3 1 728244560367382,
    decodeIntegerRow 32 3 1 1541641626482422,
    decodeIntegerRow 32 3 1 904480595540518,
    decodeIntegerRow 32 3 1 994858056662278,
    decodeIntegerRow 32 3 1 902786017967338,
    decodeIntegerRow 32 3 1 857597273234698,
    decodeIntegerRow 32 3 1 712993365358042,
    decodeIntegerRow 32 3 1 306294830725882,
    decodeIntegerRow 32 3 1 926477551104766,
    decodeIntegerRow 32 3 1 926604625024994,
    decodeIntegerRow 32 3 1 926506478500654,
    decodeIntegerRow 32 3 1 926520597823666,
    decodeIntegerRow 32 3 1 926499677117242,
    decodeIntegerRow 32 3 1 926506736782438,
    decodeIntegerRow 32 3 1 926416338667338,
    decodeIntegerRow 32 3 1 926479875627862,
    decodeIntegerRow 32 3 1 1541641623280654,
    decodeIntegerRow 32 3 1 728244559265134,
    decodeIntegerRow 32 3 1 994858027846366,
    decodeIntegerRow 32 3 1 904480585620286,
    decodeIntegerRow 32 3 1 995422887037426,
    decodeIntegerRow 32 3 1 950234180096146,
    decodeIntegerRow 32 3 1 1546725354950434,
    decodeIntegerRow 32 3 1 1140026824517314,
    decodeIntegerRow 32 3 1 926604625025478,
    decodeIntegerRow 32 3 1 926477551104922,
    decodeIntegerRow 32 3 1 926520597828022,
    decodeIntegerRow 32 3 1 926506478502058]

def assocABC : Matrix (RightIndex 4 5 5) (LeftIndex 4 5 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 5 5 r) []).getD (leftPosition 4 5 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_0 : (associatorZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_1 : (associatorZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_2 : (associatorZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_3 : (associatorZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_0 : (associatorZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_1 : (associatorZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_2 : (associatorZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_3 : (associatorZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 4 5 5 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_0_2
  · exact assocABC_row_0_0_3
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_1_2
  · exact assocABC_row_0_1_3
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_1_2
  · exact assocABC_row_1_1_3
  · exact assocABC_row_2_0_0
  · exact assocABC_row_2_0_1
  · exact assocABC_row_2_0_2
  · exact assocABC_row_2_0_3
  · exact assocABC_row_2_1_0
  · exact assocABC_row_2_1_1
  · exact assocABC_row_2_1_2
  · exact assocABC_row_2_1_3
  · exact assocABC_row_3_0_0
  · exact assocABC_row_3_0_1
  · exact assocABC_row_3_0_2
  · exact assocABC_row_3_0_3
  · exact assocABC_row_3_1_0
  · exact assocABC_row_3_1_1
  · exact assocABC_row_3_1_2
  · exact assocABC_row_3_1_3

def outerABC : Matrix (LeftIndex 5 5 4) (RightIndex 4 5 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 4 5 5 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_1_2
  · exact outerABC_row_0_1_3
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_1_0
  · exact outerABC_row_2_1_1
  · exact outerABC_row_2_1_2
  · exact outerABC_row_2_1_3
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_1_0
  · exact outerABC_row_3_1_1
  · exact outerABC_row_3_1_2
  · exact outerABC_row_3_1_3

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1201032723063100,
    decodeIntegerRow 32 3 1 331712974219504,
    decodeIntegerRow 32 3 1 1567060025056060,
    decodeIntegerRow 32 3 1 1063769643928336,
    decodeIntegerRow 32 3 1 928302295230768,
    decodeIntegerRow 32 3 1 918581160515500,
    decodeIntegerRow 32 3 1 919208753009872,
    decodeIntegerRow 32 3 1 923211593193900,
    decodeIntegerRow 32 3 1 919208782770580,
    decodeIntegerRow 32 3 1 929808589280592,
    decodeIntegerRow 32 3 1 928302307985300,
    decodeIntegerRow 32 3 1 934439055971248,
    decodeIntegerRow 32 3 1 285960164138896,
    decodeIntegerRow 32 3 1 1063769643766660,
    decodeIntegerRow 32 3 1 651987465714544,
    decodeIntegerRow 32 3 1 331712973853060,
    decodeIntegerRow 32 3 1 929989908446736,
    decodeIntegerRow 32 3 1 919125070184260,
    decodeIntegerRow 32 3 1 934397186923504,
    decodeIntegerRow 32 3 1 928107035304260,
    decodeIntegerRow 32 3 1 1063772054540500,
    decodeIntegerRow 32 3 1 285959647237072,
    decodeIntegerRow 32 3 1 331714007341780,
    decodeIntegerRow 32 3 1 651989704222768,
    decodeIntegerRow 32 3 1 1521306181878448,
    decodeIntegerRow 32 3 1 651989704139500,
    decodeIntegerRow 32 3 1 789248134464592,
    decodeIntegerRow 32 3 1 285959647576300,
    decodeIntegerRow 32 3 1 934397214558460,
    decodeIntegerRow 32 3 1 924913140792944,
    decodeIntegerRow 32 3 1 929989902069500,
    decodeIntegerRow 32 3 1 933895088906896]

def assocBAC : Matrix (RightIndex 5 4 5) (LeftIndex 5 4 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 5 4 5 r) []).getD (leftPosition 5 4 5 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 5 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 5 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 5 4 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 5 4 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_0 : (associatorZ 5 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_1 : (associatorZ 5 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_2 : (associatorZ 5 4 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_3 : (associatorZ 5 4 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 5 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 5 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 5 4 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 5 4 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_0 : (associatorZ 5 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_1 : (associatorZ 5 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_2 : (associatorZ 5 4 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_3 : (associatorZ 5 4 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 5 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 5 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 5 4 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 5 4 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_0 : (associatorZ 5 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_1 : (associatorZ 5 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_2 : (associatorZ 5 4 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_3 : (associatorZ 5 4 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 5 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 5 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 5 4 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 5 4 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_0 : (associatorZ 5 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_1 : (associatorZ 5 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_2 : (associatorZ 5 4 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_3 : (associatorZ 5 4 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 5 4 5 = assocBAC := by
  funext r
  fin_cases r
  · exact assocBAC_row_0_0_0
  · exact assocBAC_row_0_0_1
  · exact assocBAC_row_0_0_2
  · exact assocBAC_row_0_0_3
  · exact assocBAC_row_0_1_0
  · exact assocBAC_row_0_1_1
  · exact assocBAC_row_0_1_2
  · exact assocBAC_row_0_1_3
  · exact assocBAC_row_1_0_0
  · exact assocBAC_row_1_0_1
  · exact assocBAC_row_1_0_2
  · exact assocBAC_row_1_0_3
  · exact assocBAC_row_1_1_0
  · exact assocBAC_row_1_1_1
  · exact assocBAC_row_1_1_2
  · exact assocBAC_row_1_1_3
  · exact assocBAC_row_2_0_0
  · exact assocBAC_row_2_0_1
  · exact assocBAC_row_2_0_2
  · exact assocBAC_row_2_0_3
  · exact assocBAC_row_2_1_0
  · exact assocBAC_row_2_1_1
  · exact assocBAC_row_2_1_2
  · exact assocBAC_row_2_1_3
  · exact assocBAC_row_3_0_0
  · exact assocBAC_row_3_0_1
  · exact assocBAC_row_3_0_2
  · exact assocBAC_row_3_0_3
  · exact assocBAC_row_3_1_0
  · exact assocBAC_row_3_1_1
  · exact assocBAC_row_3_1_2
  · exact assocBAC_row_3_1_3

def innerABC : Matrix (LeftIndex 5 4 5) (LeftIndex 4 5 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_0 : (innerLeftZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_1 : (innerLeftZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_2 : (innerLeftZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_3 : (innerLeftZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_0 : (innerLeftZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_1 : (innerLeftZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_2 : (innerLeftZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_3 : (innerLeftZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 4 5 5 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_1_2
  · exact innerABC_row_0_1_3
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_1_2
  · exact innerABC_row_1_1_3
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_2_1_0
  · exact innerABC_row_2_1_1
  · exact innerABC_row_2_1_2
  · exact innerABC_row_2_1_3
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_3_1_0
  · exact innerABC_row_3_1_1
  · exact innerABC_row_3_1_2
  · exact innerABC_row_3_1_3

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 919165707349492,
    decodeIntegerRow 32 3 1 929899513521796,
    decodeIntegerRow 32 3 1 928204158271828,
    decodeIntegerRow 32 3 1 934417017110884,
    decodeIntegerRow 32 3 1 1567150939375520,
    decodeIntegerRow 32 3 1 789207498322720,
    decodeIntegerRow 32 3 1 1201010683100320,
    decodeIntegerRow 32 3 1 1521209068121120,
    decodeIntegerRow 32 3 1 918603201497440,
    decodeIntegerRow 32 3 1 928204151896480,
    decodeIntegerRow 32 3 1 923120688085600,
    decodeIntegerRow 32 3 1 919165734988960,
    decodeIntegerRow 32 3 1 1521209068462236,
    decodeIntegerRow 32 3 1 652009505594068,
    decodeIntegerRow 32 3 1 789207498243964,
    decodeIntegerRow 32 3 1 285869249108852,
    decodeIntegerRow 32 3 1 286050562265120,
    decodeIntegerRow 32 3 1 1063729007703520,
    decodeIntegerRow 32 3 1 651967664338720,
    decodeIntegerRow 32 3 1 331615860804320,
    decodeIntegerRow 32 3 1 919168117970404,
    decodeIntegerRow 32 3 1 929898996960172,
    decodeIntegerRow 32 3 1 928205191395076,
    decodeIntegerRow 32 3 1 934419255544588,
    decodeIntegerRow 32 3 1 331615860463092,
    decodeIntegerRow 32 3 1 1201052524670596,
    decodeIntegerRow 32 3 1 1063729007782228,
    decodeIntegerRow 32 3 1 1566969626954084,
    decodeIntegerRow 32 3 1 918600963072160,
    decodeIntegerRow 32 3 1 928205185015840,
    decodeIntegerRow 32 3 1 923121204645280,
    decodeIntegerRow 32 3 1 919168145600800]

def innerRightABC : Matrix (RightIndex 4 5 5) (RightIndex 4 5 5) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 4 5 5 r) []).getD (rightPosition 4 5 5 s) 0

private theorem innerRightABC_row_0_0_0 : (innerRightZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_2 : (innerRightZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_3 : (innerRightZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_2 : (innerRightZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_3 : (innerRightZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 4 5 5 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_0_2
  · exact innerRightABC_row_0_0_3
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_1_2
  · exact innerRightABC_row_0_1_3
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_1_2
  · exact innerRightABC_row_1_1_3
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_0_2
  · exact innerRightABC_row_2_0_3
  · exact innerRightABC_row_2_1_0
  · exact innerRightABC_row_2_1_1
  · exact innerRightABC_row_2_1_2
  · exact innerRightABC_row_2_1_3
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_0_2
  · exact innerRightABC_row_3_0_3
  · exact innerRightABC_row_3_1_0
  · exact innerRightABC_row_3_1_1
  · exact innerRightABC_row_3_1_2
  · exact innerRightABC_row_3_1_3

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 903632916144766,
    decodeIntegerRow 32 3 1 857880879853954,
    decodeIntegerRow 32 3 1 720618933633454,
    decodeIntegerRow 32 3 1 308836832065106,
    decodeIntegerRow 32 3 1 995141633520838,
    decodeIntegerRow 32 3 1 949386497866042,
    decodeIntegerRow 32 3 1 1544183615067062,
    decodeIntegerRow 32 3 1 1132401169124938,
    decodeIntegerRow 32 3 1 929048473647238,
    decodeIntegerRow 32 3 1 918874036528762,
    decodeIntegerRow 32 3 1 926761142924662,
    decodeIntegerRow 32 3 1 925568662631818,
    decodeIntegerRow 32 3 1 934125231616834,
    decodeIntegerRow 32 3 1 923964741636286,
    decodeIntegerRow 32 3 1 927263239863826,
    decodeIntegerRow 32 3 1 926196283812334,
    decodeIntegerRow 32 3 1 1132401283916194,
    decodeIntegerRow 32 3 1 308836822499166,
    decodeIntegerRow 32 3 1 949387275895666,
    decodeIntegerRow 32 3 1 857880878791054,
    decodeIntegerRow 32 3 1 308836564218842,
    decodeIntegerRow 32 3 1 1132401197822758,
    decodeIntegerRow 32 3 1 857878554268138,
    decodeIntegerRow 32 3 1 949386501054742,
    decodeIntegerRow 32 3 1 926761142880922,
    decodeIntegerRow 32 3 1 927451526208358,
    decodeIntegerRow 32 3 1 929048473292458,
    decodeIntegerRow 32 3 1 934146152205142,
    decodeIntegerRow 32 3 1 927263239849246,
    decodeIntegerRow 32 3 1 926823905004514,
    decodeIntegerRow 32 3 1 934125231498574,
    decodeIntegerRow 32 3 1 929055446861746]

def inverseACB : Matrix (LeftIndex 4 5 5) (RightIndex 4 5 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 5 5 r) []).getD (rightPosition 4 5 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_2 : (associatorInverseZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_3 : (associatorInverseZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_2 : (associatorInverseZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_3 : (associatorInverseZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 4 5 5 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_0_1_0
  · exact inverseACB_row_0_1_1
  · exact inverseACB_row_0_1_2
  · exact inverseACB_row_0_1_3
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_1_2
  · exact inverseACB_row_1_1_3
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_2_1_0
  · exact inverseACB_row_2_1_1
  · exact inverseACB_row_2_1_2
  · exact inverseACB_row_2_1_3
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_3_1_0
  · exact inverseACB_row_3_1_1
  · exact inverseACB_row_3_1_2
  · exact inverseACB_row_3_1_3

def innerACB : Matrix (LeftIndex 5 4 5) (LeftIndex 4 5 5) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 4 5 5 = innerACB := innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 926488069463848,
    decodeIntegerRow 32 3 1 926608237590568,
    decodeIntegerRow 32 3 1 926601015661672,
    decodeIntegerRow 32 3 1 926553155003752,
    decodeIntegerRow 32 3 1 1519612121036964,
    decodeIntegerRow 32 3 1 659896611985756,
    decodeIntegerRow 32 3 1 796592507646916,
    decodeIntegerRow 32 3 1 289349060125244,
    decodeIntegerRow 32 3 1 926553127290088,
    decodeIntegerRow 32 3 1 926419186312168,
    decodeIntegerRow 32 3 1 926608244309032,
    decodeIntegerRow 32 3 1 926532149306152,
    decodeIntegerRow 32 3 1 289349060124324,
    decodeIntegerRow 32 3 1 1056427681209436,
    decodeIntegerRow 32 3 1 659896611989956,
    decodeIntegerRow 32 3 1 333408067816764,
    decodeIntegerRow 32 3 1 282570751248728,
    decodeIntegerRow 32 3 1 1071114017106472,
    decodeIntegerRow 32 3 1 644080557947032,
    decodeIntegerRow 32 3 1 330018913379048,
    decodeIntegerRow 32 3 1 926550716752444,
    decodeIntegerRow 32 3 1 926419702505404,
    decodeIntegerRow 32 3 1 926607210846556,
    decodeIntegerRow 32 3 1 926529910719196,
    decodeIntegerRow 32 3 1 330018913377048,
    decodeIntegerRow 32 3 1 1208939630909032,
    decodeIntegerRow 32 3 1 1071114017101912,
    decodeIntegerRow 32 3 1 1570449437602088,
    decodeIntegerRow 32 3 1 926529881115964,
    decodeIntegerRow 32 3 1 926412984041404,
    decodeIntegerRow 32 3 1 926419690118236,
    decodeIntegerRow 32 3 1 926469444543196]

def assocBCA : Matrix (RightIndex 5 5 4) (LeftIndex 5 5 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 5 4 r) []).getD (leftPosition 5 5 4 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 5 5 4) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 5 5 4) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 5 5 4) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 5 5 4) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_0 : (associatorZ 5 5 4) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_1 : (associatorZ 5 5 4) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_2 : (associatorZ 5 5 4) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_3 : (associatorZ 5 5 4) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 5 5 4) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 5 5 4) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 5 5 4) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 5 5 4) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_0 : (associatorZ 5 5 4) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_1 : (associatorZ 5 5 4) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_2 : (associatorZ 5 5 4) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_3 : (associatorZ 5 5 4) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 5 5 4) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 5 5 4) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 5 5 4) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 5 5 4) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_0 : (associatorZ 5 5 4) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_1 : (associatorZ 5 5 4) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_2 : (associatorZ 5 5 4) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_3 : (associatorZ 5 5 4) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 5 5 4) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 5 5 4) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 5 5 4) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 5 5 4) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_0 : (associatorZ 5 5 4) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_1 : (associatorZ 5 5 4) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_2 : (associatorZ 5 5 4) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_3 : (associatorZ 5 5 4) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 5 5 4 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_0_1_0
  · exact assocBCA_row_0_1_1
  · exact assocBCA_row_0_1_2
  · exact assocBCA_row_0_1_3
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_1_0
  · exact assocBCA_row_1_1_1
  · exact assocBCA_row_1_1_2
  · exact assocBCA_row_1_1_3
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_0_2
  · exact assocBCA_row_2_0_3
  · exact assocBCA_row_2_1_0
  · exact assocBCA_row_2_1_1
  · exact assocBCA_row_2_1_2
  · exact assocBCA_row_2_1_3
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_0_2
  · exact assocBCA_row_3_0_3
  · exact assocBCA_row_3_1_0
  · exact assocBCA_row_3_1_1
  · exact assocBCA_row_3_1_2
  · exact assocBCA_row_3_1_3

def innerRightBAC : Matrix (RightIndex 5 5 4) (RightIndex 5 4 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 5 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 5 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 5 4 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 5 4 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_0 : (innerRightZ 5 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_1 : (innerRightZ 5 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_2 : (innerRightZ 5 4 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_3 : (innerRightZ 5 4 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 5 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 5 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 5 4 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 5 4 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_0 : (innerRightZ 5 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_1 : (innerRightZ 5 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_2 : (innerRightZ 5 4 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_3 : (innerRightZ 5 4 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 5 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 5 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 5 4 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 5 4 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_0 : (innerRightZ 5 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_1 : (innerRightZ 5 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_2 : (innerRightZ 5 4 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_3 : (innerRightZ 5 4 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 5 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 5 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 5 4 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 5 4 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_0 : (innerRightZ 5 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_1 : (innerRightZ 5 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_2 : (innerRightZ 5 4 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_3 : (innerRightZ 5 4 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 5 4 5 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_0_2
  · exact innerRightBAC_row_0_0_3
  · exact innerRightBAC_row_0_1_0
  · exact innerRightBAC_row_0_1_1
  · exact innerRightBAC_row_0_1_2
  · exact innerRightBAC_row_0_1_3
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_1_1_0
  · exact innerRightBAC_row_1_1_1
  · exact innerRightBAC_row_1_1_2
  · exact innerRightBAC_row_1_1_3
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_0_2
  · exact innerRightBAC_row_2_0_3
  · exact innerRightBAC_row_2_1_0
  · exact innerRightBAC_row_2_1_1
  · exact innerRightBAC_row_2_1_2
  · exact innerRightBAC_row_2_1_3
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_0_2
  · exact innerRightBAC_row_3_0_3
  · exact innerRightBAC_row_3_1_0
  · exact innerRightBAC_row_3_1_1
  · exact innerRightBAC_row_3_1_2
  · exact innerRightBAC_row_3_1_3

def assocCAB : Matrix (RightIndex 5 4 5) (LeftIndex 5 4 5) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 5 4 5 = assocCAB := assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425921,
    decodeIntegerRow 32 3 1 926510094425923,
    decodeIntegerRow 32 3 1 926510094425929,
    decodeIntegerRow 32 3 1 926510094425947,
    decodeIntegerRow 32 3 1 926510094426001,
    decodeIntegerRow 32 3 1 926510094426163,
    decodeIntegerRow 32 3 1 926510094426649,
    decodeIntegerRow 32 3 1 926510094428107,
    decodeIntegerRow 32 3 1 926510094432481,
    decodeIntegerRow 32 3 1 926510094445603,
    decodeIntegerRow 32 3 1 926510094484969,
    decodeIntegerRow 32 3 1 926510094603067,
    decodeIntegerRow 32 3 1 926510094957361,
    decodeIntegerRow 32 3 1 926510096020243,
    decodeIntegerRow 32 3 1 926510099208889,
    decodeIntegerRow 32 3 1 926510108774827,
    decodeIntegerRow 32 3 1 926510051379199,
    decodeIntegerRow 32 3 1 926509965285757,
    decodeIntegerRow 32 3 1 926509707005431,
    decodeIntegerRow 32 3 1 926508932164453,
    decodeIntegerRow 32 3 1 926506607641519,
    decodeIntegerRow 32 3 1 926499634072717,
    decodeIntegerRow 32 3 1 926478713366311,
    decodeIntegerRow 32 3 1 926415951247093,
    decodeIntegerRow 32 3 1 926227664889439,
    decodeIntegerRow 32 3 1 925662805816477,
    decodeIntegerRow 32 3 1 923968228597591,
    decodeIntegerRow 32 3 1 918884496940933,
    decodeIntegerRow 32 3 1 903633301970959,
    decodeIntegerRow 32 3 1 857879717061037,
    decodeIntegerRow 32 3 1 720618962331271,
    decodeIntegerRow 32 3 1 308836698141973]

def outerLeftABC : Matrix (RightIndex 5 4 5) (LeftIndex 4 5 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 4 5 r) []).getD (leftPosition 4 5 5 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 4 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 4 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 4 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 4 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 4 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 4 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 4 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 4 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 4 5 5 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_1_2
  · exact outerLeftABC_row_0_1_3
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_1_2
  · exact outerLeftABC_row_1_1_3
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_1_0
  · exact outerLeftABC_row_2_1_1
  · exact outerLeftABC_row_2_1_2
  · exact outerLeftABC_row_2_1_3
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_1_0
  · exact outerLeftABC_row_3_1_1
  · exact outerLeftABC_row_3_1_2
  · exact outerLeftABC_row_3_1_3

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms455
