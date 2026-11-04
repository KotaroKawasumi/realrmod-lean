import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 995140486139710,
    decodeIntegerRow 32 3 1 903633306753928,
    decodeIntegerRow 32 3 1 1544183489115544,
    decodeIntegerRow 32 3 1 720618961799830,
    decodeIntegerRow 32 3 1 926792523903352,
    decodeIntegerRow 32 3 1 927357383212510,
    decodeIntegerRow 32 3 1 929051960260810,
    decodeIntegerRow 32 3 1 934135691891224,
    decodeIntegerRow 32 3 1 720618962862712,
    decodeIntegerRow 32 3 1 1544183492304190,
    decodeIntegerRow 32 3 1 949386891663850,
    decodeIntegerRow 32 3 1 857879731409944,
    decodeIntegerRow 32 3 1 934135691930590,
    decodeIntegerRow 32 3 1 929051960247688,
    decodeIntegerRow 32 3 1 925662805993624,
    decodeIntegerRow 32 3 1 926227664830390,
    decodeIntegerRow 32 3 1 926541475485610,
    decodeIntegerRow 32 3 1 926415951247336,
    decodeIntegerRow 32 3 1 926506607642248,
    decodeIntegerRow 32 3 1 926520554781310,
    decodeIntegerRow 32 3 1 926511256687384,
    decodeIntegerRow 32 3 1 926510481846410,
    decodeIntegerRow 32 3 1 926509965285730,
    decodeIntegerRow 32 3 1 926510051379208,
    decodeIntegerRow 32 3 1 926499634074904,
    decodeIntegerRow 32 3 1 926513581211050,
    decodeIntegerRow 32 3 1 926415951246850,
    decodeIntegerRow 32 3 1 926541475485448,
    decodeIntegerRow 32 3 1 926510137472650,
    decodeIntegerRow 32 3 1 926510223566056,
    decodeIntegerRow 32 3 1 926510481846408,
    decodeIntegerRow 32 3 1 926511256687390]

def assocABC : Matrix (RightIndex 3 2 5) (LeftIndex 3 2 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 2 5 r) []).getD (leftPosition 3 2 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_0 : (associatorZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_1 : (associatorZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_2 : (associatorZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_3 : (associatorZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_0 : (associatorZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_1 : (associatorZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_2 : (associatorZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_3 : (associatorZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 2 5 = assocABC := by
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

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425921,
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

def outerABC : Matrix (LeftIndex 2 5 3) (RightIndex 3 2 5) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 5 3 r) []).getD (rightPosition 3 2 5 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 2 5 = outerABC := by
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

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 929989890377764,
    decodeIntegerRow 32 3 1 918622981733592,
    decodeIntegerRow 32 3 1 933811417772996,
    decodeIntegerRow 32 3 1 924717873426328,
    decodeIntegerRow 32 3 1 924717901061284,
    decodeIntegerRow 32 3 1 933811424150232,
    decodeIntegerRow 32 3 1 934397194363716,
    decodeIntegerRow 32 3 1 923030268713368,
    decodeIntegerRow 32 3 1 929808607349608,
    decodeIntegerRow 32 3 1 918581153075364,
    decodeIntegerRow 32 3 1 933895106975912,
    decodeIntegerRow 32 3 1 924913160987716,
    decodeIntegerRow 32 3 1 928107055499032,
    decodeIntegerRow 32 3 1 919125088253276,
    decodeIntegerRow 32 3 1 918581140320728,
    decodeIntegerRow 32 3 1 929808577588924,
    decodeIntegerRow 32 3 1 1521307214857192,
    decodeIntegerRow 32 3 1 1063769643677884,
    decodeIntegerRow 32 3 1 651989703997912,
    decodeIntegerRow 32 3 1 285959647487524,
    decodeIntegerRow 32 3 1 1567060541525992,
    decodeIntegerRow 32 3 1 1201030484487484,
    decodeIntegerRow 32 3 1 1063769644017112,
    decodeIntegerRow 32 3 1 1521307214773924,
    decodeIntegerRow 32 3 1 331714007194684,
    decodeIntegerRow 32 3 1 789248134216408,
    decodeIntegerRow 32 3 1 1201032722916004,
    decodeIntegerRow 32 3 1 1567060024961128,
    decodeIntegerRow 32 3 1 1567060024807876,
    decodeIntegerRow 32 3 1 1201032723284392,
    decodeIntegerRow 32 3 1 1063772054292316,
    decodeIntegerRow 32 3 1 1521306181731352]

def assocBAC : Matrix (RightIndex 2 3 5) (LeftIndex 2 3 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 3 5 r) []).getD (leftPosition 2 3 5 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 2 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 2 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 2 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 2 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 2 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 2 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 2 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 2 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 2 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 2 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 2 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 2 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 2 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 2 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 2 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 2 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_0 : (associatorZ 2 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_1 : (associatorZ 2 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_2 : (associatorZ 2 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_3 : (associatorZ 2 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_0 : (associatorZ 2 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_1 : (associatorZ 2 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_2 : (associatorZ 2 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_3 : (associatorZ 2 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_0 : (associatorZ 2 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_1 : (associatorZ 2 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_2 : (associatorZ 2 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_3 : (associatorZ 2 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_0 : (associatorZ 2 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_1 : (associatorZ 2 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_2 : (associatorZ 2 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_3 : (associatorZ 2 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 2 3 5 = assocBAC := by
  funext r
  fin_cases r
  · exact assocBAC_row_0_0_0
  · exact assocBAC_row_0_0_1
  · exact assocBAC_row_0_0_2
  · exact assocBAC_row_0_0_3
  · exact assocBAC_row_1_0_0
  · exact assocBAC_row_1_0_1
  · exact assocBAC_row_1_0_2
  · exact assocBAC_row_1_0_3
  · exact assocBAC_row_2_0_0
  · exact assocBAC_row_2_0_1
  · exact assocBAC_row_2_0_2
  · exact assocBAC_row_2_0_3
  · exact assocBAC_row_3_0_0
  · exact assocBAC_row_3_0_1
  · exact assocBAC_row_3_0_2
  · exact assocBAC_row_3_0_3
  · exact assocBAC_row_4_0_0
  · exact assocBAC_row_4_0_1
  · exact assocBAC_row_4_0_2
  · exact assocBAC_row_4_0_3
  · exact assocBAC_row_5_0_0
  · exact assocBAC_row_5_0_1
  · exact assocBAC_row_5_0_2
  · exact assocBAC_row_5_0_3
  · exact assocBAC_row_6_0_0
  · exact assocBAC_row_6_0_1
  · exact assocBAC_row_6_0_2
  · exact assocBAC_row_6_0_3
  · exact assocBAC_row_7_0_0
  · exact assocBAC_row_7_0_1
  · exact assocBAC_row_7_0_2
  · exact assocBAC_row_7_0_3

def innerABC : Matrix (LeftIndex 2 3 5) (LeftIndex 3 2 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 4) (Fin 2 × Fin 4 × Fin 4) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_2_0 : (innerLeftZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_2_1 : (innerLeftZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_2_2 : (innerLeftZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_2_3 : (innerLeftZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_3_0 : (innerLeftZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_3_1 : (innerLeftZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_3_2 : (innerLeftZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_3_3 : (innerLeftZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_2_0 : (innerLeftZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_2_1 : (innerLeftZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_2_2 : (innerLeftZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_2_3 : (innerLeftZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_3_0 : (innerLeftZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_3_1 : (innerLeftZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_3_2 : (innerLeftZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_3_3 : (innerLeftZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 2 5 = innerABC := by
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
  · exact innerABC_row_0_2_0
  · exact innerABC_row_0_2_1
  · exact innerABC_row_0_2_2
  · exact innerABC_row_0_2_3
  · exact innerABC_row_0_3_0
  · exact innerABC_row_0_3_1
  · exact innerABC_row_0_3_2
  · exact innerABC_row_0_3_3
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_1_2
  · exact innerABC_row_1_1_3
  · exact innerABC_row_1_2_0
  · exact innerABC_row_1_2_1
  · exact innerABC_row_1_2_2
  · exact innerABC_row_1_2_3
  · exact innerABC_row_1_3_0
  · exact innerABC_row_1_3_1
  · exact innerABC_row_1_3_2
  · exact innerABC_row_1_3_3

def innerRightABC : Matrix (RightIndex 3 5 2) (RightIndex 3 2 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 3 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_2 : (innerRightZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_3 : (innerRightZ 3 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 3 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_2 : (innerRightZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_3 : (innerRightZ 3 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 2 5 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 335200020088964,
    decodeIntegerRow 32 3 1 781384259565772,
    decodeIntegerRow 32 3 1 1208396883005476,
    decodeIntegerRow 32 3 1 1565455852328108,
    decodeIntegerRow 32 3 1 284174161720212,
    decodeIntegerRow 32 3 1 659312022594844,
    decodeIntegerRow 32 3 1 797198102809612,
    decodeIntegerRow 32 3 1 328422221398724,
    decodeIntegerRow 32 3 1 328422227406708,
    decodeIntegerRow 32 3 1 797198075021764,
    decodeIntegerRow 32 3 1 1193708136413332,
    decodeIntegerRow 32 3 1 1568846039545956,
    decodeIntegerRow 32 3 1 1565455839231324,
    decodeIntegerRow 32 3 1 1208396912691628,
    decodeIntegerRow 32 3 1 1071635901813124,
    decodeIntegerRow 32 3 1 1517820175505588,
    decodeIntegerRow 32 3 1 659351483230708,
    decodeIntegerRow 32 3 1 1568663693634884,
    decodeIntegerRow 32 3 1 328226450921492,
    decodeIntegerRow 32 3 1 1055903558230756,
    decodeIntegerRow 32 3 1 781298365788124,
    decodeIntegerRow 32 3 1 1518014918873388,
    decodeIntegerRow 32 3 1 1565275559564804,
    decodeIntegerRow 32 3 1 644667528193588,
    decodeIntegerRow 32 3 1 644667557871364,
    decodeIntegerRow 32 3 1 1565275572659532,
    decodeIntegerRow 32 3 1 335005276725156,
    decodeIntegerRow 32 3 1 1071721850545708,
    decodeIntegerRow 32 3 1 1055903530433812,
    decodeIntegerRow 32 3 1 328226444909724,
    decodeIntegerRow 32 3 1 284356507629452,
    decodeIntegerRow 32 3 1 1193668735456324]

def inverseACB : Matrix (LeftIndex 3 5 2) (RightIndex 3 5 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 5 2 r) []).getD (rightPosition 3 5 2 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 5 2 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_4_0_0
  · exact inverseACB_row_4_0_1
  · exact inverseACB_row_4_0_2
  · exact inverseACB_row_4_0_3
  · exact inverseACB_row_5_0_0
  · exact inverseACB_row_5_0_1
  · exact inverseACB_row_5_0_2
  · exact inverseACB_row_5_0_3
  · exact inverseACB_row_6_0_0
  · exact inverseACB_row_6_0_1
  · exact inverseACB_row_6_0_2
  · exact inverseACB_row_6_0_3
  · exact inverseACB_row_7_0_0
  · exact inverseACB_row_7_0_1
  · exact inverseACB_row_7_0_2
  · exact inverseACB_row_7_0_3

def innerACB : Matrix (LeftIndex 5 3 2) (LeftIndex 3 5 2) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_0 : (innerLeftZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_1 : (innerLeftZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_2 : (innerLeftZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_3 : (innerLeftZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_0 : (innerLeftZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_1 : (innerLeftZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_2 : (innerLeftZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_3 : (innerLeftZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_0 : (innerLeftZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_1 : (innerLeftZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_2 : (innerLeftZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_3 : (innerLeftZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_0 : (innerLeftZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_1 : (innerLeftZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_2 : (innerLeftZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_3 : (innerLeftZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 5 2 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_0_2
  · exact innerACB_row_2_0_3
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_0_2
  · exact innerACB_row_3_0_3
  · exact innerACB_row_4_0_0
  · exact innerACB_row_4_0_1
  · exact innerACB_row_4_0_2
  · exact innerACB_row_4_0_3
  · exact innerACB_row_5_0_0
  · exact innerACB_row_5_0_1
  · exact innerACB_row_5_0_2
  · exact innerACB_row_5_0_3
  · exact innerACB_row_6_0_0
  · exact innerACB_row_6_0_1
  · exact innerACB_row_6_0_2
  · exact innerACB_row_6_0_3
  · exact innerACB_row_7_0_0
  · exact innerACB_row_7_0_1
  · exact innerACB_row_7_0_2
  · exact innerACB_row_7_0_3

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 1517820175505588,
    decodeIntegerRow 32 3 1 1071635901813124,
    decodeIntegerRow 32 3 1 644623276160212,
    decodeIntegerRow 32 3 1 287564349620516,
    decodeIntegerRow 32 3 1 1568846039545956,
    decodeIntegerRow 32 3 1 1193708136413332,
    decodeIntegerRow 32 3 1 1055822113830076,
    decodeIntegerRow 32 3 1 1524597961445132,
    decodeIntegerRow 32 3 1 1524597967453116,
    decodeIntegerRow 32 3 1 1055822086042228,
    decodeIntegerRow 32 3 1 659312022594844,
    decodeIntegerRow 32 3 1 284174161720212,
    decodeIntegerRow 32 3 1 287564336523732,
    decodeIntegerRow 32 3 1 644623305846364,
    decodeIntegerRow 32 3 1 781384259565772,
    decodeIntegerRow 32 3 1 335200020088964,
    decodeIntegerRow 32 3 1 1193668735456324,
    decodeIntegerRow 32 3 1 284356507629452,
    decodeIntegerRow 32 3 1 1524793743942116,
    decodeIntegerRow 32 3 1 797116658418028,
    decodeIntegerRow 32 3 1 1071721850545708,
    decodeIntegerRow 32 3 1 335005276725156,
    decodeIntegerRow 32 3 1 287744616192308,
    decodeIntegerRow 32 3 1 1208352630980476,
    decodeIntegerRow 32 3 1 1208352660658252,
    decodeIntegerRow 32 3 1 287744629287036,
    decodeIntegerRow 32 3 1 1518014918873388,
    decodeIntegerRow 32 3 1 781298365788124,
    decodeIntegerRow 32 3 1 797116630621084,
    decodeIntegerRow 32 3 1 1524793737930348,
    decodeIntegerRow 32 3 1 1568663693634884,
    decodeIntegerRow 32 3 1 659351483230708]

def assocBCA : Matrix (RightIndex 2 5 3) (LeftIndex 2 5 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 5 3 r) []).getD (leftPosition 2 5 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 2 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 2 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 2 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 2 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 2 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 2 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 2 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 2 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 2 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 2 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 2 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 2 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 2 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 2 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 2 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 2 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_0 : (associatorZ 2 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_1 : (associatorZ 2 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_2 : (associatorZ 2 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_3 : (associatorZ 2 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_0 : (associatorZ 2 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_1 : (associatorZ 2 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_2 : (associatorZ 2 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_3 : (associatorZ 2 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_0 : (associatorZ 2 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_1 : (associatorZ 2 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_2 : (associatorZ 2 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_3 : (associatorZ 2 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_0 : (associatorZ 2 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_1 : (associatorZ 2 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_2 : (associatorZ 2 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_3 : (associatorZ 2 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 2 5 3 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_0_2
  · exact assocBCA_row_2_0_3
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_0_2
  · exact assocBCA_row_3_0_3
  · exact assocBCA_row_4_0_0
  · exact assocBCA_row_4_0_1
  · exact assocBCA_row_4_0_2
  · exact assocBCA_row_4_0_3
  · exact assocBCA_row_5_0_0
  · exact assocBCA_row_5_0_1
  · exact assocBCA_row_5_0_2
  · exact assocBCA_row_5_0_3
  · exact assocBCA_row_6_0_0
  · exact assocBCA_row_6_0_1
  · exact assocBCA_row_6_0_2
  · exact assocBCA_row_6_0_3
  · exact assocBCA_row_7_0_0
  · exact assocBCA_row_7_0_1
  · exact assocBCA_row_7_0_2
  · exact assocBCA_row_7_0_3

def innerRightBAC : Matrix (RightIndex 2 5 3) (RightIndex 2 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 2 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 2 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 2 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 2 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 2 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 2 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 2 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 2 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 2 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 2 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 2 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 2 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 2 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 2 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 2 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 2 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_0 : (innerRightZ 2 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_1 : (innerRightZ 2 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_2 : (innerRightZ 2 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_3 : (innerRightZ 2 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_0 : (innerRightZ 2 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_1 : (innerRightZ 2 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_2 : (innerRightZ 2 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_3 : (innerRightZ 2 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_0 : (innerRightZ 2 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_1 : (innerRightZ 2 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_2 : (innerRightZ 2 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_3 : (innerRightZ 2 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_0 : (innerRightZ 2 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_1 : (innerRightZ 2 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_2 : (innerRightZ 2 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_3 : (innerRightZ 2 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 2 3 5 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_0_2
  · exact innerRightBAC_row_0_0_3
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_0_2
  · exact innerRightBAC_row_2_0_3
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_0_2
  · exact innerRightBAC_row_3_0_3
  · exact innerRightBAC_row_4_0_0
  · exact innerRightBAC_row_4_0_1
  · exact innerRightBAC_row_4_0_2
  · exact innerRightBAC_row_4_0_3
  · exact innerRightBAC_row_5_0_0
  · exact innerRightBAC_row_5_0_1
  · exact innerRightBAC_row_5_0_2
  · exact innerRightBAC_row_5_0_3
  · exact innerRightBAC_row_6_0_0
  · exact innerRightBAC_row_6_0_1
  · exact innerRightBAC_row_6_0_2
  · exact innerRightBAC_row_6_0_3
  · exact innerRightBAC_row_7_0_0
  · exact innerRightBAC_row_7_0_1
  · exact innerRightBAC_row_7_0_2
  · exact innerRightBAC_row_7_0_3

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 719771659379482,
    decodeIntegerRow 32 3 1 1544465915483062,
    decodeIntegerRow 32 3 1 941761291049266,
    decodeIntegerRow 32 3 1 860421583597954,
    decodeIntegerRow 32 3 1 926520942199666,
    decodeIntegerRow 32 3 1 926505445380286,
    decodeIntegerRow 32 3 1 926604194558758,
    decodeIntegerRow 32 3 1 926478842508662,
    decodeIntegerRow 32 3 1 926505445379818,
    decodeIntegerRow 32 3 1 926499246652282,
    decodeIntegerRow 32 3 1 926478842504286,
    decodeIntegerRow 32 3 1 926415994294546,
    decodeIntegerRow 32 3 1 308554263842206,
    decodeIntegerRow 32 3 1 719771688064174,
    decodeIntegerRow 32 3 1 992598606671062,
    decodeIntegerRow 32 3 1 941761287742522,
    decodeIntegerRow 32 3 1 896007706021246,
    decodeIntegerRow 32 3 1 855337850878414,
    decodeIntegerRow 32 3 1 721466265296182,
    decodeIntegerRow 32 3 1 309119122875802,
    decodeIntegerRow 32 3 1 926415908201098,
    decodeIntegerRow 32 3 1 926478584223962,
    decodeIntegerRow 32 3 1 926520167358526,
    decodeIntegerRow 32 3 1 926512418949106,
    decodeIntegerRow 32 3 1 926541604623506,
    decodeIntegerRow 32 3 1 926415908199646,
    decodeIntegerRow 32 3 1 926507769903238,
    decodeIntegerRow 32 3 1 926520167358742,
    decodeIntegerRow 32 3 1 855337851587002,
    decodeIntegerRow 32 3 1 957012485901142,
    decodeIntegerRow 32 3 1 309119132481106,
    decodeIntegerRow 32 3 1 1131553952266594]

def assocCAB : Matrix (RightIndex 5 3 2) (LeftIndex 5 3 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 5 3 2 r) []).getD (leftPosition 5 3 2 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = assocCAB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = assocCAB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_0 : (associatorZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_1 : (associatorZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_2 : (associatorZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = assocCAB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_3 : (associatorZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = assocCAB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_2_0 : (associatorZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_2_1 : (associatorZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_2_2 : (associatorZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = assocCAB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_2_3 : (associatorZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = assocCAB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_3_0 : (associatorZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_3_1 : (associatorZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_3_2 : (associatorZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = assocCAB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_3_3 : (associatorZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = assocCAB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = assocCAB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = assocCAB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_0 : (associatorZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_1 : (associatorZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_2 : (associatorZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = assocCAB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_3 : (associatorZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = assocCAB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_2_0 : (associatorZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_2_1 : (associatorZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_2_2 : (associatorZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = assocCAB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_2_3 : (associatorZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = assocCAB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_3_0 : (associatorZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_3_1 : (associatorZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_3_2 : (associatorZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = assocCAB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_3_3 : (associatorZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = assocCAB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 5 3 2 = assocCAB := by
  funext r
  fin_cases r
  · exact assocCAB_row_0_0_0
  · exact assocCAB_row_0_0_1
  · exact assocCAB_row_0_0_2
  · exact assocCAB_row_0_0_3
  · exact assocCAB_row_0_1_0
  · exact assocCAB_row_0_1_1
  · exact assocCAB_row_0_1_2
  · exact assocCAB_row_0_1_3
  · exact assocCAB_row_0_2_0
  · exact assocCAB_row_0_2_1
  · exact assocCAB_row_0_2_2
  · exact assocCAB_row_0_2_3
  · exact assocCAB_row_0_3_0
  · exact assocCAB_row_0_3_1
  · exact assocCAB_row_0_3_2
  · exact assocCAB_row_0_3_3
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_1_1_0
  · exact assocCAB_row_1_1_1
  · exact assocCAB_row_1_1_2
  · exact assocCAB_row_1_1_3
  · exact assocCAB_row_1_2_0
  · exact assocCAB_row_1_2_1
  · exact assocCAB_row_1_2_2
  · exact assocCAB_row_1_2_3
  · exact assocCAB_row_1_3_0
  · exact assocCAB_row_1_3_1
  · exact assocCAB_row_1_3_2
  · exact assocCAB_row_1_3_3

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510079374020,
    decodeIntegerRow 32 3 1 926510088011504,
    decodeIntegerRow 32 3 1 926510091313872,
    decodeIntegerRow 32 3 1 926510080792660,
    decodeIntegerRow 32 3 1 926510080791664,
    decodeIntegerRow 32 3 1 926510091318140,
    decodeIntegerRow 32 3 1 926510100844820,
    decodeIntegerRow 32 3 1 926510109475888,
    decodeIntegerRow 32 3 1 926510097695376,
    decodeIntegerRow 32 3 1 926510080425220,
    decodeIntegerRow 32 3 1 926510079715180,
    decodeIntegerRow 32 3 1 926510100761552,
    decodeIntegerRow 32 3 1 926510088085700,
    decodeIntegerRow 32 3 1 926510109134704,
    decodeIntegerRow 32 3 1 926510080424272,
    decodeIntegerRow 32 3 1 926510097691220,
    decodeIntegerRow 32 3 1 1574445034245820,
    decodeIntegerRow 32 3 1 1202629670355856,
    decodeIntegerRow 32 3 1 1060473556420528,
    decodeIntegerRow 32 3 1 1513377233966380,
    decodeIntegerRow 32 3 1 1513420108500496,
    decodeIntegerRow 32 3 1 1060289833015300,
    decodeIntegerRow 32 3 1 650197496999020,
    decodeIntegerRow 32 3 1 278658320870992,
    decodeIntegerRow 32 3 1 785770734172144,
    decodeIntegerRow 32 3 1 1529194321130620,
    decodeIntegerRow 32 3 1 1559759214909460,
    decodeIntegerRow 32 3 1 653781911363248,
    decodeIntegerRow 32 3 1 1199435775844540,
    decodeIntegerRow 32 3 1 293345173328656,
    decodeIntegerRow 32 3 1 1529235129422128,
    decodeIntegerRow 32 3 1 785949636344620]

def outerLeftABC : Matrix (RightIndex 5 3 2) (LeftIndex 3 2 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 3 2 r) []).getD (leftPosition 3 2 5 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_0 : (outerLeftZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_1 : (outerLeftZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_2 : (outerLeftZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_3 : (outerLeftZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_0 : (outerLeftZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_1 : (outerLeftZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_2 : (outerLeftZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_3 : (outerLeftZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_0 : (outerLeftZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_1 : (outerLeftZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_2 : (outerLeftZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_3 : (outerLeftZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_0 : (outerLeftZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_1 : (outerLeftZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_2 : (outerLeftZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_3 : (outerLeftZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 2 5 = outerLeftABC := by
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
  · exact outerLeftABC_row_0_2_0
  · exact outerLeftABC_row_0_2_1
  · exact outerLeftABC_row_0_2_2
  · exact outerLeftABC_row_0_2_3
  · exact outerLeftABC_row_0_3_0
  · exact outerLeftABC_row_0_3_1
  · exact outerLeftABC_row_0_3_2
  · exact outerLeftABC_row_0_3_3
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_1_2
  · exact outerLeftABC_row_1_1_3
  · exact outerLeftABC_row_1_2_0
  · exact outerLeftABC_row_1_2_1
  · exact outerLeftABC_row_1_2_2
  · exact outerLeftABC_row_1_2_3
  · exact outerLeftABC_row_1_3_0
  · exact outerLeftABC_row_1_3_1
  · exact outerLeftABC_row_1_3_2
  · exact outerLeftABC_row_1_3_3

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325
