import RMod.BrundanEllis.StackingReferenceHexagonAtoms325
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1060403145620864,
    decodeIntegerRow 32 3 1 339529659026200,
    decodeIntegerRow 32 3 1 278520220572400,
    decodeIntegerRow 32 3 1 1202767749183648,
    decodeIntegerRow 32 3 1 1529125277457040,
    decodeIntegerRow 32 3 1 1067139585448608,
    decodeIntegerRow 32 3 1 653725247170944,
    decodeIntegerRow 32 3 1 293401829150440,
    decodeIntegerRow 32 3 1 1202767779290000,
    decodeIntegerRow 32 3 1 278520233407648,
    decodeIntegerRow 32 3 1 1513490536046464,
    decodeIntegerRow 32 3 1 792617070502760,
    decodeIntegerRow 32 3 1 1559618372375296,
    decodeIntegerRow 32 3 1 1199294912265960,
    decodeIntegerRow 32 3 1 1067139613446800,
    decodeIntegerRow 32 3 1 1529125270923232,
    decodeIntegerRow 32 3 1 1559815870733200,
    decodeIntegerRow 32 3 1 1199379111647648,
    decodeIntegerRow 32 3 1 1067180421742464,
    decodeIntegerRow 32 3 1 1529304173094760,
    decodeIntegerRow 32 3 1 650335575831296,
    decodeIntegerRow 32 3 1 1574306933949160,
    decodeIntegerRow 32 3 1 339713376211600,
    decodeIntegerRow 32 3 1 1060360243819232,
    decodeIntegerRow 32 3 1 1529304179630464,
    decodeIntegerRow 32 3 1 1067180393735960,
    decodeIntegerRow 32 3 1 653641047780080,
    decodeIntegerRow 32 3 1 293204330796448,
    decodeIntegerRow 32 3 1 792659917769360,
    decodeIntegerRow 32 3 1 1513306806421408,
    decodeIntegerRow 32 3 1 1574306946780544,
    decodeIntegerRow 32 3 1 650335605928680]

def assocABC : Matrix (RightIndex 3 5 2) (LeftIndex 3 5 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 5 2 r) []).getD (leftPosition 3 5 2 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_0 : (associatorZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_1 : (associatorZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_2 : (associatorZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_3 : (associatorZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_0 : (associatorZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_1 : (associatorZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_2 : (associatorZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_3 : (associatorZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 5 2 = assocABC := by
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

def outerABC : Matrix (LeftIndex 5 2 3) (RightIndex 3 5 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 5 2 3 r) []).getD (rightPosition 3 5 2 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 5 2 = outerABC := by
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

def assocBAC : Matrix (RightIndex 5 3 2) (LeftIndex 5 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocCAB

theorem assocBAC_eq : associatorZ 5 3 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocCAB_eq

def innerABC : Matrix (LeftIndex 5 3 2) (LeftIndex 3 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.innerACB

theorem innerABC_eq : innerLeftZ 3 5 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 2 5) (RightIndex 3 5 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 3 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_2 : (innerRightZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_3 : (innerRightZ 3 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 3 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_2 : (innerRightZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_3 : (innerRightZ 3 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 5 2 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 720629422684474,
    decodeIntegerRow 32 3 1 1544180003925466,
    decodeIntegerRow 32 3 1 949481030059708,
    decodeIntegerRow 32 3 1 857848336001428,
    decodeIntegerRow 32 3 1 918884539987654,
    decodeIntegerRow 32 3 1 923968357737754,
    decodeIntegerRow 32 3 1 927357770455852,
    decodeIntegerRow 32 3 1 926793686223868,
    decodeIntegerRow 32 3 1 926510092832326,
    decodeIntegerRow 32 3 1 926510094955174,
    decodeIntegerRow 32 3 1 926510080076932,
    decodeIntegerRow 32 3 1 926510099209132,
    decodeIntegerRow 32 3 1 926510094432454,
    decodeIntegerRow 32 3 1 926510094445594,
    decodeIntegerRow 32 3 1 926510094484972,
    decodeIntegerRow 32 3 1 926510094603068,
    decodeIntegerRow 32 3 1 949292743702054,
    decodeIntegerRow 32 3 1 995109090731194,
    decodeIntegerRow 32 3 1 1132411686873772,
    decodeIntegerRow 32 3 1 1544186977494268,
    decodeIntegerRow 32 3 1 927356995614874,
    decodeIntegerRow 32 3 1 926228827150906,
    decodeIntegerRow 32 3 1 934135734957628,
    decodeIntegerRow 32 3 1 923968099457428,
    decodeIntegerRow 32 3 1 926510080077094,
    decodeIntegerRow 32 3 1 926510089643194,
    decodeIntegerRow 32 3 1 926510096020972,
    decodeIntegerRow 32 3 1 926510094959548,
    decodeIntegerRow 32 3 1 926510094484966,
    decodeIntegerRow 32 3 1 926510094248774,
    decodeIntegerRow 32 3 1 926510094419332,
    decodeIntegerRow 32 3 1 926510094445612]

def inverseACB : Matrix (LeftIndex 3 2 5) (RightIndex 3 2 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 2 5 r) []).getD (rightPosition 3 2 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = inverseACB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = inverseACB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = inverseACB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = inverseACB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_0 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_1 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_2 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = inverseACB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_3 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = inverseACB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_0 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_1 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_2 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = inverseACB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_3 : (associatorInverseZ 3 2 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = inverseACB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = inverseACB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = inverseACB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = inverseACB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = inverseACB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_0 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_1 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_2 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = inverseACB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_3 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = inverseACB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_0 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_1 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_2 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = inverseACB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_3 : (associatorInverseZ 3 2 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = inverseACB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 2 5 = inverseACB := by
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
  · exact inverseACB_row_0_2_0
  · exact inverseACB_row_0_2_1
  · exact inverseACB_row_0_2_2
  · exact inverseACB_row_0_2_3
  · exact inverseACB_row_0_3_0
  · exact inverseACB_row_0_3_1
  · exact inverseACB_row_0_3_2
  · exact inverseACB_row_0_3_3
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_1_2
  · exact inverseACB_row_1_1_3
  · exact inverseACB_row_1_2_0
  · exact inverseACB_row_1_2_1
  · exact inverseACB_row_1_2_2
  · exact inverseACB_row_1_2_3
  · exact inverseACB_row_1_3_0
  · exact inverseACB_row_1_3_1
  · exact inverseACB_row_1_3_2
  · exact inverseACB_row_1_3_3

def innerACB : Matrix (LeftIndex 2 3 5) (LeftIndex 3 2 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.innerABC

theorem innerACB_eq : innerLeftZ 3 2 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 333505187778884,
    decodeIntegerRow 32 3 1 781949203669132,
    decodeIntegerRow 32 3 1 1193143392214756,
    decodeIntegerRow 32 3 1 1570540349258348,
    decodeIntegerRow 32 3 1 282479833555484,
    decodeIntegerRow 32 3 1 659876824355308,
    decodeIntegerRow 32 3 1 781949233268164,
    decodeIntegerRow 32 3 1 333505174657908,
    decodeIntegerRow 32 3 1 1208961684608428,
    decodeIntegerRow 32 3 1 289258665370916,
    decodeIntegerRow 32 3 1 1522903122756788,
    decodeIntegerRow 32 3 1 796633128792316,
    decodeIntegerRow 32 3 1 796633158706252,
    decodeIntegerRow 32 3 1 1522903135143036,
    decodeIntegerRow 32 3 1 1563761530201388,
    decodeIntegerRow 32 3 1 644058531804124,
    decodeIntegerRow 32 3 1 796551856578844,
    decodeIntegerRow 32 3 1 1523099415803628,
    decodeIntegerRow 32 3 1 1563580727254724,
    decodeIntegerRow 32 3 1 644102584090228,
    decodeIntegerRow 32 3 1 1208917577209924,
    decodeIntegerRow 32 3 1 289439454880652,
    decodeIntegerRow 32 3 1 1523099428191716,
    decodeIntegerRow 32 3 1 796551886501228,
    decodeIntegerRow 32 3 1 1570358519910732,
    decodeIntegerRow 32 3 1 1193103789226876,
    decodeIntegerRow 32 3 1 1071157078628908,
    decodeIntegerRow 32 3 1 1519709227877084,
    decodeIntegerRow 32 3 1 1519709241000108,
    decodeIntegerRow 32 3 1 1071157049021476,
    decodeIntegerRow 32 3 1 659916427334068,
    decodeIntegerRow 32 3 1 282661662906876]

def assocBCA : Matrix (RightIndex 5 2 3) (LeftIndex 5 2 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 2 3 r) []).getD (leftPosition 5 2 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = assocBCA ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 5 2 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = assocBCA ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_0 : (associatorZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_1 : (associatorZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_2 : (associatorZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = assocBCA ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_3 : (associatorZ 5 2 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = assocBCA ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_2_0 : (associatorZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_2_1 : (associatorZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_2_2 : (associatorZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = assocBCA ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_2_3 : (associatorZ 5 2 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = assocBCA ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_3_0 : (associatorZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_3_1 : (associatorZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_3_2 : (associatorZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = assocBCA ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_3_3 : (associatorZ 5 2 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = assocBCA ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = assocBCA ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 5 2 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = assocBCA ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_0 : (associatorZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_1 : (associatorZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_2 : (associatorZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = assocBCA ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_3 : (associatorZ 5 2 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = assocBCA ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_2_0 : (associatorZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_2_1 : (associatorZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_2_2 : (associatorZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = assocBCA ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_2_3 : (associatorZ 5 2 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = assocBCA ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_3_0 : (associatorZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_3_1 : (associatorZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_3_2 : (associatorZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = assocBCA ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_3_3 : (associatorZ 5 2 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = assocBCA ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 5 2 3 = assocBCA := by
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
  · exact assocBCA_row_0_2_0
  · exact assocBCA_row_0_2_1
  · exact assocBCA_row_0_2_2
  · exact assocBCA_row_0_2_3
  · exact assocBCA_row_0_3_0
  · exact assocBCA_row_0_3_1
  · exact assocBCA_row_0_3_2
  · exact assocBCA_row_0_3_3
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_1_0
  · exact assocBCA_row_1_1_1
  · exact assocBCA_row_1_1_2
  · exact assocBCA_row_1_1_3
  · exact assocBCA_row_1_2_0
  · exact assocBCA_row_1_2_1
  · exact assocBCA_row_1_2_2
  · exact assocBCA_row_1_2_3
  · exact assocBCA_row_1_3_0
  · exact assocBCA_row_1_3_1
  · exact assocBCA_row_1_3_2
  · exact assocBCA_row_1_3_3

def innerRightBAC : Matrix (RightIndex 5 2 3) (RightIndex 5 3 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 4) (Fin 2 × Fin 4 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerRightBAC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerRightBAC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerRightBAC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerRightBAC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_0 : (innerRightZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerRightBAC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_1 : (innerRightZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerRightBAC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_2 : (innerRightZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerRightBAC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_3 : (innerRightZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerRightBAC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_2_0 : (innerRightZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerRightBAC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_2_1 : (innerRightZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerRightBAC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_2_2 : (innerRightZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerRightBAC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_2_3 : (innerRightZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerRightBAC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_3_0 : (innerRightZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerRightBAC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_3_1 : (innerRightZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerRightBAC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_3_2 : (innerRightZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerRightBAC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_3_3 : (innerRightZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerRightBAC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerRightBAC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerRightBAC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerRightBAC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerRightBAC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_0 : (innerRightZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerRightBAC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_1 : (innerRightZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerRightBAC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_2 : (innerRightZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerRightBAC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_3 : (innerRightZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerRightBAC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_2_0 : (innerRightZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerRightBAC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_2_1 : (innerRightZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerRightBAC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_2_2 : (innerRightZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerRightBAC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_2_3 : (innerRightZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerRightBAC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_3_0 : (innerRightZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerRightBAC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_3_1 : (innerRightZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerRightBAC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_3_2 : (innerRightZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerRightBAC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_3_3 : (innerRightZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerRightBAC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 5 3 2 = innerRightBAC := by
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
  · exact innerRightBAC_row_0_2_0
  · exact innerRightBAC_row_0_2_1
  · exact innerRightBAC_row_0_2_2
  · exact innerRightBAC_row_0_2_3
  · exact innerRightBAC_row_0_3_0
  · exact innerRightBAC_row_0_3_1
  · exact innerRightBAC_row_0_3_2
  · exact innerRightBAC_row_0_3_3
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_1_1_0
  · exact innerRightBAC_row_1_1_1
  · exact innerRightBAC_row_1_1_2
  · exact innerRightBAC_row_1_1_3
  · exact innerRightBAC_row_1_2_0
  · exact innerRightBAC_row_1_2_1
  · exact innerRightBAC_row_1_2_2
  · exact innerRightBAC_row_1_2_3
  · exact innerRightBAC_row_1_3_0
  · exact innerRightBAC_row_1_3_1
  · exact innerRightBAC_row_1_3_2
  · exact innerRightBAC_row_1_3_3

def assocCAB : Matrix (RightIndex 2 3 5) (LeftIndex 2 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocBAC

theorem assocCAB_eq : associatorZ 2 3 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 2 3 5) (LeftIndex 3 5 2) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 5 2) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 5 2) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 5 2) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 5 2) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_0 : (outerLeftZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_1 : (outerLeftZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_2 : (outerLeftZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_3 : (outerLeftZ 3 5 2) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_0 : (outerLeftZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_1 : (outerLeftZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_2 : (outerLeftZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_3 : (outerLeftZ 3 5 2) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_0 : (outerLeftZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_1 : (outerLeftZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_2 : (outerLeftZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_3 : (outerLeftZ 3 5 2) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_0 : (outerLeftZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_1 : (outerLeftZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_2 : (outerLeftZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_3 : (outerLeftZ 3 5 2) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 5 2 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_4_0_0
  · exact outerLeftABC_row_4_0_1
  · exact outerLeftABC_row_4_0_2
  · exact outerLeftABC_row_4_0_3
  · exact outerLeftABC_row_5_0_0
  · exact outerLeftABC_row_5_0_1
  · exact outerLeftABC_row_5_0_2
  · exact outerLeftABC_row_5_0_3
  · exact outerLeftABC_row_6_0_0
  · exact outerLeftABC_row_6_0_1
  · exact outerLeftABC_row_6_0_2
  · exact outerLeftABC_row_6_0_3
  · exact outerLeftABC_row_7_0_0
  · exact outerLeftABC_row_7_0_1
  · exact outerLeftABC_row_7_0_2
  · exact outerLeftABC_row_7_0_3

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352
