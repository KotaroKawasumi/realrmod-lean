import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1795904917194320,
    decodeIntegerRow 32 3 1 423353158132128,
    decodeIntegerRow 32 3 1 1246903739320704,
    decodeIntegerRow 32 3 1 148747966188200,
    decodeIntegerRow 32 3 1 916908113036200,
    decodeIntegerRow 32 3 1 930465559836544,
    decodeIntegerRow 32 3 1 932721915896032,
    decodeIntegerRow 32 3 1 915776806943920,
    decodeIntegerRow 32 3 1 1429667030535936,
    decodeIntegerRow 32 3 1 1795904916748200,
    decodeIntegerRow 32 3 1 1704272223162320,
    decodeIntegerRow 32 3 1 1246903739609312,
    decodeIntegerRow 32 3 1 930465583213792,
    decodeIntegerRow 32 3 1 936112116208720,
    decodeIntegerRow 32 3 1 915776843079640,
    decodeIntegerRow 32 3 1 920298287841664,
    decodeIntegerRow 32 3 1 916906907724448,
    decodeIntegerRow 32 3 1 930462632653360,
    decodeIntegerRow 32 3 1 932725187441320,
    decodeIntegerRow 32 3 1 915778700997376,
    decodeIntegerRow 32 3 1 1795751498680704,
    decodeIntegerRow 32 3 1 423088162517720,
    decodeIntegerRow 32 3 1 1246666637981360,
    decodeIntegerRow 32 3 1 148650336224928,
    decodeIntegerRow 32 3 1 930462656042920,
    decodeIntegerRow 32 3 1 936113321513344,
    decodeIntegerRow 32 3 1 915778737137632,
    decodeIntegerRow 32 3 1 920295016285360,
    decodeIntegerRow 32 3 1 1429932026150480,
    decodeIntegerRow 32 3 1 1795751498234528,
    decodeIntegerRow 32 3 1 1704369853125504,
    decodeIntegerRow 32 3 1 1246666638270120]

def assocABC : Matrix (RightIndex 3 4 5) (LeftIndex 3 4 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 4 5 r) []).getD (leftPosition 3 4 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_0 : (associatorZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_1 : (associatorZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_2 : (associatorZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_3 : (associatorZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_0 : (associatorZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_1 : (associatorZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_2 : (associatorZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_3 : (associatorZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 4 5 = assocABC := by
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

def outerABC : Matrix (LeftIndex 4 5 3) (RightIndex 3 4 5) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 4 5 3 r) []).getD (rightPosition 3 4 5 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 4 5 = outerABC := by
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

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 931593910053172,
    decodeIntegerRow 32 3 1 936677384488012,
    decodeIntegerRow 32 3 1 925945991061736,
    decodeIntegerRow 32 3 1 925378817032264,
    decodeIntegerRow 32 3 1 916342459987144,
    decodeIntegerRow 32 3 1 931593737860456,
    decodeIntegerRow 32 3 1 927638272455988,
    decodeIntegerRow 32 3 1 925944441380428,
    decodeIntegerRow 32 3 1 927638253323788,
    decodeIntegerRow 32 3 1 927075709208308,
    decodeIntegerRow 32 3 1 936677730987544,
    decodeIntegerRow 32 3 1 931593742117816,
    decodeIntegerRow 32 3 1 927074159525704,
    decodeIntegerRow 32 3 1 925378836163816,
    decodeIntegerRow 32 3 1 931593914298868,
    decodeIntegerRow 32 3 1 916342802235148,
    decodeIntegerRow 32 3 1 1338299332210228,
    decodeIntegerRow 32 3 1 1750060675680052,
    decodeIntegerRow 32 3 1 880819271871416,
    decodeIntegerRow 32 3 1 834877400485736,
    decodeIntegerRow 32 3 1 1750088569955224,
    decodeIntegerRow 32 3 1 514734803779144,
    decodeIntegerRow 32 3 1 835128448962612,
    decodeIntegerRow 32 3 1 972326441218868,
    decodeIntegerRow 32 3 1 835128448726412,
    decodeIntegerRow 32 3 1 880693747160588,
    decodeIntegerRow 32 3 1 102931618922824,
    decodeIntegerRow 32 3 1 514734803831704,
    decodeIntegerRow 32 3 1 972200917452824,
    decodeIntegerRow 32 3 1 834877400249544,
    decodeIntegerRow 32 3 1 1338299332157812,
    decodeIntegerRow 32 3 1 102959513198068]

def assocBAC : Matrix (RightIndex 4 3 5) (LeftIndex 4 3 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 4 3 5 r) []).getD (leftPosition 4 3 5 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 4 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 4 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 4 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 4 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 4 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 4 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 4 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 4 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 4 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 4 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 4 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 4 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 4 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 4 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 4 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 4 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_0 : (associatorZ 4 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_1 : (associatorZ 4 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_2 : (associatorZ 4 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_3 : (associatorZ 4 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_0 : (associatorZ 4 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_1 : (associatorZ 4 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_2 : (associatorZ 4 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_3 : (associatorZ 4 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_0 : (associatorZ 4 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_1 : (associatorZ 4 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_2 : (associatorZ 4 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_3 : (associatorZ 4 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_0 : (associatorZ 4 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_1 : (associatorZ 4 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_2 : (associatorZ 4 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_3 : (associatorZ 4 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 4 3 5 = assocBAC := by
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

def innerABC : Matrix (LeftIndex 4 3 5) (LeftIndex 3 4 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_0 : (innerLeftZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_1 : (innerLeftZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_2 : (innerLeftZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_3 : (innerLeftZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_0 : (innerLeftZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_1 : (innerLeftZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_2 : (innerLeftZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_3 : (innerLeftZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 4 5 = innerABC := by
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

def innerRightABC : Matrix (RightIndex 3 5 4) (RightIndex 3 4 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_2 : (innerRightZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_3 : (innerRightZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_2 : (innerRightZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_3 : (innerRightZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 4 5 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 933852731995336,
    decodeIntegerRow 32 3 1 928205873766616,
    decodeIntegerRow 32 3 1 923119827148588,
    decodeIntegerRow 32 3 1 918602340565612,
    decodeIntegerRow 32 3 1 928203463145704,
    decodeIntegerRow 32 3 1 919166423733256,
    decodeIntegerRow 32 3 1 918601824003988,
    decodeIntegerRow 32 3 1 929898123269548,
    decodeIntegerRow 32 3 1 934418394607576,
    decodeIntegerRow 32 3 1 929898136028344,
    decodeIntegerRow 32 3 1 928203469527532,
    decodeIntegerRow 32 3 1 933853792751572,
    decodeIntegerRow 32 3 1 929900374453624,
    decodeIntegerRow 32 3 1 918602310803944,
    decodeIntegerRow 32 3 1 933852759632212,
    decodeIntegerRow 32 3 1 924814308712468,
    decodeIntegerRow 32 3 1 285938984796904,
    decodeIntegerRow 32 3 1 652079241282056,
    decodeIntegerRow 32 3 1 789346969619988,
    decodeIntegerRow 32 3 1 331671649013548,
    decodeIntegerRow 32 3 1 651897928493256,
    decodeIntegerRow 32 3 1 1567039362642136,
    decodeIntegerRow 32 3 1 331755331839148,
    decodeIntegerRow 32 3 1 1063868479158252,
    decodeIntegerRow 32 3 1 1521264856671496,
    decodeIntegerRow 32 3 1 1063868479079576,
    decodeIntegerRow 32 3 1 651897928650668,
    decodeIntegerRow 32 3 1 285980826577132,
    decodeIntegerRow 32 3 1 1063673219153064,
    decodeIntegerRow 32 3 1 331671649354696,
    decodeIntegerRow 32 3 1 285938985164308,
    decodeIntegerRow 32 3 1 1200940947412268]

def inverseACB : Matrix (LeftIndex 3 5 4) (RightIndex 3 5 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 5 4 r) []).getD (rightPosition 3 5 4 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 5 4) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 5 4) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 5 4) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 5 4) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 5 4) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 5 4) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 5 4) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 5 4) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 5 4) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 5 4) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 5 4) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 5 4) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 5 4) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 5 4) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 5 4) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 5 4) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 3 5 4) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 3 5 4) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 3 5 4) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 3 5 4) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 3 5 4) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 3 5 4) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 3 5 4) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 3 5 4) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 3 5 4) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 3 5 4) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 3 5 4) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 3 5 4) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 3 5 4) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 3 5 4) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 3 5 4) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 3 5 4) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 5 4 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 5 3 4) (LeftIndex 3 5 4) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 5 4) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 5 4) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 3 5 4) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 3 5 4) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 5 4) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 5 4) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 3 5 4) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 3 5 4) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 3 5 4) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 3 5 4) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 3 5 4) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 3 5 4) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 3 5 4) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 3 5 4) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 3 5 4) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 3 5 4) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_0 : (innerLeftZ 3 5 4) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_1 : (innerLeftZ 3 5 4) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_2 : (innerLeftZ 3 5 4) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_3 : (innerLeftZ 3 5 4) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_0 : (innerLeftZ 3 5 4) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_1 : (innerLeftZ 3 5 4) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_2 : (innerLeftZ 3 5 4) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_3 : (innerLeftZ 3 5 4) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_0 : (innerLeftZ 3 5 4) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_1 : (innerLeftZ 3 5 4) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_2 : (innerLeftZ 3 5 4) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_3 : (innerLeftZ 3 5 4) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_0 : (innerLeftZ 3 5 4) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_1 : (innerLeftZ 3 5 4) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_2 : (innerLeftZ 3 5 4) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_3 : (innerLeftZ 3 5 4) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 5 4 = innerACB := by
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

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 933852759632212,
    decodeIntegerRow 32 3 1 928205880139372,
    decodeIntegerRow 32 3 1 923119814398216,
    decodeIntegerRow 32 3 1 918602310803944,
    decodeIntegerRow 32 3 1 928203469527532,
    decodeIntegerRow 32 3 1 919166396100268,
    decodeIntegerRow 32 3 1 918601794244264,
    decodeIntegerRow 32 3 1 929898136028344,
    decodeIntegerRow 32 3 1 934418364847852,
    decodeIntegerRow 32 3 1 929898123269548,
    decodeIntegerRow 32 3 1 928203463145704,
    decodeIntegerRow 32 3 1 933853765118584,
    decodeIntegerRow 32 3 1 929900361703252,
    decodeIntegerRow 32 3 1 918602340565612,
    decodeIntegerRow 32 3 1 933852731995336,
    decodeIntegerRow 32 3 1 924814315085224,
    decodeIntegerRow 32 3 1 285938985164308,
    decodeIntegerRow 32 3 1 652079241439572,
    decodeIntegerRow 32 3 1 789346969698776,
    decodeIntegerRow 32 3 1 331671649354696,
    decodeIntegerRow 32 3 1 651897928650668,
    decodeIntegerRow 32 3 1 1567039362274708,
    decodeIntegerRow 32 3 1 331755332180344,
    decodeIntegerRow 32 3 1 1063868479079576,
    decodeIntegerRow 32 3 1 1521264857012692,
    decodeIntegerRow 32 3 1 1063868479158252,
    decodeIntegerRow 32 3 1 651897928493256,
    decodeIntegerRow 32 3 1 285980826209704,
    decodeIntegerRow 32 3 1 1063673219231852,
    decodeIntegerRow 32 3 1 331671649013548,
    decodeIntegerRow 32 3 1 285938984796904,
    decodeIntegerRow 32 3 1 1200940947569784]

def assocBCA : Matrix (RightIndex 4 5 3) (LeftIndex 4 5 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 4 5 3 r) []).getD (leftPosition 4 5 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_0 : (associatorZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_1 : (associatorZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_2 : (associatorZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_3 : (associatorZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_0 : (associatorZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_1 : (associatorZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_2 : (associatorZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_3 : (associatorZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_0 : (associatorZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_1 : (associatorZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_2 : (associatorZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_3 : (associatorZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_0 : (associatorZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_1 : (associatorZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_2 : (associatorZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_3 : (associatorZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 4 5 3 = assocBCA := by
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

def innerRightBAC : Matrix (RightIndex 4 5 3) (RightIndex 4 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 4 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 4 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 4 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 4 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 4 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 4 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 4 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 4 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 4 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 4 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 4 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 4 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 4 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 4 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 4 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 4 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_0 : (innerRightZ 4 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_1 : (innerRightZ 4 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_2 : (innerRightZ 4 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_3 : (innerRightZ 4 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_0 : (innerRightZ 4 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_1 : (innerRightZ 4 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_2 : (innerRightZ 4 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_3 : (innerRightZ 4 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_0 : (innerRightZ 4 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_1 : (innerRightZ 4 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_2 : (innerRightZ 4 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_3 : (innerRightZ 4 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_0 : (innerRightZ 4 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_1 : (innerRightZ 4 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_2 : (innerRightZ 4 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_3 : (innerRightZ 4 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 4 3 5 = innerRightBAC := by
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

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 881950539463096,
    decodeIntegerRow 32 3 1 1018706872716184,
    decodeIntegerRow 32 3 1 524888147794252,
    decodeIntegerRow 32 3 1 1755144493417012,
    decodeIntegerRow 32 3 1 926510095516468,
    decodeIntegerRow 32 3 1 926510092316212,
    decodeIntegerRow 32 3 1 926510104227896,
    decodeIntegerRow 32 3 1 926510075411816,
    decodeIntegerRow 32 3 1 108015264472936,
    decodeIntegerRow 32 3 1 1348453020546616,
    decodeIntegerRow 32 3 1 1017326106093388,
    decodeIntegerRow 32 3 1 879565578932812,
    decodeIntegerRow 32 3 1 926510113675572,
    decodeIntegerRow 32 3 1 926510085096012,
    decodeIntegerRow 32 3 1 926510092284136,
    decodeIntegerRow 32 3 1 926510095461064,
    decodeIntegerRow 32 3 1 926510084623628,
    decodeIntegerRow 32 3 1 926510075412468,
    decodeIntegerRow 32 3 1 926510095513624,
    decodeIntegerRow 32 3 1 926510096541496,
    decodeIntegerRow 32 3 1 524902439305624,
    decodeIntegerRow 32 3 1 97847973346504,
    decodeIntegerRow 32 3 1 971198272991092,
    decodeIntegerRow 32 3 1 1018457373921268,
    decodeIntegerRow 32 3 1 926510096561908,
    decodeIntegerRow 32 3 1 926510095464052,
    decodeIntegerRow 32 3 1 926510113676216,
    decodeIntegerRow 32 3 1 926510103755496,
    decodeIntegerRow 32 3 1 1017578704252216,
    decodeIntegerRow 32 3 1 973332185044504,
    decodeIntegerRow 32 3 1 1744976857916812,
    decodeIntegerRow 32 3 1 1348466623310452]

def assocCAB : Matrix (RightIndex 5 3 4) (LeftIndex 5 3 4) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 5 3 4 r) []).getD (leftPosition 5 3 4 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 5 3 4) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 5 3 4) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 5 3 4) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 5 3 4) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_0 : (associatorZ 5 3 4) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_1 : (associatorZ 5 3 4) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_2 : (associatorZ 5 3 4) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_3 : (associatorZ 5 3 4) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 5 3 4) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 5 3 4) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 5 3 4) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 5 3 4) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_0 : (associatorZ 5 3 4) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_1 : (associatorZ 5 3 4) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_2 : (associatorZ 5 3 4) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_3 : (associatorZ 5 3 4) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_0 : (associatorZ 5 3 4) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_1 : (associatorZ 5 3 4) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_2 : (associatorZ 5 3 4) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_3 : (associatorZ 5 3 4) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_0 : (associatorZ 5 3 4) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_1 : (associatorZ 5 3 4) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_2 : (associatorZ 5 3 4) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_3 : (associatorZ 5 3 4) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_0 : (associatorZ 5 3 4) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_1 : (associatorZ 5 3 4) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_2 : (associatorZ 5 3 4) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_3 : (associatorZ 5 3 4) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_0 : (associatorZ 5 3 4) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_1 : (associatorZ 5 3 4) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_2 : (associatorZ 5 3 4) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_3 : (associatorZ 5 3 4) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 5 3 4 = assocCAB := by
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
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_1_1_0
  · exact assocCAB_row_1_1_1
  · exact assocCAB_row_1_1_2
  · exact assocCAB_row_1_1_3
  · exact assocCAB_row_2_0_0
  · exact assocCAB_row_2_0_1
  · exact assocCAB_row_2_0_2
  · exact assocCAB_row_2_0_3
  · exact assocCAB_row_2_1_0
  · exact assocCAB_row_2_1_1
  · exact assocCAB_row_2_1_2
  · exact assocCAB_row_2_1_3
  · exact assocCAB_row_3_0_0
  · exact assocCAB_row_3_0_1
  · exact assocCAB_row_3_0_2
  · exact assocCAB_row_3_0_3
  · exact assocCAB_row_3_1_0
  · exact assocCAB_row_3_1_1
  · exact assocCAB_row_3_1_2
  · exact assocCAB_row_3_1_3

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

def outerLeftABC : Matrix (RightIndex 5 3 4) (LeftIndex 3 4 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 3 4 r) []).getD (leftPosition 3 4 5 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 4 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 3 4 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 4 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 3 4 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 4 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 3 4 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 4 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 3 4 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 4 5 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345
