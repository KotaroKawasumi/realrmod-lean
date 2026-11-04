import RMod.BrundanEllis.StackingReferenceHexagonAtoms356
import RMod.BrundanEllis.StackingReferenceHexagonAtoms365
import RMod.BrundanEllis.StackingReferenceHexagonAtoms563
import RMod.BrundanEllis.StackingReferenceHexagonAtoms635
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms653
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 5 3) (LeftIndex 6 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.assocBCA

theorem assocABC_eq : associatorZ 6 5 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.assocBCA_eq

def outerABC : Matrix (LeftIndex 5 3 6) (RightIndex 6 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_0 : (outerRightZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_1 : (outerRightZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_2 : (outerRightZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_3 : (outerRightZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_0 : (outerRightZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_1 : (outerRightZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_2 : (outerRightZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_3 : (outerRightZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_0 : (outerRightZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_1 : (outerRightZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_2 : (outerRightZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_3 : (outerRightZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_0 : (outerRightZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_1 : (outerRightZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_2 : (outerRightZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_3 : (outerRightZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 6 5 3 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_4_0_0
  · exact outerABC_row_4_0_1
  · exact outerABC_row_4_0_2
  · exact outerABC_row_4_0_3
  · exact outerABC_row_5_0_0
  · exact outerABC_row_5_0_1
  · exact outerABC_row_5_0_2
  · exact outerABC_row_5_0_3
  · exact outerABC_row_6_0_0
  · exact outerABC_row_6_0_1
  · exact outerABC_row_6_0_2
  · exact outerABC_row_6_0_3
  · exact outerABC_row_7_0_0
  · exact outerABC_row_7_0_1
  · exact outerABC_row_7_0_2
  · exact outerABC_row_7_0_3

def assocBAC : Matrix (RightIndex 5 6 3) (LeftIndex 5 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBCA

theorem assocBAC_eq : associatorZ 5 6 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBCA_eq

def innerABC : Matrix (LeftIndex 5 6 3) (LeftIndex 6 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms635.innerACB

theorem innerABC_eq : innerLeftZ 6 5 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms635.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 3 5) (RightIndex 6 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms563.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 5 3 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms563.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 785881637237444,
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

def inverseACB : Matrix (LeftIndex 6 3 5) (RightIndex 6 3 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 3 5 r) []).getD (rightPosition 6 3 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_2 : (associatorInverseZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_3 : (associatorInverseZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_2 : (associatorInverseZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_3 : (associatorInverseZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 6 3 5 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 3 6 5) (LeftIndex 6 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms635.innerABC

theorem innerACB_eq : innerLeftZ 6 3 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms635.innerABC_eq

def assocBCA : Matrix (RightIndex 5 3 6) (LeftIndex 5 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBAC

theorem assocBCA_eq : associatorZ 5 3 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 5 3 6) (RightIndex 5 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms563.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 6 3 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms563.innerRightABC_eq

def assocCAB : Matrix (RightIndex 3 6 5) (LeftIndex 3 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.assocABC

theorem assocCAB_eq : associatorZ 3 6 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510080778548,
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

def outerLeftABC : Matrix (RightIndex 3 6 5) (LeftIndex 6 5 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 6 5 r) []).getD (leftPosition 6 5 3 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_0 : (outerLeftZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_1 : (outerLeftZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_2 : (outerLeftZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_3 : (outerLeftZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_0 : (outerLeftZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_1 : (outerLeftZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_2 : (outerLeftZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_3 : (outerLeftZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_0 : (outerLeftZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_1 : (outerLeftZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_2 : (outerLeftZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_3 : (outerLeftZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_0 : (outerLeftZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_1 : (outerLeftZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_2 : (outerLeftZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_3 : (outerLeftZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 6 5 3 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms653
