import RMod.BrundanEllis.StackingReferenceHexagonAtoms346
import RMod.BrundanEllis.StackingReferenceHexagonAtoms364
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms634
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 3 4) (LeftIndex 6 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocCAB

theorem assocABC_eq : associatorZ 6 3 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocCAB_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094426434,
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

def outerABC : Matrix (LeftIndex 3 4 6) (RightIndex 6 3 4) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 3 4 6 r) []).getD (rightPosition 6 3 4 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 6 3 4 = outerABC := by
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
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_0_4
  · exact outerABC_row_1_0_5
  · exact outerABC_row_1_0_6
  · exact outerABC_row_1_0_7
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_0_4
  · exact outerABC_row_2_0_5
  · exact outerABC_row_2_0_6
  · exact outerABC_row_2_0_7
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_0_4
  · exact outerABC_row_3_0_5
  · exact outerABC_row_3_0_6
  · exact outerABC_row_3_0_7

def assocBAC : Matrix (RightIndex 3 6 4) (LeftIndex 3 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.assocABC

theorem assocBAC_eq : associatorZ 3 6 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.assocABC_eq

def innerABC : Matrix (LeftIndex 3 6 4) (LeftIndex 6 3 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_4 : (innerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_5 : (innerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_6 : (innerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_7 : (innerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_4 : (innerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_5 : (innerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_6 : (innerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_7 : (innerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 6 3 4 = innerABC := by
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

def innerRightABC : Matrix (RightIndex 6 4 3) (RightIndex 6 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 3 4 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 918884497472374,
    decodeIntegerRow 32 3 1 929051958659926,
    decodeIntegerRow 32 3 1 925662801033508,
    decodeIntegerRow 32 3 1 926792538311308,
    decodeIntegerRow 32 3 1 308836698148534,
    decodeIntegerRow 32 3 1 1132401226500886,
    decodeIntegerRow 32 3 1 857879717001988,
    decodeIntegerRow 32 3 1 949386887058028,
    decodeIntegerRow 32 3 1 926513581210294,
    decodeIntegerRow 32 3 1 926499634072726,
    decodeIntegerRow 32 3 1 926478713366308,
    decodeIntegerRow 32 3 1 926604237604748,
    decodeIntegerRow 32 3 1 926510137470454,
    decodeIntegerRow 32 3 1 926509965286486,
    decodeIntegerRow 32 3 1 926509707005188,
    decodeIntegerRow 32 3 1 926511256687468,
    decodeIntegerRow 32 3 1 925662810599446,
    decodeIntegerRow 32 3 1 926227679238346,
    decodeIntegerRow 32 3 1 918884496409492,
    decodeIntegerRow 32 3 1 923968227003268,
    decodeIntegerRow 32 3 1 857879717120086,
    decodeIntegerRow 32 3 1 903633302148106,
    decodeIntegerRow 32 3 1 308836698135412,
    decodeIntegerRow 32 3 1 720618962311588,
    decodeIntegerRow 32 3 1 926478713366314,
    decodeIntegerRow 32 3 1 926415951247094,
    decodeIntegerRow 32 3 1 926513581210348,
    decodeIntegerRow 32 3 1 926520554779132,
    decodeIntegerRow 32 3 1 926509707005674,
    decodeIntegerRow 32 3 1 926508932164534,
    decodeIntegerRow 32 3 1 926510137474828,
    decodeIntegerRow 32 3 1 926510223566812]

def inverseACB : Matrix (LeftIndex 6 4 3) (RightIndex 6 4 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 4 3 r) []).getD (rightPosition 6 4 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_4 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_5 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_6 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_7 : (associatorInverseZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_4 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_5 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_6 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_7 : (associatorInverseZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 6 4 3 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 4 6 3) (LeftIndex 6 4 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 6 4 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_0 : (innerLeftZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_1 : (innerLeftZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_2 : (innerLeftZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_3 : (innerLeftZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_4 : (innerLeftZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_5 : (innerLeftZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_6 : (innerLeftZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_7 : (innerLeftZ 6 4 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 6 4 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_0 : (innerLeftZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_1 : (innerLeftZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_2 : (innerLeftZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_3 : (innerLeftZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_4 : (innerLeftZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_5 : (innerLeftZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_6 : (innerLeftZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_7 : (innerLeftZ 6 4 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 6 4 3 = innerACB := by
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

def assocBCA : Matrix (RightIndex 3 4 6) (LeftIndex 3 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocABC

theorem assocBCA_eq : associatorZ 3 4 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 4 6) (RightIndex 3 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 6 4 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.innerRightABC_eq

def assocCAB : Matrix (RightIndex 4 6 3) (LeftIndex 4 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocBCA

theorem assocCAB_eq : associatorZ 4 6 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 4 6 3) (LeftIndex 6 3 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 6 3 4 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms634
