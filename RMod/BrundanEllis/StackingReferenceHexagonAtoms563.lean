import RMod.BrundanEllis.StackingReferenceHexagonAtoms356
import RMod.BrundanEllis.StackingReferenceHexagonAtoms365
import RMod.BrundanEllis.StackingReferenceHexagonAtoms536
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms563
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 6 3) (LeftIndex 5 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBCA

theorem assocABC_eq : associatorZ 5 6 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425919,
    decodeIntegerRow 32 3 1 926510094425917,
    decodeIntegerRow 32 3 1 926510094425911,
    decodeIntegerRow 32 3 1 926510094425893,
    decodeIntegerRow 32 3 1 926510094425839,
    decodeIntegerRow 32 3 1 926510094425677,
    decodeIntegerRow 32 3 1 926510094425191,
    decodeIntegerRow 32 3 1 926510094423733,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094406237,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510094248773,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510089642951,
    decodeIntegerRow 32 3 1 926510080077013,
    decodeIntegerRow 32 3 1 926510137472641,
    decodeIntegerRow 32 3 1 926510223566083,
    decodeIntegerRow 32 3 1 926510481846409,
    decodeIntegerRow 32 3 1 926511256687387,
    decodeIntegerRow 32 3 1 926513581210321,
    decodeIntegerRow 32 3 1 926520554779123,
    decodeIntegerRow 32 3 1 926541475485529,
    decodeIntegerRow 32 3 1 926604237604747,
    decodeIntegerRow 32 3 1 926792523962401,
    decodeIntegerRow 32 3 1 927357383035363,
    decodeIntegerRow 32 3 1 929051960254249,
    decodeIntegerRow 32 3 1 934135691910907,
    decodeIntegerRow 32 3 1 949386886880881,
    decodeIntegerRow 32 3 1 995140471790803,
    decodeIntegerRow 32 3 1 1132401226520569,
    decodeIntegerRow 32 3 1 1544183490709867]

def outerABC : Matrix (LeftIndex 6 3 5) (RightIndex 5 6 3) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 6 3 5 r) []).getD (rightPosition 5 6 3 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 6 3 = outerABC := by
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

def assocBAC : Matrix (RightIndex 6 5 3) (LeftIndex 6 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.assocBCA

theorem assocBAC_eq : associatorZ 6 5 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.assocBCA_eq

def innerABC : Matrix (LeftIndex 6 5 3) (LeftIndex 5 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms536.innerACB

theorem innerABC_eq : innerLeftZ 5 6 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms536.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 3 6) (RightIndex 5 6 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 5 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 5 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 5 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 5 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 5 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_2 : (innerRightZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_3 : (innerRightZ 5 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 5 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_2 : (innerRightZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_3 : (innerRightZ 5 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 5 6 3 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 289439455219880,
    decodeIntegerRow 32 3 1 1056387059906272,
    decodeIntegerRow 32 3 1 659876824272040,
    decodeIntegerRow 32 3 1 333310960606368,
    decodeIntegerRow 32 3 1 1523099428558160,
    decodeIntegerRow 32 3 1 644058504169216,
    decodeIntegerRow 32 3 1 781949233429840,
    decodeIntegerRow 32 3 1 282661669284224,
    decodeIntegerRow 32 3 1 1570358526288080,
    decodeIntegerRow 32 3 1 781949203507456,
    decodeIntegerRow 32 3 1 1208961656973520,
    decodeIntegerRow 32 3 1 1523099415437184,
    decodeIntegerRow 32 3 1 333310948220120,
    decodeIntegerRow 32 3 1 1193143392131488,
    decodeIntegerRow 32 3 1 1056387030298840,
    decodeIntegerRow 32 3 1 1563580727593952,
    decodeIntegerRow 32 3 1 644102611725184,
    decodeIntegerRow 32 3 1 1522903122388400,
    decodeIntegerRow 32 3 1 282479833216256,
    decodeIntegerRow 32 3 1 781863110069680,
    decodeIntegerRow 32 3 1 796551886339552,
    decodeIntegerRow 32 3 1 1563761523824040,
    decodeIntegerRow 32 3 1 1519515013827488,
    decodeIntegerRow 32 3 1 1193103789152680,
    decodeIntegerRow 32 3 1 659916427259872,
    decodeIntegerRow 32 3 1 1519515001439400,
    decodeIntegerRow 32 3 1 289258658993568,
    decodeIntegerRow 32 3 1 796551856740520,
    decodeIntegerRow 32 3 1 781863139983616,
    decodeIntegerRow 32 3 1 1570540348919120,
    decodeIntegerRow 32 3 1 1522903135511424,
    decodeIntegerRow 32 3 1 1208917604844880]

def inverseACB : Matrix (LeftIndex 5 3 6) (RightIndex 5 3 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 3 6 r) []).getD (rightPosition 5 3 6 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 3 6) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 3 6) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 3 6) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 3 6) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 3 6) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 3 6) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 3 6) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 3 6) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 3 6) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 3 6) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 3 6) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 3 6) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 3 6) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 3 6) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 3 6) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 3 6) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 5 3 6) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 5 3 6) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 5 3 6) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 5 3 6) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 5 3 6) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 5 3 6) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 5 3 6) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 5 3 6) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 5 3 6) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 5 3 6) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 5 3 6) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 5 3 6) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 5 3 6) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 5 3 6) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 5 3 6) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 5 3 6) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 3 6 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 3 5 6) (LeftIndex 5 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms536.innerABC

theorem innerACB_eq : innerLeftZ 5 3 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms536.innerABC_eq

def assocBCA : Matrix (RightIndex 6 3 5) (LeftIndex 6 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocCAB

theorem assocBCA_eq : associatorZ 6 3 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocCAB_eq

def innerRightBAC : Matrix (RightIndex 6 3 5) (RightIndex 6 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 6 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 6 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 6 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 6 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_0 : (innerRightZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_1 : (innerRightZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_2 : (innerRightZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_3 : (innerRightZ 6 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_0 : (innerRightZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_1 : (innerRightZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_2 : (innerRightZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_3 : (innerRightZ 6 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_0 : (innerRightZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_1 : (innerRightZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_2 : (innerRightZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_3 : (innerRightZ 6 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_0 : (innerRightZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_1 : (innerRightZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_2 : (innerRightZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_3 : (innerRightZ 6 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 6 5 3 = innerRightBAC := by
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

def assocCAB : Matrix (RightIndex 3 5 6) (LeftIndex 3 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocABC

theorem assocCAB_eq : associatorZ 3 5 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocABC_eq

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

def outerLeftABC : Matrix (RightIndex 3 5 6) (LeftIndex 5 6 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 5 6 r) []).getD (leftPosition 5 6 3 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 6 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 6 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 6 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 6 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 5 6 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 5 6 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 5 6 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 5 6 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_0 : (outerLeftZ 5 6 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_1 : (outerLeftZ 5 6 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_2 : (outerLeftZ 5 6 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_3 : (outerLeftZ 5 6 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_0 : (outerLeftZ 5 6 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_1 : (outerLeftZ 5 6 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_2 : (outerLeftZ 5 6 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_3 : (outerLeftZ 5 6 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerLeftABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 6 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 6 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 6 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 6 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 5 6 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 5 6 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 5 6 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 5 6 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_0 : (outerLeftZ 5 6 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_1 : (outerLeftZ 5 6 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_2 : (outerLeftZ 5 6 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_3 : (outerLeftZ 5 6 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_0 : (outerLeftZ 5 6 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_1 : (outerLeftZ 5 6 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_2 : (outerLeftZ 5 6 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_3 : (outerLeftZ 5 6 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerLeftABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 6 3 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms563
