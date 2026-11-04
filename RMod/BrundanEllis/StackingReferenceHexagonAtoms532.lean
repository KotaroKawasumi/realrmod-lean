import RMod.BrundanEllis.StackingReferenceHexagonAtoms325
import RMod.BrundanEllis.StackingReferenceHexagonAtoms352
import RMod.BrundanEllis.StackingReferenceHexagonAtoms523
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms532
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 3 2) (LeftIndex 5 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocCAB

theorem assocABC_eq : associatorZ 5 3 2 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocCAB_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510079374020,
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

def outerABC : Matrix (LeftIndex 3 2 5) (RightIndex 5 3 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 3 2 5 r) []).getD (rightPosition 5 3 2 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 3 2) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 5 3 2) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_0 : (outerRightZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_1 : (outerRightZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_2 : (outerRightZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_3 : (outerRightZ 5 3 2) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_0 : (outerRightZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_1 : (outerRightZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_2 : (outerRightZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_3 : (outerRightZ 5 3 2) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 3 2) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 5 3 2) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_0 : (outerRightZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_1 : (outerRightZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_2 : (outerRightZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_3 : (outerRightZ 5 3 2) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_0 : (outerRightZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_1 : (outerRightZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_2 : (outerRightZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_3 : (outerRightZ 5 3 2) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = outerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 3 2 = outerABC := by
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
  · exact outerABC_row_0_2_0
  · exact outerABC_row_0_2_1
  · exact outerABC_row_0_2_2
  · exact outerABC_row_0_2_3
  · exact outerABC_row_0_3_0
  · exact outerABC_row_0_3_1
  · exact outerABC_row_0_3_2
  · exact outerABC_row_0_3_3
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_1_2_0
  · exact outerABC_row_1_2_1
  · exact outerABC_row_1_2_2
  · exact outerABC_row_1_2_3
  · exact outerABC_row_1_3_0
  · exact outerABC_row_1_3_1
  · exact outerABC_row_1_3_2
  · exact outerABC_row_1_3_3

def assocBAC : Matrix (RightIndex 3 5 2) (LeftIndex 3 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.assocABC

theorem assocBAC_eq : associatorZ 3 5 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.assocABC_eq

def innerABC : Matrix (LeftIndex 3 5 2) (LeftIndex 5 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms523.innerACB

theorem innerABC_eq : innerLeftZ 5 3 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms523.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 2 3) (RightIndex 5 3 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.innerRightBAC

theorem innerRightABC_eq : innerRightZ 5 3 2 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 293345176593956,
    decodeIntegerRow 32 3 1 653584399005652,
    decodeIntegerRow 32 3 1 785949621635836,
    decodeIntegerRow 32 3 1 323785065769932,
    decodeIntegerRow 32 3 1 785770748882884,
    decodeIntegerRow 32 3 1 1529194327466252,
    decodeIntegerRow 32 3 1 1559759218178916,
    decodeIntegerRow 32 3 1 653781925363948,
    decodeIntegerRow 32 3 1 323785053089492,
    decodeIntegerRow 32 3 1 785949651053404,
    decodeIntegerRow 32 3 1 1199435761842892,
    decodeIntegerRow 32 3 1 1559675018788484,
    decodeIntegerRow 32 3 1 653781897362548,
    decodeIntegerRow 32 3 1 1559759211640004,
    decodeIntegerRow 32 3 1 323825874056852,
    decodeIntegerRow 32 3 1 1067249469390436,
    decodeIntegerRow 32 3 1 1202822705487076,
    decodeIntegerRow 32 3 1 278658323978772,
    decodeIntegerRow 32 3 1 1513420102081596,
    decodeIntegerRow 32 3 1 792730340786572,
    decodeIntegerRow 32 3 1 339642948471044,
    decodeIntegerRow 32 3 1 792546647483212,
    decodeIntegerRow 32 3 1 1202629656722596,
    decodeIntegerRow 32 3 1 1574445037357868,
    decodeIntegerRow 32 3 1 1060289817965332,
    decodeIntegerRow 32 3 1 339600073932444,
    decodeIntegerRow 32 3 1 278658317763212,
    decodeIntegerRow 32 3 1 1202822678218564,
    decodeIntegerRow 32 3 1 278575157718068,
    decodeIntegerRow 32 3 1 650390504862724,
    decodeIntegerRow 32 3 1 792546617379412,
    decodeIntegerRow 32 3 1 339642961299876]

def inverseACB : Matrix (LeftIndex 5 2 3) (RightIndex 5 2 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 2 3 r) []).getD (rightPosition 5 2 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 2 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 5 2 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 2 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 5 2 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 2 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_2 : (associatorInverseZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_3 : (associatorInverseZ 5 2 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 2 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_2 : (associatorInverseZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_3 : (associatorInverseZ 5 2 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 2 3 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 2 5 3) (LeftIndex 5 2 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms523.innerABC

theorem innerACB_eq : innerLeftZ 5 2 3 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms523.innerABC_eq

def assocBCA : Matrix (RightIndex 3 2 5) (LeftIndex 3 2 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocABC

theorem assocBCA_eq : associatorZ 3 2 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 2 5) (RightIndex 3 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 5 2 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms352.innerRightABC_eq

def assocCAB : Matrix (RightIndex 2 5 3) (LeftIndex 2 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocBCA

theorem assocCAB_eq : associatorZ 2 5 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms325.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 2 5 3) (LeftIndex 5 3 2) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 3 2) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 3 2) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 5 3 2) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 5 3 2) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_0 : (outerLeftZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_1 : (outerLeftZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_2 : (outerLeftZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_3 : (outerLeftZ 5 3 2) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_0 : (outerLeftZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_1 : (outerLeftZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_2 : (outerLeftZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_3 : (outerLeftZ 5 3 2) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_0 : (outerLeftZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_1 : (outerLeftZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_2 : (outerLeftZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_3 : (outerLeftZ 5 3 2) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_0 : (outerLeftZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_1 : (outerLeftZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_2 : (outerLeftZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_3 : (outerLeftZ 5 3 2) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 3 2 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms532
