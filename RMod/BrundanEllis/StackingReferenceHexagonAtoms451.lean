import RMod.BrundanEllis.StackingReferenceHexagonAtoms415
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21516808,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 35872024]

def assocABC : Matrix (RightIndex 4 5 1) (LeftIndex 4 5 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 5 1 r) []).getD (leftPosition 4 5 1 s) 0

theorem assocABC_eq : associatorZ 4 5 1 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 5 1 4) (RightIndex 4 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 5 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 4 1) (LeftIndex 5 4 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocCAB

theorem assocBAC_eq : associatorZ 5 4 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocCAB_eq

def innerABC : Matrix (LeftIndex 5 4 1) (LeftIndex 4 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.innerACB

theorem innerABC_eq : innerLeftZ 4 5 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 1 5) (RightIndex 4 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 5 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26306326,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 20991892,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 21514612,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21346294,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21700588,
    decodeIntegerRow 16 3 1 21464068,
    decodeIntegerRow 16 3 1 7174452,
    decodeIntegerRow 16 3 1 16740388,
    decodeIntegerRow 16 3 1 23117674,
    decodeIntegerRow 16 3 1 22054774]

def inverseACB : Matrix (LeftIndex 4 1 5) (RightIndex 4 1 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 1 5 r) []).getD (rightPosition 4 1 5 s) 0

theorem inverseACB_eq : associatorInverseZ 4 1 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 4 5) (LeftIndex 4 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.innerABC

theorem innerACB_eq : innerLeftZ 4 1 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 35419558,
    decodeIntegerRow 16 3 1 24528298,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 6603646,
    decodeIntegerRow 16 3 1 21522414,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 21521242,
    decodeIntegerRow 16 3 1 21523818,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21523874,
    decodeIntegerRow 16 3 1 21525454,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 7784626,
    decodeIntegerRow 16 3 1 6682378,
    decodeIntegerRow 16 3 1 28071238]

def assocBCA : Matrix (RightIndex 5 1 4) (LeftIndex 5 1 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 1 4 r) []).getD (leftPosition 5 1 4 s) 0

theorem assocBCA_eq : associatorZ 5 1 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 5 1 4) (RightIndex 5 4 1) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 5 4 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 1 4 5) (LeftIndex 1 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocBAC

theorem assocCAB_eq : associatorZ 1 4 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523348,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21522388,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21602092,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 6643012,
    decodeIntegerRow 16 3 1 27900652]

def outerLeftABC : Matrix (RightIndex 1 4 5) (LeftIndex 4 5 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 4 5 r) []).getD (leftPosition 4 5 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 4 5 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451
