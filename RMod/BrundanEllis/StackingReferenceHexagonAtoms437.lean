import RMod.BrundanEllis.StackingReferenceHexagonAtoms347
import RMod.BrundanEllis.StackingReferenceHexagonAtoms374
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms437
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 4 3 7) (LeftIndex 4 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBAC

theorem assocABC_eq : associatorZ 4 3 7 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBAC_eq

def outerABC : Matrix (LeftIndex 3 7 4) (RightIndex 4 3 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 3 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 4 7) (LeftIndex 3 4 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocABC

theorem assocBAC_eq : associatorZ 3 4 7 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocABC_eq

def innerABC : Matrix (LeftIndex 3 4 7) (LeftIndex 4 3 7) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 4 3 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 7 3) (RightIndex 4 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.innerRightBAC

theorem innerRightABC_eq : innerRightZ 4 3 7 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36403682,
    decodeIntegerRow 16 3 1 18334726,
    decodeIntegerRow 16 3 1 27900658,
    decodeIntegerRow 16 3 1 35340854,
    decodeIntegerRow 16 3 1 6642986,
    decodeIntegerRow 16 3 1 24712018,
    decodeIntegerRow 16 3 1 15146074,
    decodeIntegerRow 16 3 1 7705922,
    decodeIntegerRow 16 3 1 21696214,
    decodeIntegerRow 16 3 1 21444142,
    decodeIntegerRow 16 3 1 21484966,
    decodeIntegerRow 16 3 1 21341758,
    decodeIntegerRow 16 3 1 21691678,
    decodeIntegerRow 16 3 1 21445114,
    decodeIntegerRow 16 3 1 21483022,
    decodeIntegerRow 16 3 1 21337546]

def inverseACB : Matrix (LeftIndex 4 7 3) (RightIndex 4 7 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 7 3 r) []).getD (rightPosition 4 7 3 s) 0

theorem inverseACB_eq : associatorInverseZ 4 7 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 4 3) (LeftIndex 4 7 3) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 4 7 3 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 3 7 4) (LeftIndex 3 7 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocABC

theorem assocBCA_eq : associatorZ 3 7 4 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 7 4) (RightIndex 3 4 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 4 7 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.innerRightABC_eq

def assocCAB : Matrix (RightIndex 7 4 3) (LeftIndex 7 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocBCA

theorem assocCAB_eq : associatorZ 7 4 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocBCA_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 6643012,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 15146068]

def outerLeftABC : Matrix (RightIndex 7 4 3) (LeftIndex 4 3 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 4 3 r) []).getD (leftPosition 4 3 7 s) 0

theorem outerLeftABC_eq : outerLeftZ 4 3 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms437
