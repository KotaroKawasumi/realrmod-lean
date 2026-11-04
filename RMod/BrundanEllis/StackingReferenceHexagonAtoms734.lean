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
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms734
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 3 4) (LeftIndex 7 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocCAB

theorem assocABC_eq : associatorZ 7 3 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocCAB_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
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

def outerABC : Matrix (LeftIndex 3 4 7) (RightIndex 7 3 4) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 3 4 7 r) []).getD (rightPosition 7 3 4 s) 0

theorem outerABC_eq : outerRightZ 7 3 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 7 4) (LeftIndex 3 7 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocABC

theorem assocBAC_eq : associatorZ 3 7 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocABC_eq

def innerABC : Matrix (LeftIndex 3 7 4) (LeftIndex 7 3 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 3 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 4 3) (RightIndex 7 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 3 4 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23176786,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 35879554,
    decodeIntegerRow 16 3 1 26288834,
    decodeIntegerRow 16 3 1 19987978,
    decodeIntegerRow 16 3 1 20814538,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 20815006,
    decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7181746]

def inverseACB : Matrix (LeftIndex 7 4 3) (RightIndex 7 4 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 4 3 r) []).getD (rightPosition 7 4 3 s) 0

theorem inverseACB_eq : associatorInverseZ 7 4 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 7 3) (LeftIndex 7 4 3) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 7 4 3 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 3 4 7) (LeftIndex 3 4 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocABC

theorem assocBCA_eq : associatorZ 3 4 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 4 7) (RightIndex 3 7 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 7 4 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.innerRightABC_eq

def assocCAB : Matrix (RightIndex 4 7 3) (LeftIndex 4 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBCA

theorem assocCAB_eq : associatorZ 4 7 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 4 7 3) (LeftIndex 7 3 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 3 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms734
