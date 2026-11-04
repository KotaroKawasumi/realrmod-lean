import RMod.BrundanEllis.StackingReferenceHexagonAtoms347
import RMod.BrundanEllis.StackingReferenceHexagonAtoms374
import RMod.BrundanEllis.StackingReferenceHexagonAtoms437
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms473
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 4 7 3) (LeftIndex 4 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBCA

theorem assocABC_eq : associatorZ 4 7 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBCA_eq

def outerABC : Matrix (LeftIndex 7 3 4) (RightIndex 4 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 7 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 4 3) (LeftIndex 7 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocBCA

theorem assocBAC_eq : associatorZ 7 4 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374.assocBCA_eq

def innerABC : Matrix (LeftIndex 7 4 3) (LeftIndex 4 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms437.innerACB

theorem innerABC_eq : innerLeftZ 4 7 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms437.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 3 7) (RightIndex 4 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 7 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21529912,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 35872510]

def inverseACB : Matrix (LeftIndex 4 3 7) (RightIndex 4 3 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 3 7 r) []).getD (rightPosition 4 3 7 s) 0

theorem inverseACB_eq : associatorInverseZ 4 3 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 4 7) (LeftIndex 4 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms437.innerABC

theorem innerACB_eq : innerLeftZ 4 3 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms437.innerABC_eq

def assocBCA : Matrix (RightIndex 7 3 4) (LeftIndex 7 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocCAB

theorem assocBCA_eq : associatorZ 7 3 4 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocCAB_eq

def innerRightBAC : Matrix (RightIndex 7 3 4) (RightIndex 7 4 3) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 4 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 3 4 7) (LeftIndex 3 4 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocABC

theorem assocCAB_eq : associatorZ 3 4 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
    decodeIntegerRow 16 3 1 27824216,
    decodeIntegerRow 16 3 1 24674772,
    decodeIntegerRow 16 3 1 36220984,
    decodeIntegerRow 16 3 1 35169748,
    decodeIntegerRow 16 3 1 15227096,
    decodeIntegerRow 16 3 1 18376212,
    decodeIntegerRow 16 3 1 6827704,
    decodeIntegerRow 16 3 1 27981624,
    decodeIntegerRow 16 3 1 7534828,
    decodeIntegerRow 16 3 1 36588376,
    decodeIntegerRow 16 3 1 24753452,
    decodeIntegerRow 16 3 1 27977144,
    decodeIntegerRow 16 3 1 7535788,
    decodeIntegerRow 16 3 1 36586456,
    decodeIntegerRow 16 3 1 24749292]

def outerLeftABC : Matrix (RightIndex 3 4 7) (LeftIndex 4 7 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 4 7 r) []).getD (leftPosition 4 7 3 s) 0

theorem outerLeftABC_eq : outerLeftZ 4 7 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms473
