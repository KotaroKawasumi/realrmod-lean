import RMod.BrundanEllis.StackingReferenceHexagonAtoms577
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms757
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 5 7) (LeftIndex 7 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocBAC

theorem assocABC_eq : associatorZ 7 5 7 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocBAC_eq

def outerABC : Matrix (LeftIndex 5 7 7) (RightIndex 7 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 5 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 7 7) (LeftIndex 5 7 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocABC

theorem assocBAC_eq : associatorZ 5 7 7 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocABC_eq

def innerABC : Matrix (LeftIndex 5 7 7) (LeftIndex 7 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 5 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 7 5) (RightIndex 7 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 5 7 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808]

def inverseACB : Matrix (LeftIndex 7 7 5) (RightIndex 7 7 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 7 5 r) []).getD (rightPosition 7 7 5 s) 0

theorem inverseACB_eq : associatorInverseZ 7 7 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21700510,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 35872024,
    decodeIntegerRow 16 3 1 16740310,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21529912]

def innerACB : Matrix (LeftIndex 7 7 5) (LeftIndex 7 7 5) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 7 7 5 r) []).getD (leftPosition 7 7 5 s) 0

theorem innerACB_eq : innerLeftZ 7 7 5 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 5 7 7) (LeftIndex 5 7 7) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 5 7 7 = assocBCA := assocBAC_eq

def innerRightBAC : Matrix (RightIndex 5 7 7) (RightIndex 5 7 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 7 7 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.innerRightABC_eq

def assocCAB : Matrix (RightIndex 7 7 5) (LeftIndex 7 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocBCA

theorem assocCAB_eq : associatorZ 7 7 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 7 7 5) (LeftIndex 7 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 5 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms757
