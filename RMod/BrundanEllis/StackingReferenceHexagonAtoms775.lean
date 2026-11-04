import RMod.BrundanEllis.StackingReferenceHexagonAtoms577
import RMod.BrundanEllis.StackingReferenceHexagonAtoms757
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms775
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 7 5) (LeftIndex 7 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocBCA

theorem assocABC_eq : associatorZ 7 7 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocBCA_eq

def outerABC : Matrix (LeftIndex 7 5 7) (RightIndex 7 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 7 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 7 5) (LeftIndex 7 7 5) ℤ := assocABC

theorem assocBAC_eq : associatorZ 7 7 5 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 7 7 5) (LeftIndex 7 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms757.innerACB

theorem innerABC_eq : innerLeftZ 7 7 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms757.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 5 7) (RightIndex 7 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 7 7 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

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

def inverseACB : Matrix (LeftIndex 7 5 7) (RightIndex 7 5 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 5 7 r) []).getD (rightPosition 7 5 7 s) 0

theorem inverseACB_eq : associatorInverseZ 7 5 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 7 7) (LeftIndex 7 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms757.innerABC

theorem innerACB_eq : innerLeftZ 7 5 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms757.innerABC_eq

def assocBCA : Matrix (RightIndex 7 5 7) (LeftIndex 7 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocBAC

theorem assocBCA_eq : associatorZ 7 5 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 7 5 7) (RightIndex 7 7 5) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 7 7 5 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 7 7) (LeftIndex 5 7 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocABC

theorem assocCAB_eq : associatorZ 5 7 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms577.assocABC_eq

def outerLeftABC : Matrix (RightIndex 5 7 7) (LeftIndex 7 7 5) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 7 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms775
