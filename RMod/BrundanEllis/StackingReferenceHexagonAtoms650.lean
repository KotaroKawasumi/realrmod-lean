import RMod.BrundanEllis.StackingReferenceHexagonAtoms506
import RMod.BrundanEllis.StackingReferenceHexagonAtoms560
import RMod.BrundanEllis.StackingReferenceHexagonAtoms605
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms650
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 5 0) (LeftIndex 6 5 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocCAB

theorem assocABC_eq : associatorZ 6 5 0 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocCAB_eq

def outerABC : Matrix (LeftIndex 5 0 6) (RightIndex 6 5 0) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 5 0 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 6 0) (LeftIndex 5 6 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.assocABC

theorem assocBAC_eq : associatorZ 5 6 0 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.assocABC_eq

def innerABC : Matrix (LeftIndex 5 6 0) (LeftIndex 6 5 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms605.innerACB

theorem innerABC_eq : innerLeftZ 6 5 0 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms605.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 0 5) (RightIndex 6 5 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 5 0 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.innerRightBAC_eq

def inverseACB : Matrix (LeftIndex 6 0 5) (RightIndex 6 0 5) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem inverseACB_eq : associatorInverseZ 6 0 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 0 6 5) (LeftIndex 6 0 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms605.innerABC

theorem innerACB_eq : innerLeftZ 6 0 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms605.innerABC_eq

def assocBCA : Matrix (RightIndex 5 0 6) (LeftIndex 5 0 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocABC

theorem assocBCA_eq : associatorZ 5 0 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 0 6) (RightIndex 5 6 0) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 6 0 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms560.innerRightABC_eq

def assocCAB : Matrix (RightIndex 0 6 5) (LeftIndex 0 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocBCA

theorem assocCAB_eq : associatorZ 0 6 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms506.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 0 6 5) (LeftIndex 6 5 0) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 5 0 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms650
