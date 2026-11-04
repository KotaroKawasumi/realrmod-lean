import RMod.BrundanEllis.StackingReferenceHexagonAtoms566
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms656
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 5 6) (LeftIndex 6 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocBAC

theorem assocABC_eq : associatorZ 6 5 6 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocBAC_eq

def outerABC : Matrix (LeftIndex 5 6 6) (RightIndex 6 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 5 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 6 6) (LeftIndex 5 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocABC

theorem assocBAC_eq : associatorZ 5 6 6 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocABC_eq

def innerABC : Matrix (LeftIndex 5 6 6) (LeftIndex 6 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 5 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 6 5) (RightIndex 6 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 5 6 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 5528476,
    decodeIntegerRow 16 3 1 26682728,
    decodeIntegerRow 16 3 1 37414888,
    decodeIntegerRow 16 3 1 16053924,
    decodeIntegerRow 16 3 1 17073048,
    decodeIntegerRow 16 3 1 8835004,
    decodeIntegerRow 16 3 1 25576124,
    decodeIntegerRow 16 3 1 34344232,
    decodeIntegerRow 16 3 1 26997672,
    decodeIntegerRow 16 3 1 37413316,
    decodeIntegerRow 16 3 1 26677884,
    decodeIntegerRow 16 3 1 37519912,
    decodeIntegerRow 16 3 1 34342876,
    decodeIntegerRow 16 3 1 17466728,
    decodeIntegerRow 16 3 1 34212952,
    decodeIntegerRow 16 3 1 17076956]

def inverseACB : Matrix (LeftIndex 6 6 5) (RightIndex 6 6 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 6 5 r) []).getD (rightPosition 6 6 5 s) 0

theorem inverseACB_eq : associatorInverseZ 6 6 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921]

def innerACB : Matrix (LeftIndex 6 6 5) (LeftIndex 6 6 5) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 6 6 5 r) []).getD (leftPosition 6 6 5 s) 0

theorem innerACB_eq : innerLeftZ 6 6 5 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 5 6 6) (LeftIndex 5 6 6) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 5 6 6 = assocBCA := assocBAC_eq

def innerRightBAC : Matrix (RightIndex 5 6 6) (RightIndex 5 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 6 6 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.innerRightABC_eq

def assocCAB : Matrix (RightIndex 6 6 5) (LeftIndex 6 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocBCA

theorem assocCAB_eq : associatorZ 6 6 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 6 6 5) (LeftIndex 6 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 5 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms656
