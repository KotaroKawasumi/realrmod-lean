import RMod.BrundanEllis.StackingReferenceHexagonAtoms446
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms464
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 4 6 4) (LeftIndex 4 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocBCA

theorem assocABC_eq : associatorZ 4 6 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocBCA_eq

def outerABC : Matrix (LeftIndex 6 4 4) (RightIndex 4 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 6 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 4 4) (LeftIndex 6 4 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocCAB

theorem assocBAC_eq : associatorZ 6 4 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 4 4) (LeftIndex 4 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.innerACB

theorem innerABC_eq : innerLeftZ 4 6 4 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 4 6) (RightIndex 4 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 6 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21700510,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808,
    decodeIntegerRow 16 3 1 16740310,
    decodeIntegerRow 16 3 1 35872024,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 16740472]

def inverseACB : Matrix (LeftIndex 4 4 6) (RightIndex 4 4 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 4 6 r) []).getD (rightPosition 4 4 6 s) 0

theorem inverseACB_eq : associatorInverseZ 4 4 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 4 6) (LeftIndex 4 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.innerABC

theorem innerACB_eq : innerLeftZ 4 4 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.innerABC_eq

def assocBCA : Matrix (RightIndex 6 4 4) (LeftIndex 6 4 4) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 6 4 4 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def innerRightBAC : Matrix (RightIndex 6 4 4) (RightIndex 6 4 4) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 6 4 4 r) []).getD (rightPosition 6 4 4 s) 0

theorem innerRightBAC_eq : innerRightZ 6 4 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 4 4 6) (LeftIndex 4 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocABC

theorem assocCAB_eq : associatorZ 4 4 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocABC_eq

def outerLeftABC : Matrix (RightIndex 4 4 6) (LeftIndex 4 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 6 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms464
