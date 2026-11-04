import RMod.BrundanEllis.StackingReferenceHexagonAtoms557
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms575
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 7 5) (LeftIndex 5 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocBCA

theorem assocABC_eq : associatorZ 5 7 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocBCA_eq

def outerABC : Matrix (LeftIndex 7 5 5) (RightIndex 5 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 7 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 5 5) (LeftIndex 7 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocCAB

theorem assocBAC_eq : associatorZ 7 5 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 5 5) (LeftIndex 5 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.innerACB

theorem innerABC_eq : innerLeftZ 5 7 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 5 7) (RightIndex 5 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 7 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 34278592,
    decodeIntegerRow 16 3 1 17273776,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21470848,
    decodeIntegerRow 16 3 1 21365904,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37465780]

def inverseACB : Matrix (LeftIndex 5 5 7) (RightIndex 5 5 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 5 7 r) []).getD (rightPosition 5 5 7 s) 0

theorem inverseACB_eq : associatorInverseZ 5 5 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 5 7) (LeftIndex 5 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.innerABC

theorem innerACB_eq : innerLeftZ 5 5 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.innerABC_eq

def assocBCA : Matrix (RightIndex 7 5 5) (LeftIndex 7 5 5) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 7 5 5 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36573820,
    decodeIntegerRow 16 3 1 18253740,
    decodeIntegerRow 16 3 1 27859152,
    decodeIntegerRow 16 3 1 35158096,
    decodeIntegerRow 16 3 1 35156140,
    decodeIntegerRow 16 3 1 15183300,
    decodeIntegerRow 16 3 1 18258224,
    decodeIntegerRow 16 3 1 6471952,
    decodeIntegerRow 16 3 1 27937940,
    decodeIntegerRow 16 3 1 35525500,
    decodeIntegerRow 16 3 1 6814096,
    decodeIntegerRow 16 3 1 24635568,
    decodeIntegerRow 16 3 1 18415740,
    decodeIntegerRow 16 3 1 6813100,
    decodeIntegerRow 16 3 1 7523152,
    decodeIntegerRow 16 3 1 27942096]

def innerRightBAC : Matrix (RightIndex 7 5 5) (RightIndex 7 5 5) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 7 5 5 r) []).getD (rightPosition 7 5 5 s) 0

theorem innerRightBAC_eq : innerRightZ 7 5 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 5 7) (LeftIndex 5 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocABC

theorem assocCAB_eq : associatorZ 5 5 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocABC_eq

def outerLeftABC : Matrix (RightIndex 5 5 7) (LeftIndex 5 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 7 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms575
