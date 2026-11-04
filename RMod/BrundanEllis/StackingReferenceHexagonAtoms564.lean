import RMod.BrundanEllis.StackingReferenceHexagonAtoms456
import RMod.BrundanEllis.StackingReferenceHexagonAtoms465
import RMod.BrundanEllis.StackingReferenceHexagonAtoms546
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms564
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 6 4) (LeftIndex 5 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBCA

theorem assocABC_eq : associatorZ 5 6 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBCA_eq

def outerABC : Matrix (LeftIndex 6 4 5) (RightIndex 5 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 6 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 5 4) (LeftIndex 6 5 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocBCA

theorem assocBAC_eq : associatorZ 6 5 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocBCA_eq

def innerABC : Matrix (LeftIndex 6 5 4) (LeftIndex 5 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms546.innerACB

theorem innerABC_eq : innerLeftZ 5 6 4 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms546.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 4 6) (RightIndex 5 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 6 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26325760,
    decodeIntegerRow 16 3 1 35878720,
    decodeIntegerRow 16 3 1 19870720,
    decodeIntegerRow 16 3 1 20816960,
    decodeIntegerRow 16 3 1 21879840,
    decodeIntegerRow 16 3 1 23059360,
    decodeIntegerRow 16 3 1 35865760,
    decodeIntegerRow 16 3 1 26286880,
    decodeIntegerRow 16 3 1 7167784,
    decodeIntegerRow 16 3 1 16720456,
    decodeIntegerRow 16 3 1 22234136,
    decodeIntegerRow 16 3 1 23177464,
    decodeIntegerRow 16 3 1 19988812,
    decodeIntegerRow 16 3 1 21171252,
    decodeIntegerRow 16 3 1 16760308,
    decodeIntegerRow 16 3 1 7181068]

def inverseACB : Matrix (LeftIndex 5 4 6) (RightIndex 5 4 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 4 6 r) []).getD (rightPosition 5 4 6 s) 0

theorem inverseACB_eq : associatorInverseZ 5 4 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 5 6) (LeftIndex 5 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms546.innerABC

theorem innerACB_eq : innerLeftZ 5 4 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms546.innerABC_eq

def assocBCA : Matrix (RightIndex 6 4 5) (LeftIndex 6 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocCAB

theorem assocBCA_eq : associatorZ 6 4 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocCAB_eq

def innerRightBAC : Matrix (RightIndex 6 4 5) (RightIndex 6 5 4) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 5 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 4 5 6) (LeftIndex 4 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocABC

theorem assocCAB_eq : associatorZ 4 5 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocABC_eq

def outerLeftABC : Matrix (RightIndex 4 5 6) (LeftIndex 5 6 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 6 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms564
