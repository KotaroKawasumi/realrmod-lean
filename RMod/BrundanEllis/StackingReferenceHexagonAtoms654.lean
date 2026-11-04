import RMod.BrundanEllis.StackingReferenceHexagonAtoms456
import RMod.BrundanEllis.StackingReferenceHexagonAtoms465
import RMod.BrundanEllis.StackingReferenceHexagonAtoms564
import RMod.BrundanEllis.StackingReferenceHexagonAtoms645
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms654
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 5 4) (LeftIndex 6 5 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocBCA

theorem assocABC_eq : associatorZ 6 5 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocBCA_eq

def outerABC : Matrix (LeftIndex 5 4 6) (RightIndex 6 5 4) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 5 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 6 4) (LeftIndex 5 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBCA

theorem assocBAC_eq : associatorZ 5 6 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBCA_eq

def innerABC : Matrix (LeftIndex 5 6 4) (LeftIndex 6 5 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms645.innerACB

theorem innerABC_eq : innerLeftZ 6 5 4 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms645.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 4 5) (RightIndex 6 5 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms564.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 5 4 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms564.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23058688,
    decodeIntegerRow 16 3 1 21877888,
    decodeIntegerRow 16 3 1 26328200,
    decodeIntegerRow 16 3 1 35879560,
    decodeIntegerRow 16 3 1 7180288,
    decodeIntegerRow 16 3 1 16757888,
    decodeIntegerRow 16 3 1 20814520,
    decodeIntegerRow 16 3 1 19869880,
    decodeIntegerRow 16 3 1 7181740,
    decodeIntegerRow 16 3 1 16762260,
    decodeIntegerRow 16 3 1 20815024,
    decodeIntegerRow 16 3 1 19870096,
    decodeIntegerRow 16 3 1 23058580,
    decodeIntegerRow 16 3 1 21877420,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 35878096]

def inverseACB : Matrix (LeftIndex 6 4 5) (RightIndex 6 4 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 4 5 r) []).getD (rightPosition 6 4 5 s) 0

theorem inverseACB_eq : associatorInverseZ 6 4 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 6 5) (LeftIndex 6 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms645.innerABC

theorem innerACB_eq : innerLeftZ 6 4 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms645.innerABC_eq

def assocBCA : Matrix (RightIndex 5 4 6) (LeftIndex 5 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBAC

theorem assocBCA_eq : associatorZ 5 4 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 5 4 6) (RightIndex 5 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms564.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 6 4 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms564.innerRightABC_eq

def assocCAB : Matrix (RightIndex 4 6 5) (LeftIndex 4 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocABC

theorem assocCAB_eq : associatorZ 4 6 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465.assocABC_eq

def outerLeftABC : Matrix (RightIndex 4 6 5) (LeftIndex 6 5 4) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 5 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms654
