import RMod.BrundanEllis.StackingReferenceHexagonAtoms366
import RMod.BrundanEllis.StackingReferenceHexagonAtoms636
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms663
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 6 3) (LeftIndex 6 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocBCA

theorem assocABC_eq : associatorZ 6 6 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocBCA_eq

def outerABC : Matrix (LeftIndex 6 3 6) (RightIndex 6 6 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 6 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 6 3) (LeftIndex 6 6 3) ℤ := assocABC

theorem assocBAC_eq : associatorZ 6 6 3 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 6 6 3) (LeftIndex 6 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms636.innerACB

theorem innerABC_eq : innerLeftZ 6 6 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms636.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 3 6) (RightIndex 6 6 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 6 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23058526,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 7167166,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 26323826,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 23058742,
    decodeIntegerRow 16 3 1 20814538,
    decodeIntegerRow 16 3 1 19869934,
    decodeIntegerRow 16 3 1 16762262,
    decodeIntegerRow 16 3 1 7181746,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16757886,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 22231714]

def inverseACB : Matrix (LeftIndex 6 3 6) (RightIndex 6 3 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 3 6 r) []).getD (rightPosition 6 3 6 s) 0

theorem inverseACB_eq : associatorInverseZ 6 3 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 6 6) (LeftIndex 6 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms636.innerABC

theorem innerACB_eq : innerLeftZ 6 3 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms636.innerABC_eq

def assocBCA : Matrix (RightIndex 6 3 6) (LeftIndex 6 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocBAC

theorem assocBCA_eq : associatorZ 6 3 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 6 3 6) (RightIndex 6 6 3) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 6 6 3 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 3 6 6) (LeftIndex 3 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocABC

theorem assocCAB_eq : associatorZ 3 6 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocABC_eq

def outerLeftABC : Matrix (RightIndex 3 6 6) (LeftIndex 6 6 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 6 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms663
