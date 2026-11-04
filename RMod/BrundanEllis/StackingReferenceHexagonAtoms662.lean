import RMod.BrundanEllis.StackingReferenceHexagonAtoms626
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms662
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 6 2) (LeftIndex 6 6 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.assocCAB

theorem assocABC_eq : associatorZ 6 6 2 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.assocCAB_eq

def outerABC : Matrix (LeftIndex 6 2 6) (RightIndex 6 6 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 6 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 6 2) (LeftIndex 6 6 2) ℤ := assocABC

theorem assocBAC_eq : associatorZ 6 6 2 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 6 6 2) (LeftIndex 6 6 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.innerACB

theorem innerABC_eq : innerLeftZ 6 6 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 2 6) (RightIndex 6 6 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 6 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19988140,
    decodeIntegerRow 16 3 1 20815024,
    decodeIntegerRow 16 3 1 7181740,
    decodeIntegerRow 16 3 1 16722896,
    decodeIntegerRow 16 3 1 16718520,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 20814520,
    decodeIntegerRow 16 3 1 23058688,
    decodeIntegerRow 16 3 1 21877888,
    decodeIntegerRow 16 3 1 23176840,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 35879560,
    decodeIntegerRow 16 3 1 7168624,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 19870096,
    decodeIntegerRow 16 3 1 21877420]

def inverseACB : Matrix (LeftIndex 6 2 6) (RightIndex 6 2 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 2 6 r) []).getD (rightPosition 6 2 6 s) 0

theorem inverseACB_eq : associatorInverseZ 6 2 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 6 6) (LeftIndex 6 2 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.innerABC

theorem innerACB_eq : innerLeftZ 6 2 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.innerABC_eq

def assocBCA : Matrix (RightIndex 6 2 6) (LeftIndex 6 2 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.assocABC

theorem assocBCA_eq : associatorZ 6 2 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.assocABC_eq

def innerRightBAC : Matrix (RightIndex 6 2 6) (RightIndex 6 6 2) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 6 6 2 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 2 6 6) (LeftIndex 2 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.assocBAC

theorem assocCAB_eq : associatorZ 2 6 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms626.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 2 6 6) (LeftIndex 6 6 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 6 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms662
