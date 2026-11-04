import RMod.BrundanEllis.StackingReferenceHexagonAtoms446
import RMod.BrundanEllis.StackingReferenceHexagonAtoms464
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms644
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 4 4) (LeftIndex 6 4 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocCAB

theorem assocABC_eq : associatorZ 6 4 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocCAB_eq

def outerABC : Matrix (LeftIndex 4 4 6) (RightIndex 6 4 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 4 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 6 4) (LeftIndex 4 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocBCA

theorem assocBAC_eq : associatorZ 4 6 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocBCA_eq

def innerABC : Matrix (LeftIndex 4 6 4) (LeftIndex 6 4 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 4 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 4 4) (RightIndex 6 4 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms464.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 4 4 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms464.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523252,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21522628,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 21877654,
    decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 26286646]

def inverseACB : Matrix (LeftIndex 6 4 4) (RightIndex 6 4 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 4 4 r) []).getD (rightPosition 6 4 4 s) 0

theorem inverseACB_eq : associatorInverseZ 6 4 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 6 4) (LeftIndex 6 4 4) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 6 4 4 = innerACB := innerABC_eq

def assocBCA : Matrix (RightIndex 4 4 6) (LeftIndex 4 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocABC

theorem assocBCA_eq : associatorZ 4 4 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms446.assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 4 6) (RightIndex 4 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms464.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 6 4 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms464.innerRightABC_eq

def assocCAB : Matrix (RightIndex 4 6 4) (LeftIndex 4 6 4) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 4 6 4 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 4 6 4) (LeftIndex 6 4 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 4 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms644
