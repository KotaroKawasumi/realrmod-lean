import RMod.BrundanEllis.StackingReferenceHexagonAtoms557
import RMod.BrundanEllis.StackingReferenceHexagonAtoms575
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms755
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 5 5) (LeftIndex 7 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocCAB

theorem assocABC_eq : associatorZ 7 5 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocCAB_eq

def outerABC : Matrix (LeftIndex 5 5 7) (RightIndex 7 5 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 5 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 7 5) (LeftIndex 5 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocBCA

theorem assocBAC_eq : associatorZ 5 7 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocBCA_eq

def innerABC : Matrix (LeftIndex 5 7 5) (LeftIndex 7 5 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 5 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 5 5) (RightIndex 7 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms575.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 5 5 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms575.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 6827680,
    decodeIntegerRow 16 3 1 24674720,
    decodeIntegerRow 16 3 1 7535800,
    decodeIntegerRow 16 3 1 27981680,
    decodeIntegerRow 16 3 1 27977088,
    decodeIntegerRow 16 3 1 35511904,
    decodeIntegerRow 16 3 1 18376160,
    decodeIntegerRow 16 3 1 6825760,
    decodeIntegerRow 16 3 1 27819680,
    decodeIntegerRow 16 3 1 35170720,
    decodeIntegerRow 16 3 1 18297480,
    decodeIntegerRow 16 3 1 6458320,
    decodeIntegerRow 16 3 1 36586432,
    decodeIntegerRow 16 3 1 18293216,
    decodeIntegerRow 16 3 1 35169760,
    decodeIntegerRow 16 3 1 15222560]

def inverseACB : Matrix (LeftIndex 7 5 5) (RightIndex 7 5 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 5 5 r) []).getD (rightPosition 7 5 5 s) 0

theorem inverseACB_eq : associatorInverseZ 7 5 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 7 5) (LeftIndex 7 5 5) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 7 5 5 = innerACB := innerABC_eq

def assocBCA : Matrix (RightIndex 5 5 7) (LeftIndex 5 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocABC

theorem assocBCA_eq : associatorZ 5 5 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 5 7) (RightIndex 5 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms575.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 7 5 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms575.innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 7 5) (LeftIndex 5 7 5) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 5 7 5 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 5 7 5) (LeftIndex 7 5 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 5 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms755
