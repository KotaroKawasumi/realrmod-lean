import RMod.BrundanEllis.StackingReferenceHexagonAtoms347
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523282,
    decodeIntegerRow 16 3 1 21523118,
    decodeIntegerRow 16 3 1 21522658,
    decodeIntegerRow 16 3 1 21521182,
    decodeIntegerRow 16 3 1 21523444,
    decodeIntegerRow 16 3 1 21523604,
    decodeIntegerRow 16 3 1 21524116,
    decodeIntegerRow 16 3 1 21525556,
    decodeIntegerRow 16 3 1 7115404,
    decodeIntegerRow 16 3 1 26483476,
    decodeIntegerRow 16 3 1 19922476,
    decodeIntegerRow 16 3 1 22074484,
    decodeIntegerRow 16 3 1 35813218,
    decodeIntegerRow 16 3 1 16917538,
    decodeIntegerRow 16 3 1 23111122,
    decodeIntegerRow 16 3 1 21011602]

def assocABC : Matrix (RightIndex 3 7 4) (LeftIndex 3 7 4) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 7 4 r) []).getD (leftPosition 3 7 4 s) 0

theorem assocABC_eq : associatorZ 3 7 4 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
    decodeIntegerRow 16 3 1 27824216,
    decodeIntegerRow 16 3 1 24674772,
    decodeIntegerRow 16 3 1 36220984,
    decodeIntegerRow 16 3 1 35169748,
    decodeIntegerRow 16 3 1 15227096,
    decodeIntegerRow 16 3 1 18376212,
    decodeIntegerRow 16 3 1 6827704,
    decodeIntegerRow 16 3 1 27981624,
    decodeIntegerRow 16 3 1 7534828,
    decodeIntegerRow 16 3 1 36588376,
    decodeIntegerRow 16 3 1 24753452,
    decodeIntegerRow 16 3 1 27977144,
    decodeIntegerRow 16 3 1 7535788,
    decodeIntegerRow 16 3 1 36586456,
    decodeIntegerRow 16 3 1 24749292]

def outerABC : Matrix (LeftIndex 7 4 3) (RightIndex 3 7 4) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 7 4 3 r) []).getD (rightPosition 3 7 4 s) 0

theorem outerABC_eq : outerRightZ 3 7 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 3 4) (LeftIndex 7 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocCAB

theorem assocBAC_eq : associatorZ 7 3 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 3 4) (LeftIndex 3 7 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.innerACB

theorem innerABC_eq : innerLeftZ 3 7 4 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 4 7) (RightIndex 3 7 4) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 7 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26363164,
    decodeIntegerRow 16 3 1 6998044,
    decodeIntegerRow 16 3 1 22061116,
    decodeIntegerRow 16 3 1 19909436,
    decodeIntegerRow 16 3 1 23097920,
    decodeIntegerRow 16 3 1 22048000,
    decodeIntegerRow 16 3 1 35694400,
    decodeIntegerRow 16 3 1 26245120,
    decodeIntegerRow 16 3 1 22061608,
    decodeIntegerRow 16 3 1 23137448,
    decodeIntegerRow 16 3 1 26367592,
    decodeIntegerRow 16 3 1 36050152,
    decodeIntegerRow 16 3 1 35695840,
    decodeIntegerRow 16 3 1 16797280,
    decodeIntegerRow 16 3 1 23098080,
    decodeIntegerRow 16 3 1 20998240]

def inverseACB : Matrix (LeftIndex 3 4 7) (RightIndex 3 4 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 4 7 r) []).getD (rightPosition 3 4 7 s) 0

theorem inverseACB_eq : associatorInverseZ 3 4 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 3 7) (LeftIndex 3 4 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.innerABC

theorem innerACB_eq : innerLeftZ 3 4 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 16683556,
    decodeIntegerRow 16 3 1 36048676,
    decodeIntegerRow 16 3 1 20985604,
    decodeIntegerRow 16 3 1 23137284,
    decodeIntegerRow 16 3 1 23097920,
    decodeIntegerRow 16 3 1 22048000,
    decodeIntegerRow 16 3 1 35694400,
    decodeIntegerRow 16 3 1 26245120,
    decodeIntegerRow 16 3 1 36050152,
    decodeIntegerRow 16 3 1 16679128,
    decodeIntegerRow 16 3 1 23137448,
    decodeIntegerRow 16 3 1 20985112,
    decodeIntegerRow 16 3 1 20998240,
    decodeIntegerRow 16 3 1 19948640,
    decodeIntegerRow 16 3 1 16797280,
    decodeIntegerRow 16 3 1 7350880]

def assocBCA : Matrix (RightIndex 7 4 3) (LeftIndex 7 4 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 4 3 r) []).getD (leftPosition 7 4 3 s) 0

theorem assocBCA_eq : associatorZ 7 4 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 4 3) (RightIndex 7 3 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 3 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 4 3 7) (LeftIndex 4 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBAC

theorem assocCAB_eq : associatorZ 4 3 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms347.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 4 3 7) (LeftIndex 3 7 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 7 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms374
