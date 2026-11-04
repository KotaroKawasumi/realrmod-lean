import RMod.BrundanEllis.StackingReferenceHexagonAtoms426
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20460476,
    decodeIntegerRow 16 3 1 23649128,
    decodeIntegerRow 16 3 1 11957404,
    decodeIntegerRow 16 3 1 40655272,
    decodeIntegerRow 16 3 1 23649120,
    decodeIntegerRow 16 3 1 22586240,
    decodeIntegerRow 16 3 1 40655200,
    decodeIntegerRow 16 3 1 31089280,
    decodeIntegerRow 16 3 1 21497440,
    decodeIntegerRow 16 3 1 21510400,
    decodeIntegerRow 16 3 1 21290080,
    decodeIntegerRow 16 3 1 21406720,
    decodeIntegerRow 16 3 1 21510076,
    decodeIntegerRow 16 3 1 21549928,
    decodeIntegerRow 16 3 1 21403804,
    decodeIntegerRow 16 3 1 21762472]

def assocABC : Matrix (RightIndex 4 6 2) (LeftIndex 4 6 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 6 2 r) []).getD (leftPosition 4 6 2 s) 0

theorem assocABC_eq : associatorZ 4 6 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 6 2 4) (RightIndex 4 6 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 6 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 4 2) (LeftIndex 6 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocCAB

theorem assocBAC_eq : associatorZ 6 4 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 4 2) (LeftIndex 4 6 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.innerACB

theorem innerABC_eq : innerLeftZ 4 6 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 2 6) (RightIndex 4 6 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 6 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26129182,
    decodeIntegerRow 16 3 1 7115404,
    decodeIntegerRow 16 3 1 21011602,
    decodeIntegerRow 16 3 1 23124244,
    decodeIntegerRow 16 3 1 21523276,
    decodeIntegerRow 16 3 1 21523118,
    decodeIntegerRow 16 3 1 21522604,
    decodeIntegerRow 16 3 1 21521182,
    decodeIntegerRow 16 3 1 21525556,
    decodeIntegerRow 16 3 1 21524062,
    decodeIntegerRow 16 3 1 21523116,
    decodeIntegerRow 16 3 1 21523282,
    decodeIntegerRow 16 3 1 23111122,
    decodeIntegerRow 16 3 1 20972236,
    decodeIntegerRow 16 3 1 35813218,
    decodeIntegerRow 16 3 1 16563244]

def inverseACB : Matrix (LeftIndex 4 2 6) (RightIndex 4 2 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 2 6 r) []).getD (rightPosition 4 2 6 s) 0

theorem inverseACB_eq : associatorInverseZ 4 2 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 4 6) (LeftIndex 4 2 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.innerABC

theorem innerACB_eq : innerLeftZ 4 2 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 35931316,
    decodeIntegerRow 16 3 1 26129182,
    decodeIntegerRow 16 3 1 19922476,
    decodeIntegerRow 16 3 1 21011602,
    decodeIntegerRow 16 3 1 21525538,
    decodeIntegerRow 16 3 1 21524116,
    decodeIntegerRow 16 3 1 21523118,
    decodeIntegerRow 16 3 1 21523276,
    decodeIntegerRow 16 3 1 21522658,
    decodeIntegerRow 16 3 1 21525556,
    decodeIntegerRow 16 3 1 21523438,
    decodeIntegerRow 16 3 1 21523116,
    decodeIntegerRow 16 3 1 26483476,
    decodeIntegerRow 16 3 1 7233502,
    decodeIntegerRow 16 3 1 20972236,
    decodeIntegerRow 16 3 1 23111122]

def assocBCA : Matrix (RightIndex 6 2 4) (LeftIndex 6 2 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 2 4 r) []).getD (leftPosition 6 2 4 s) 0

theorem assocBCA_eq : associatorZ 6 2 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 2 4) (RightIndex 6 4 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 4 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 2 4 6) (LeftIndex 2 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocBAC

theorem assocCAB_eq : associatorZ 2 4 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426.assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 23117683]

def outerLeftABC : Matrix (RightIndex 2 4 6) (LeftIndex 4 6 2) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 2 4 6 r) []).getD (leftPosition 4 6 2 s) 0

theorem outerLeftABC_eq : outerLeftZ 4 6 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms462
