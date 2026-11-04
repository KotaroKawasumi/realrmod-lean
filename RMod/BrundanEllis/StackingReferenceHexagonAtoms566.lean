import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 34211716,
    decodeIntegerRow 16 3 1 17073048,
    decodeIntegerRow 16 3 1 8702488,
    decodeIntegerRow 16 3 1 25576124,
    decodeIntegerRow 16 3 1 16363992,
    decodeIntegerRow 16 3 1 5528476,
    decodeIntegerRow 16 3 1 26992796,
    decodeIntegerRow 16 3 1 37414888,
    decodeIntegerRow 16 3 1 17076956,
    decodeIntegerRow 16 3 1 8833768,
    decodeIntegerRow 16 3 1 25579992,
    decodeIntegerRow 16 3 1 34342876,
    decodeIntegerRow 16 3 1 5526808,
    decodeIntegerRow 16 3 1 26677884,
    decodeIntegerRow 16 3 1 37413316,
    decodeIntegerRow 16 3 1 16049048]

def assocABC : Matrix (RightIndex 5 6 6) (LeftIndex 5 6 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 6 6 r) []).getD (leftPosition 5 6 6 s) 0

theorem assocABC_eq : associatorZ 5 6 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 6 6 5) (RightIndex 5 6 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 6 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20974432,
    decodeIntegerRow 16 3 1 19934896,
    decodeIntegerRow 16 3 1 16917780,
    decodeIntegerRow 16 3 1 7115320,
    decodeIntegerRow 16 3 1 23125000,
    decodeIntegerRow 16 3 1 21013780,
    decodeIntegerRow 16 3 1 7233424,
    decodeIntegerRow 16 3 1 26483232,
    decodeIntegerRow 16 3 1 35931232,
    decodeIntegerRow 16 3 1 16917296,
    decodeIntegerRow 16 3 1 23110420,
    decodeIntegerRow 16 3 1 20970040,
    decodeIntegerRow 16 3 1 26483720,
    decodeIntegerRow 16 3 1 35813140,
    decodeIntegerRow 16 3 1 21009424,
    decodeIntegerRow 16 3 1 19923232]

def assocBAC : Matrix (RightIndex 6 5 6) (LeftIndex 6 5 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 6 5 6 r) []).getD (leftPosition 6 5 6 s) 0

theorem assocBAC_eq : associatorZ 6 5 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 6 5 6) (LeftIndex 5 6 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 6 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921]

def innerRightABC : Matrix (RightIndex 5 6 6) (RightIndex 5 6 6) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 5 6 6 r) []).getD (rightPosition 5 6 6 s) 0

theorem innerRightABC_eq : innerRightZ 5 6 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 34226128,
    decodeIntegerRow 16 3 1 17116304,
    decodeIntegerRow 16 3 1 8715664,
    decodeIntegerRow 16 3 1 25615472,
    decodeIntegerRow 16 3 1 16408220,
    decodeIntegerRow 16 3 1 5513740,
    decodeIntegerRow 16 3 1 16014540,
    decodeIntegerRow 16 3 1 5644900,
    decodeIntegerRow 16 3 1 27037020,
    decodeIntegerRow 16 3 1 37400140,
    decodeIntegerRow 16 3 1 16403340,
    decodeIntegerRow 16 3 1 5515300,
    decodeIntegerRow 16 3 1 8716912,
    decodeIntegerRow 16 3 1 25619376,
    decodeIntegerRow 16 3 1 8821936,
    decodeIntegerRow 16 3 1 25934288]

def inverseACB : Matrix (LeftIndex 5 6 6) (RightIndex 5 6 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 6 6 r) []).getD (rightPosition 5 6 6 s) 0

theorem inverseACB_eq : associatorInverseZ 5 6 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 5 6) (LeftIndex 5 6 6) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 5 6 6 = innerACB := innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
    decodeIntegerRow 16 3 1 16014072,
    decodeIntegerRow 16 3 1 37532872,
    decodeIntegerRow 16 3 1 16407716,
    decodeIntegerRow 16 3 1 17426876,
    decodeIntegerRow 16 3 1 8717128,
    decodeIntegerRow 16 3 1 25934792,
    decodeIntegerRow 16 3 1 34224676,
    decodeIntegerRow 16 3 1 17116808,
    decodeIntegerRow 16 3 1 8820484,
    decodeIntegerRow 16 3 1 17431716,
    decodeIntegerRow 16 3 1 8715448,
    decodeIntegerRow 16 3 1 37531528,
    decodeIntegerRow 16 3 1 16403844,
    decodeIntegerRow 16 3 1 5646364,
    decodeIntegerRow 16 3 1 27036552]

def assocBCA : Matrix (RightIndex 6 6 5) (LeftIndex 6 6 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 6 5 r) []).getD (leftPosition 6 6 5 s) 0

theorem assocBCA_eq : associatorZ 6 6 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 6 5) (RightIndex 6 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 5 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 6 5 6) (LeftIndex 6 5 6) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 6 5 6 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 6 5 6) (LeftIndex 5 6 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 6 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms566
