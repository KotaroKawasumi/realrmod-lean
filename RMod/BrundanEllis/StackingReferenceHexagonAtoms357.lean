import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 37466582,
    decodeIntegerRow 16 3 1 26837746,
    decodeIntegerRow 16 3 1 21365086,
    decodeIntegerRow 16 3 1 21468442,
    decodeIntegerRow 16 3 1 17271802,
    decodeIntegerRow 16 3 1 8768766,
    decodeIntegerRow 16 3 1 21587026,
    decodeIntegerRow 16 3 1 21719542,
    decodeIntegerRow 16 3 1 21590914,
    decodeIntegerRow 16 3 1 21720838,
    decodeIntegerRow 16 3 1 17271862,
    decodeIntegerRow 16 3 1 8768786,
    decodeIntegerRow 16 3 1 21680014,
    decodeIntegerRow 16 3 1 21573418,
    decodeIntegerRow 16 3 1 5580122,
    decodeIntegerRow 16 3 1 16208926]

def assocABC : Matrix (RightIndex 3 5 7) (LeftIndex 3 5 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 5 7 r) []).getD (leftPosition 3 5 7 s) 0

theorem assocABC_eq : associatorZ 3 5 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 5 7 3) (RightIndex 3 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 5 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16263412,
    decodeIntegerRow 16 3 1 5738252,
    decodeIntegerRow 16 3 1 17339896,
    decodeIntegerRow 16 3 1 8966424,
    decodeIntegerRow 16 3 1 8571144,
    decodeIntegerRow 16 3 1 17203816,
    decodeIntegerRow 16 3 1 5422028,
    decodeIntegerRow 16 3 1 16154548,
    decodeIntegerRow 16 3 1 5736936,
    decodeIntegerRow 16 3 1 16259464,
    decodeIntegerRow 16 3 1 8964788,
    decodeIntegerRow 16 3 1 17334988,
    decodeIntegerRow 16 3 1 17208628,
    decodeIntegerRow 16 3 1 8572748,
    decodeIntegerRow 16 3 1 16158376,
    decodeIntegerRow 16 3 1 5423304]

def assocBAC : Matrix (RightIndex 5 3 7) (LeftIndex 5 3 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 5 3 7 r) []).getD (leftPosition 5 3 7 s) 0

theorem assocBAC_eq : associatorZ 5 3 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 5 3 7) (LeftIndex 3 5 7) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 5 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 7 5) (RightIndex 3 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 5 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232]

def inverseACB : Matrix (LeftIndex 3 7 5) (RightIndex 3 7 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 7 5 r) []).getD (rightPosition 3 7 5 s) 0

theorem inverseACB_eq : associatorInverseZ 3 7 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 3 5) (LeftIndex 3 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 7 5 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232]

def assocBCA : Matrix (RightIndex 5 7 3) (LeftIndex 5 7 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 7 3 r) []).getD (leftPosition 5 7 3 s) 0

theorem assocBCA_eq : associatorZ 5 7 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 5 7 3) (RightIndex 5 3 7) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 5 3 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232,
    decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25934304,
    decodeIntegerRow 16 3 1 34331104,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 17427360,
    decodeIntegerRow 16 3 1 8820640,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680]

def assocCAB : Matrix (RightIndex 7 3 5) (LeftIndex 7 3 5) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 3 5 r) []).getD (leftPosition 7 3 5 s) 0

theorem assocCAB_eq : associatorZ 7 3 5 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 7 3 5) (LeftIndex 3 5 7) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 5 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357
