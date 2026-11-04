import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 26306328,
    decodeIntegerRow 16 3 1 21582490,
    decodeIntegerRow 16 3 1 21700750,
    decodeIntegerRow 16 3 1 22054792,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21530650,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 21582328,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 20991910]

def assocABC : Matrix (RightIndex 3 1 5) (LeftIndex 3 1 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 1 5 r) []).getD (leftPosition 3 1 5 s) 0

theorem assocABC_eq : associatorZ 3 1 5 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 1 5 3) (RightIndex 3 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 1 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20812586,
    decodeIntegerRow 16 3 1 19988818,
    decodeIntegerRow 16 3 1 26325778,
    decodeIntegerRow 16 3 1 35865814,
    decodeIntegerRow 16 3 1 21879842,
    decodeIntegerRow 16 3 1 23176006,
    decodeIntegerRow 16 3 1 26286394,
    decodeIntegerRow 16 3 1 35878882,
    decodeIntegerRow 16 3 1 7167946,
    decodeIntegerRow 16 3 1 26286898,
    decodeIntegerRow 16 3 1 23177458,
    decodeIntegerRow 16 3 1 21171254,
    decodeIntegerRow 16 3 1 7181122,
    decodeIntegerRow 16 3 1 26326246,
    decodeIntegerRow 16 3 1 19987354,
    decodeIntegerRow 16 3 1 22229762]

def assocBAC : Matrix (RightIndex 1 3 5) (LeftIndex 1 3 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 3 5 r) []).getD (leftPosition 1 3 5 s) 0

theorem assocBAC_eq : associatorZ 1 3 5 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 3 5) (LeftIndex 3 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 1 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 5 1) (RightIndex 3 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 1 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 34344172,
    decodeIntegerRow 16 3 1 17470616,
    decodeIntegerRow 16 3 1 5631784,
    decodeIntegerRow 16 3 1 26992812,
    decodeIntegerRow 16 3 1 8833708,
    decodeIntegerRow 16 3 1 25969784,
    decodeIntegerRow 16 3 1 37519864,
    decodeIntegerRow 16 3 1 16368852,
    decodeIntegerRow 16 3 1 17073068,
    decodeIntegerRow 16 3 1 8835064,
    decodeIntegerRow 16 3 1 26682744,
    decodeIntegerRow 16 3 1 37518292,
    decodeIntegerRow 16 3 1 25580012,
    decodeIntegerRow 16 3 1 34342936,
    decodeIntegerRow 16 3 1 16049064,
    decodeIntegerRow 16 3 1 5633452]

def inverseACB : Matrix (LeftIndex 3 5 1) (RightIndex 3 5 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 5 1 r) []).getD (rightPosition 3 5 1 s) 0

theorem inverseACB_eq : associatorInverseZ 3 5 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 3 1) (LeftIndex 3 5 1) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 5 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 8702548,
    decodeIntegerRow 16 3 1 25576104,
    decodeIntegerRow 16 3 1 37414936,
    decodeIntegerRow 16 3 1 16053908,
    decodeIntegerRow 16 3 1 34213012,
    decodeIntegerRow 16 3 1 17076936,
    decodeIntegerRow 16 3 1 5526856,
    decodeIntegerRow 16 3 1 26677868,
    decodeIntegerRow 16 3 1 25973652,
    decodeIntegerRow 16 3 1 34211656,
    decodeIntegerRow 16 3 1 16363976,
    decodeIntegerRow 16 3 1 5528428,
    decodeIntegerRow 16 3 1 17466708,
    decodeIntegerRow 16 3 1 8703784,
    decodeIntegerRow 16 3 1 26997656,
    decodeIntegerRow 16 3 1 37413268]

def assocBCA : Matrix (RightIndex 1 5 3) (LeftIndex 1 5 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 5 3 r) []).getD (leftPosition 1 5 3 s) 0

theorem assocBCA_eq : associatorZ 1 5 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 5 3) (RightIndex 1 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 3 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36049496,
    decodeIntegerRow 16 3 1 16681588,
    decodeIntegerRow 16 3 1 19948000,
    decodeIntegerRow 16 3 1 22046080,
    decodeIntegerRow 16 3 1 22063576,
    decodeIntegerRow 16 3 1 23136628,
    decodeIntegerRow 16 3 1 16799200,
    decodeIntegerRow 16 3 1 7351680,
    decodeIntegerRow 16 3 1 22050400,
    decodeIntegerRow 16 3 1 23097280,
    decodeIntegerRow 16 3 1 26365624,
    decodeIntegerRow 16 3 1 36049332,
    decodeIntegerRow 16 3 1 35695200,
    decodeIntegerRow 16 3 1 16799680,
    decodeIntegerRow 16 3 1 23138104,
    decodeIntegerRow 16 3 1 20987572]

def assocCAB : Matrix (RightIndex 5 3 1) (LeftIndex 5 3 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 5 3 1 r) []).getD (leftPosition 5 3 1 s) 0

theorem assocCAB_eq : associatorZ 5 3 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 5 3 1) (LeftIndex 3 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 1 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315
