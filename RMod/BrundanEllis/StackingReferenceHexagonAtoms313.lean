import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms313
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346214,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 21503686]

def assocABC : Matrix (RightIndex 3 1 3) (LeftIndex 3 1 3) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 1 3 r) []).getD (leftPosition 3 1 3 s) 0

theorem assocABC_eq : associatorZ 3 1 3 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 1 3 3) (RightIndex 3 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 1 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37465780,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 21575872]

def assocBAC : Matrix (RightIndex 1 3 3) (LeftIndex 1 3 3) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 3 3 r) []).getD (leftPosition 1 3 3 s) 0

theorem assocBAC_eq : associatorZ 1 3 3 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 3 3) (LeftIndex 3 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 1 3 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 3 1) (RightIndex 3 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 1 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 26306328]

def inverseACB : Matrix (LeftIndex 3 3 1) (RightIndex 3 3 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 3 1 r) []).getD (rightPosition 3 3 1 s) 0

theorem inverseACB_eq : associatorInverseZ 3 3 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36219508,
    decodeIntegerRow 16 3 1 27819788,
    decodeIntegerRow 16 3 1 24670344,
    decodeIntegerRow 16 3 1 35169256,
    decodeIntegerRow 16 3 1 6826228,
    decodeIntegerRow 16 3 1 15222668,
    decodeIntegerRow 16 3 1 18371784,
    decodeIntegerRow 16 3 1 7875496,
    decodeIntegerRow 16 3 1 27977304,
    decodeIntegerRow 16 3 1 36586936,
    decodeIntegerRow 16 3 1 7536268,
    decodeIntegerRow 16 3 1 18297588,
    decodeIntegerRow 16 3 1 27981464,
    decodeIntegerRow 16 3 1 36587896,
    decodeIntegerRow 16 3 1 7534348,
    decodeIntegerRow 16 3 1 18293108]

def innerACB : Matrix (LeftIndex 3 3 1) (LeftIndex 3 3 1) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 3 3 1 r) []).getD (leftPosition 3 3 1 s) 0

theorem innerACB_eq : innerLeftZ 3 3 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37465780,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 21575872]

def assocBCA : Matrix (RightIndex 1 3 3) (LeftIndex 1 3 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 3 3 r) []).getD (leftPosition 1 3 3 s) 0

theorem assocBCA_eq : associatorZ 1 3 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36219508,
    decodeIntegerRow 16 3 1 27819788,
    decodeIntegerRow 16 3 1 24670344,
    decodeIntegerRow 16 3 1 35169256,
    decodeIntegerRow 16 3 1 6826228,
    decodeIntegerRow 16 3 1 15222668,
    decodeIntegerRow 16 3 1 18371784,
    decodeIntegerRow 16 3 1 7875496,
    decodeIntegerRow 16 3 1 27977304,
    decodeIntegerRow 16 3 1 36586936,
    decodeIntegerRow 16 3 1 7536268,
    decodeIntegerRow 16 3 1 18297588,
    decodeIntegerRow 16 3 1 27981464,
    decodeIntegerRow 16 3 1 36587896,
    decodeIntegerRow 16 3 1 7534348,
    decodeIntegerRow 16 3 1 18293108]

def innerRightBAC : Matrix (RightIndex 1 3 3) (RightIndex 1 3 3) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 1 3 3 r) []).getD (rightPosition 1 3 3 s) 0

theorem innerRightBAC_eq : innerRightZ 1 3 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21503758,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21462124,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 20991916,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 35872276,
    decodeIntegerRow 16 3 1 26306356]

def assocCAB : Matrix (RightIndex 3 3 1) (LeftIndex 3 3 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 3 3 1 r) []).getD (leftPosition 3 3 1 s) 0

theorem assocCAB_eq : associatorZ 3 3 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 3 3 1) (LeftIndex 3 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 1 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms313
