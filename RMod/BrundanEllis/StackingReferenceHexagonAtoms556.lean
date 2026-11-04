import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19420960,
    decodeIntegerRow 16 3 1 20448832,
    decodeIntegerRow 16 3 1 20445880,
    decodeIntegerRow 16 3 1 23620000,
    decodeIntegerRow 16 3 1 2627360,
    decodeIntegerRow 16 3 1 31207232,
    decodeIntegerRow 16 3 1 11839160,
    decodeIntegerRow 16 3 1 2628000,
    decodeIntegerRow 16 3 1 2155616,
    decodeIntegerRow 16 3 1 30971360,
    decodeIntegerRow 16 3 1 30971040,
    decodeIntegerRow 16 3 1 40891760,
    decodeIntegerRow 16 3 1 23672416,
    decodeIntegerRow 16 3 1 22574560,
    decodeIntegerRow 16 3 1 20475040,
    decodeIntegerRow 16 3 1 23678320]

def assocABC : Matrix (RightIndex 5 5 6) (LeftIndex 5 5 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 5 6 r) []).getD (leftPosition 5 5 6 s) 0

theorem assocABC_eq : associatorZ 5 5 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def outerABC : Matrix (LeftIndex 5 6 5) (RightIndex 5 5 6) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 5 6 5 r) []).getD (rightPosition 5 5 6 s) 0

theorem outerABC_eq : outerRightZ 5 5 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 5 6) (LeftIndex 5 5 6) ℤ := assocABC

theorem assocBAC_eq : associatorZ 5 5 6 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20431336,
    decodeIntegerRow 16 3 1 23634508,
    decodeIntegerRow 16 3 1 40773176,
    decodeIntegerRow 16 3 1 30853428,
    decodeIntegerRow 16 3 1 19409224,
    decodeIntegerRow 16 3 1 20437132,
    decodeIntegerRow 16 3 1 30852776,
    decodeIntegerRow 16 3 1 2273228,
    decodeIntegerRow 16 3 1 31325816,
    decodeIntegerRow 16 3 1 2509748,
    decodeIntegerRow 16 3 1 23660824,
    decodeIntegerRow 16 3 1 22562932,
    decodeIntegerRow 16 3 1 2509416,
    decodeIntegerRow 16 3 1 11721548,
    decodeIntegerRow 16 3 1 20489656,
    decodeIntegerRow 16 3 1 23663668]

def innerABC : Matrix (LeftIndex 5 5 6) (LeftIndex 5 5 6) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 5 5 6 r) []).getD (leftPosition 5 5 6 s) 0

theorem innerABC_eq : innerLeftZ 5 5 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 6 5) (RightIndex 5 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 8 × Fin 1) (Fin 2 × Fin 8 × Fin 1) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 5 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991916,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 23117684,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21516556]

def inverseACB : Matrix (LeftIndex 5 6 5) (RightIndex 5 6 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 6 5 r) []).getD (rightPosition 5 6 5 s) 0

theorem inverseACB_eq : associatorInverseZ 5 6 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 5 5) (LeftIndex 5 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 8 × Fin 1) (Fin 2 × Fin 8 × Fin 1) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 6 5 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21701236,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21503758,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 21462124,
    decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 21529678]

def assocBCA : Matrix (RightIndex 5 6 5) (LeftIndex 5 6 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 6 5 r) []).getD (leftPosition 5 6 5 s) 0

theorem assocBCA_eq : associatorZ 5 6 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 5 6 5) (RightIndex 5 5 6) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 5 6 = innerRightBAC := innerRightABC_eq

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 37466620,
    decodeIntegerRow 16 3 1 25774896,
    decodeIntegerRow 16 3 1 21363952,
    decodeIntegerRow 16 3 1 21456940,
    decodeIntegerRow 16 3 1 37466560,
    decodeIntegerRow 16 3 1 17271840,
    decodeIntegerRow 16 3 1 21678880,
    decodeIntegerRow 16 3 1 21458560,
    decodeIntegerRow 16 3 1 21328960,
    decodeIntegerRow 16 3 1 21575200,
    decodeIntegerRow 16 3 1 8768800,
    decodeIntegerRow 16 3 1 26837760,
    decodeIntegerRow 16 3 1 21722620,
    decodeIntegerRow 16 3 1 21576496,
    decodeIntegerRow 16 3 1 8768752,
    decodeIntegerRow 16 3 1 16208940]

def assocCAB : Matrix (RightIndex 6 5 5) (LeftIndex 6 5 5) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 5 5 r) []).getD (leftPosition 6 5 5 s) 0

theorem assocCAB_eq : associatorZ 6 5 5 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 6 5 5) (LeftIndex 5 5 6) ℤ :=
  (show Matrix (Fin 4 × Fin 4 × Fin 1) (Fin 4 × Fin 4 × Fin 1) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 5 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556
