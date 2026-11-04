import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19909436,
    decodeIntegerRow 16 3 1 22061608,
    decodeIntegerRow 16 3 1 23137448,
    decodeIntegerRow 16 3 1 20985604,
    decodeIntegerRow 16 3 1 7352320,
    decodeIntegerRow 16 3 1 26249440,
    decodeIntegerRow 16 3 1 7350880,
    decodeIntegerRow 16 3 1 26245120,
    decodeIntegerRow 16 3 1 22048480,
    decodeIntegerRow 16 3 1 23097920,
    decodeIntegerRow 16 3 1 20998720,
    decodeIntegerRow 16 3 1 19948640,
    decodeIntegerRow 16 3 1 26367592,
    decodeIntegerRow 16 3 1 36048676,
    decodeIntegerRow 16 3 1 26363164,
    decodeIntegerRow 16 3 1 36050152]

def assocABC : Matrix (RightIndex 5 5 7) (LeftIndex 5 5 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 5 7 r) []).getD (leftPosition 5 5 7 s) 0

theorem assocABC_eq : associatorZ 5 5 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 5 7 5) (RightIndex 5 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 5 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 5 7) (LeftIndex 5 5 7) ℤ := assocABC

theorem assocBAC_eq : associatorZ 5 5 7 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36573820,
    decodeIntegerRow 16 3 1 18253740,
    decodeIntegerRow 16 3 1 27859152,
    decodeIntegerRow 16 3 1 35158096,
    decodeIntegerRow 16 3 1 35156140,
    decodeIntegerRow 16 3 1 15183300,
    decodeIntegerRow 16 3 1 18258224,
    decodeIntegerRow 16 3 1 6471952,
    decodeIntegerRow 16 3 1 27937940,
    decodeIntegerRow 16 3 1 35525500,
    decodeIntegerRow 16 3 1 6814096,
    decodeIntegerRow 16 3 1 24635568,
    decodeIntegerRow 16 3 1 18415740,
    decodeIntegerRow 16 3 1 6813100,
    decodeIntegerRow 16 3 1 7523152,
    decodeIntegerRow 16 3 1 27942096]

def innerABC : Matrix (LeftIndex 5 5 7) (LeftIndex 5 5 7) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 5 5 7 r) []).getD (leftPosition 5 5 7 s) 0

theorem innerABC_eq : innerLeftZ 5 5 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 7 5) (RightIndex 5 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 5 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 21529192,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21530650,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 22054792,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 21346456]

def inverseACB : Matrix (LeftIndex 5 7 5) (RightIndex 5 7 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 7 5 r) []).getD (rightPosition 5 7 5 s) 0

theorem inverseACB_eq : associatorInverseZ 5 7 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 5 5) (LeftIndex 5 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 7 5 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21582490,
    decodeIntegerRow 16 3 1 21700750,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 26306328,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21582328,
    decodeIntegerRow 16 3 1 21700264]

def assocBCA : Matrix (RightIndex 5 7 5) (LeftIndex 5 7 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 7 5 r) []).getD (leftPosition 5 7 5 s) 0

theorem assocBCA_eq : associatorZ 5 7 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 5 7 5) (RightIndex 5 5 7) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 5 7 = innerRightBAC := innerRightABC_eq

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 37414780,
    decodeIntegerRow 16 3 1 16053420,
    decodeIntegerRow 16 3 1 25580496,
    decodeIntegerRow 16 3 1 34342768,
    decodeIntegerRow 16 3 1 8702380,
    decodeIntegerRow 16 3 1 25575620,
    decodeIntegerRow 16 3 1 16049552,
    decodeIntegerRow 16 3 1 5633296,
    decodeIntegerRow 16 3 1 26682260,
    decodeIntegerRow 16 3 1 37518460,
    decodeIntegerRow 16 3 1 34213168,
    decodeIntegerRow 16 3 1 17077424,
    decodeIntegerRow 16 3 1 17072580,
    decodeIntegerRow 16 3 1 8835220,
    decodeIntegerRow 16 3 1 5527024,
    decodeIntegerRow 16 3 1 26678352]

def assocCAB : Matrix (RightIndex 7 5 5) (LeftIndex 7 5 5) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 5 5 r) []).getD (leftPosition 7 5 5 s) 0

theorem assocCAB_eq : associatorZ 7 5 5 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 7 5 5) (LeftIndex 5 5 7) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 5 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms557
