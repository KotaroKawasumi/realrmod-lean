import RMod.BrundanEllis.StackingReferenceHexagonAtoms567
import RMod.BrundanEllis.StackingReferenceHexagonAtoms576
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms657
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 5 7) (LeftIndex 6 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBAC

theorem assocABC_eq : associatorZ 6 5 7 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBAC_eq

def outerABC : Matrix (LeftIndex 5 7 6) (RightIndex 6 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 5 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 6 7) (LeftIndex 5 6 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocABC

theorem assocBAC_eq : associatorZ 5 6 7 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocABC_eq

def innerABC : Matrix (LeftIndex 5 6 7) (LeftIndex 6 5 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 5 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 7 5) (RightIndex 6 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 5 7 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523270,
    decodeIntegerRow 16 3 1 21523144,
    decodeIntegerRow 16 3 1 21522632,
    decodeIntegerRow 16 3 1 21521170,
    decodeIntegerRow 16 3 1 20106184,
    decodeIntegerRow 16 3 1 22113850,
    decodeIntegerRow 16 3 1 7154770,
    decodeIntegerRow 16 3 1 26299768,
    decodeIntegerRow 16 3 1 21995752,
    decodeIntegerRow 16 3 1 23294830,
    decodeIntegerRow 16 3 1 26312890,
    decodeIntegerRow 16 3 1 35852584,
    decodeIntegerRow 16 3 1 21523630,
    decodeIntegerRow 16 3 1 21523288,
    decodeIntegerRow 16 3 1 21525544,
    decodeIntegerRow 16 3 1 21522630]

def inverseACB : Matrix (LeftIndex 6 7 5) (RightIndex 6 7 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 7 5 r) []).getD (rightPosition 6 7 5 s) 0

theorem inverseACB_eq : associatorInverseZ 6 7 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 36404194,
    decodeIntegerRow 16 3 1 15148174,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 35339854]

def innerACB : Matrix (LeftIndex 7 6 5) (LeftIndex 6 7 5) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 7 6 5 r) []).getD (leftPosition 6 7 5 s) 0

theorem innerACB_eq : innerLeftZ 6 7 5 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 5 7 6) (LeftIndex 5 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocABC

theorem assocBCA_eq : associatorZ 5 7 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 7 6) (RightIndex 5 6 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 6 7 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.innerRightABC_eq

def assocCAB : Matrix (RightIndex 7 6 5) (LeftIndex 7 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocBCA

theorem assocCAB_eq : associatorZ 7 6 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576.assocBCA_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def outerLeftABC : Matrix (RightIndex 7 6 5) (LeftIndex 6 5 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 6 5 r) []).getD (leftPosition 6 5 7 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 5 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms657
