import RMod.BrundanEllis.StackingReferenceHexagonAtoms456
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26328200,
    decodeIntegerRow 16 3 1 35879560,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 23176840,
    decodeIntegerRow 16 3 1 22232200,
    decodeIntegerRow 16 3 1 19988032,
    decodeIntegerRow 16 3 1 21168832,
    decodeIntegerRow 16 3 1 35864980,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 35878096,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 21877420,
    decodeIntegerRow 16 3 1 23058580,
    decodeIntegerRow 16 3 1 20815024,
    decodeIntegerRow 16 3 1 19870096]

def assocABC : Matrix (RightIndex 4 6 5) (LeftIndex 4 6 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 6 5 r) []).getD (leftPosition 4 6 5 s) 0

theorem assocABC_eq : associatorZ 4 6 5 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 6 5 4) (RightIndex 4 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 6 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 4 5) (LeftIndex 6 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocCAB

theorem assocBAC_eq : associatorZ 6 4 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 4 5) (LeftIndex 4 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.innerACB

theorem innerABC_eq : innerLeftZ 4 6 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 5 6) (RightIndex 4 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 6 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16917296,
    decodeIntegerRow 16 3 1 7233424,
    decodeIntegerRow 16 3 1 35813140,
    decodeIntegerRow 16 3 1 26128940,
    decodeIntegerRow 16 3 1 22032940,
    decodeIntegerRow 16 3 1 23110420,
    decodeIntegerRow 16 3 1 19934896,
    decodeIntegerRow 16 3 1 21009424,
    decodeIntegerRow 16 3 1 7115320,
    decodeIntegerRow 16 3 1 16563000,
    decodeIntegerRow 16 3 1 16563488,
    decodeIntegerRow 16 3 1 7115488,
    decodeIntegerRow 16 3 1 19923232,
    decodeIntegerRow 16 3 1 20974432,
    decodeIntegerRow 16 3 1 20970040,
    decodeIntegerRow 16 3 1 19921720]

def inverseACB : Matrix (LeftIndex 4 5 6) (RightIndex 4 5 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 5 6 r) []).getD (rightPosition 4 5 6 s) 0

theorem inverseACB_eq : associatorInverseZ 4 5 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 4 6) (LeftIndex 4 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.innerABC

theorem innerACB_eq : innerLeftZ 4 5 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 16917296,
    decodeIntegerRow 16 3 1 7233424,
    decodeIntegerRow 16 3 1 35813140,
    decodeIntegerRow 16 3 1 26128940,
    decodeIntegerRow 16 3 1 22032940,
    decodeIntegerRow 16 3 1 23110420,
    decodeIntegerRow 16 3 1 19934896,
    decodeIntegerRow 16 3 1 21009424,
    decodeIntegerRow 16 3 1 7115320,
    decodeIntegerRow 16 3 1 16563000,
    decodeIntegerRow 16 3 1 16563488,
    decodeIntegerRow 16 3 1 7115488,
    decodeIntegerRow 16 3 1 19923232,
    decodeIntegerRow 16 3 1 20974432,
    decodeIntegerRow 16 3 1 20970040,
    decodeIntegerRow 16 3 1 19921720]

def assocBCA : Matrix (RightIndex 6 5 4) (LeftIndex 6 5 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 5 4 r) []).getD (leftPosition 6 5 4 s) 0

theorem assocBCA_eq : associatorZ 6 5 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 5 4) (RightIndex 6 4 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 4 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 4 6) (LeftIndex 5 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBAC

theorem assocCAB_eq : associatorZ 5 4 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms456.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 5 4 6) (LeftIndex 4 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 6 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms465
