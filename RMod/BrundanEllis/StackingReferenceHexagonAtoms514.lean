import RMod.BrundanEllis.StackingReferenceHexagonAtoms415
import RMod.BrundanEllis.StackingReferenceHexagonAtoms451
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms514
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 1 4) (LeftIndex 5 1 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.assocBCA

theorem assocABC_eq : associatorZ 5 1 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36575260,
    decodeIntegerRow 16 3 1 27937776,
    decodeIntegerRow 16 3 1 24635408,
    decodeIntegerRow 16 3 1 35156620,
    decodeIntegerRow 16 3 1 35157616,
    decodeIntegerRow 16 3 1 24631140,
    decodeIntegerRow 16 3 1 15104460,
    decodeIntegerRow 16 3 1 6473392,
    decodeIntegerRow 16 3 1 18253904,
    decodeIntegerRow 16 3 1 35524060,
    decodeIntegerRow 16 3 1 36234100,
    decodeIntegerRow 16 3 1 15187728,
    decodeIntegerRow 16 3 1 27863580,
    decodeIntegerRow 16 3 1 6814576,
    decodeIntegerRow 16 3 1 35525008,
    decodeIntegerRow 16 3 1 18258060]

def outerABC : Matrix (LeftIndex 1 4 5) (RightIndex 5 1 4) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 1 4 5 r) []).getD (rightPosition 5 1 4 s) 0

theorem outerABC_eq : outerRightZ 5 1 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 1 5 4) (LeftIndex 1 5 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocBCA

theorem assocBAC_eq : associatorZ 1 5 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocBCA_eq

def innerABC : Matrix (LeftIndex 1 5 4) (LeftIndex 5 1 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 1 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 4 1) (RightIndex 5 1 4) ℤ :=
  (show Matrix (Fin 1 × Fin 4 × Fin 4) (Fin 1 × Fin 4 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 1 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7521688,
    decodeIntegerRow 16 3 1 18258116,
    decodeIntegerRow 16 3 1 27863528,
    decodeIntegerRow 16 3 1 36232156,
    decodeIntegerRow 16 3 1 6473404,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 24792872,
    decodeIntegerRow 16 3 1 7522684,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 27859044]

def inverseACB : Matrix (LeftIndex 5 4 1) (RightIndex 5 4 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 4 1 r) []).getD (rightPosition 5 4 1 s) 0

theorem inverseACB_eq : associatorInverseZ 5 4 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 5 1) (LeftIndex 5 4 1) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 4 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 1 4 5) (LeftIndex 1 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocBAC

theorem assocBCA_eq : associatorZ 1 4 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms415.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 1 4 5) (RightIndex 1 5 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 5 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 4 5 1) (LeftIndex 4 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.assocABC

theorem assocCAB_eq : associatorZ 4 5 1 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms451.assocABC_eq

def outerLeftABC : Matrix (RightIndex 4 5 1) (LeftIndex 5 1 4) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 1 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms514
