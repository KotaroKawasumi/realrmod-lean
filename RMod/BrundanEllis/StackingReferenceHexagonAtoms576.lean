import RMod.BrundanEllis.StackingReferenceHexagonAtoms567
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507]

def assocABC : Matrix (RightIndex 5 7 6) (LeftIndex 5 7 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 7 6 r) []).getD (leftPosition 5 7 6 s) 0

theorem assocABC_eq : associatorZ 5 7 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

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

def outerABC : Matrix (LeftIndex 7 6 5) (RightIndex 5 7 6) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 7 6 5 r) []).getD (rightPosition 5 7 6 s) 0

theorem outerABC_eq : outerRightZ 5 7 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 5 6) (LeftIndex 7 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocCAB

theorem assocBAC_eq : associatorZ 7 5 6 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 5 6) (LeftIndex 5 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.innerACB

theorem innerABC_eq : innerLeftZ 5 7 6 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.innerACB_eq

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18334688,
    decodeIntegerRow 16 3 1 35340820,
    decodeIntegerRow 16 3 1 36403720,
    decodeIntegerRow 16 3 1 15146096,
    decodeIntegerRow 16 3 1 21604360,
    decodeIntegerRow 16 3 1 21340624,
    decodeIntegerRow 16 3 1 21694432,
    decodeIntegerRow 16 3 1 21486100,
    decodeIntegerRow 16 3 1 21708040,
    decodeIntegerRow 16 3 1 21599824,
    decodeIntegerRow 16 3 1 21564832,
    decodeIntegerRow 16 3 1 21693460,
    decodeIntegerRow 16 3 1 7705888,
    decodeIntegerRow 16 3 1 18334740,
    decodeIntegerRow 16 3 1 27900680,
    decodeIntegerRow 16 3 1 36403696]

def innerRightABC : Matrix (RightIndex 5 6 7) (RightIndex 5 7 6) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 5 6 7 r) []).getD (rightPosition 5 7 6 s) 0

theorem innerRightABC_eq : innerRightZ 5 7 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547]

def inverseACB : Matrix (LeftIndex 5 6 7) (RightIndex 5 6 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 6 7 r) []).getD (rightPosition 5 6 7 s) 0

theorem inverseACB_eq : associatorInverseZ 5 6 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 5 7) (LeftIndex 5 6 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.innerABC

theorem innerACB_eq : innerLeftZ 5 6 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 7877464,
    decodeIntegerRow 16 3 1 18371784,
    decodeIntegerRow 16 3 1 27824052,
    decodeIntegerRow 16 3 1 36219508,
    decodeIntegerRow 16 3 1 15065256,
    decodeIntegerRow 16 3 1 36586936,
    decodeIntegerRow 16 3 1 7536268,
    decodeIntegerRow 16 3 1 24753612,
    decodeIntegerRow 16 3 1 15069416,
    decodeIntegerRow 16 3 1 36587896,
    decodeIntegerRow 16 3 1 7534348,
    decodeIntegerRow 16 3 1 24749132,
    decodeIntegerRow 16 3 1 7875496,
    decodeIntegerRow 16 3 1 18376376,
    decodeIntegerRow 16 3 1 27819788,
    decodeIntegerRow 16 3 1 36220492]

def assocBCA : Matrix (RightIndex 7 6 5) (LeftIndex 7 6 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 6 5 r) []).getD (leftPosition 7 6 5 s) 0

theorem assocBCA_eq : associatorZ 7 6 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 6 5) (RightIndex 7 5 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 5 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 6 5 7) (LeftIndex 6 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBAC

theorem assocCAB_eq : associatorZ 6 5 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms567.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 6 5 7) (LeftIndex 5 7 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 7 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms576
