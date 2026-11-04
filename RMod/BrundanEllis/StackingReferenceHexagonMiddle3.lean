import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows30
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows31
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows32
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows33
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows34
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows35
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows36
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows37

/-! Intermediate matrices assembled from independently compiled label rows. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def middleRows (kind b c : ℕ) : List (List ℤ) :=
  match b with
  | 0 => HexagonMiddle3.rowsB0 kind c
  | 1 => HexagonMiddle3.rowsB1 kind c
  | 2 => HexagonMiddle3.rowsB2 kind c
  | 3 => HexagonMiddle3.rowsB3 kind c
  | 4 => HexagonMiddle3.rowsB4 kind c
  | 5 => HexagonMiddle3.rowsB5 kind c
  | 6 => HexagonMiddle3.rowsB6 kind c
  | 7 => HexagonMiddle3.rowsB7 kind c
  | _ => []

def left0Middle3 (b c : ZMod 8) : Matrix (LeftIndex b c 3) (LeftIndex 3 b c) ℤ :=
  fun r s => ((middleRows 0 b.val c.val).getD (leftPosition b c 3 r) []).getD (leftPosition 3 b c s) 0

def left1Middle3 (b c : ZMod 8) : Matrix (RightIndex b 3 c) (LeftIndex 3 b c) ℤ :=
  fun r s => ((middleRows 1 b.val c.val).getD (rightPosition b 3 c r) []).getD (leftPosition 3 b c s) 0

def right0Middle3 (b c : ZMod 8) : Matrix (RightIndex 3 c b) (LeftIndex 3 b c) ℤ :=
  fun r s => ((middleRows 2 b.val c.val).getD (rightPosition 3 c b r) []).getD (leftPosition 3 b c s) 0

def right1Middle3 (b c : ZMod 8) : Matrix (LeftIndex 3 c b) (LeftIndex 3 b c) ℤ :=
  fun r s => ((middleRows 3 b.val c.val).getD (leftPosition 3 c b r) []).getD (leftPosition 3 b c s) 0

def right2Middle3 (b c : ZMod 8) : Matrix (LeftIndex c 3 b) (LeftIndex 3 b c) ℤ :=
  fun r s => ((middleRows 4 b.val c.val).getD (leftPosition c 3 b r) []).getD (leftPosition 3 b c s) 0

end RMod.BrundanEllis.Stacking.ReferenceCommutor
