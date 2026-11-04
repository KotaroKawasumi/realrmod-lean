import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows60
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows61
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows62
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows63
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows64
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows65
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows66
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows67

/-! Intermediate matrices assembled from independently compiled label rows. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def middleRows (kind b c : ℕ) : List (List ℤ) :=
  match b with
  | 0 => HexagonMiddle6.rowsB0 kind c
  | 1 => HexagonMiddle6.rowsB1 kind c
  | 2 => HexagonMiddle6.rowsB2 kind c
  | 3 => HexagonMiddle6.rowsB3 kind c
  | 4 => HexagonMiddle6.rowsB4 kind c
  | 5 => HexagonMiddle6.rowsB5 kind c
  | 6 => HexagonMiddle6.rowsB6 kind c
  | 7 => HexagonMiddle6.rowsB7 kind c
  | _ => []

def left0Middle6 (b c : ZMod 8) : Matrix (LeftIndex b c 6) (LeftIndex 6 b c) ℤ :=
  fun r s => ((middleRows 0 b.val c.val).getD (leftPosition b c 6 r) []).getD (leftPosition 6 b c s) 0

def left1Middle6 (b c : ZMod 8) : Matrix (RightIndex b 6 c) (LeftIndex 6 b c) ℤ :=
  fun r s => ((middleRows 1 b.val c.val).getD (rightPosition b 6 c r) []).getD (leftPosition 6 b c s) 0

def right0Middle6 (b c : ZMod 8) : Matrix (RightIndex 6 c b) (LeftIndex 6 b c) ℤ :=
  fun r s => ((middleRows 2 b.val c.val).getD (rightPosition 6 c b r) []).getD (leftPosition 6 b c s) 0

def right1Middle6 (b c : ZMod 8) : Matrix (LeftIndex 6 c b) (LeftIndex 6 b c) ℤ :=
  fun r s => ((middleRows 3 b.val c.val).getD (leftPosition 6 c b r) []).getD (leftPosition 6 b c s) 0

def right2Middle6 (b c : ZMod 8) : Matrix (LeftIndex c 6 b) (LeftIndex 6 b c) ℤ :=
  fun r s => ((middleRows 4 b.val c.val).getD (leftPosition c 6 b r) []).getD (leftPosition 6 b c s) 0

end RMod.BrundanEllis.Stacking.ReferenceCommutor
