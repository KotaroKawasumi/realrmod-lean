import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows70
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows71
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows72
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows73
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows74
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows75
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows76
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows77

/-! Intermediate matrices assembled from independently compiled label rows. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def middleRows (kind b c : ℕ) : List (List ℤ) :=
  match b with
  | 0 => HexagonMiddle7.rowsB0 kind c
  | 1 => HexagonMiddle7.rowsB1 kind c
  | 2 => HexagonMiddle7.rowsB2 kind c
  | 3 => HexagonMiddle7.rowsB3 kind c
  | 4 => HexagonMiddle7.rowsB4 kind c
  | 5 => HexagonMiddle7.rowsB5 kind c
  | 6 => HexagonMiddle7.rowsB6 kind c
  | 7 => HexagonMiddle7.rowsB7 kind c
  | _ => []

def left0Middle7 (b c : ZMod 8) : Matrix (LeftIndex b c 7) (LeftIndex 7 b c) ℤ :=
  fun r s => ((middleRows 0 b.val c.val).getD (leftPosition b c 7 r) []).getD (leftPosition 7 b c s) 0

def left1Middle7 (b c : ZMod 8) : Matrix (RightIndex b 7 c) (LeftIndex 7 b c) ℤ :=
  fun r s => ((middleRows 1 b.val c.val).getD (rightPosition b 7 c r) []).getD (leftPosition 7 b c s) 0

def right0Middle7 (b c : ZMod 8) : Matrix (RightIndex 7 c b) (LeftIndex 7 b c) ℤ :=
  fun r s => ((middleRows 2 b.val c.val).getD (rightPosition 7 c b r) []).getD (leftPosition 7 b c s) 0

def right1Middle7 (b c : ZMod 8) : Matrix (LeftIndex 7 c b) (LeftIndex 7 b c) ℤ :=
  fun r s => ((middleRows 3 b.val c.val).getD (leftPosition 7 c b r) []).getD (leftPosition 7 b c s) 0

def right2Middle7 (b c : ZMod 8) : Matrix (LeftIndex c 7 b) (LeftIndex 7 b c) ℤ :=
  fun r s => ((middleRows 4 b.val c.val).getD (leftPosition c 7 b r) []).getD (leftPosition 7 b c s) 0

end RMod.BrundanEllis.Stacking.ReferenceCommutor
