import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows50
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows51
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows52
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows53
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows54
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows55
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows56
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows57

/-! Intermediate matrices assembled from independently compiled label rows. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def middleRows (kind b c : ℕ) : List (List ℤ) :=
  match b with
  | 0 => HexagonMiddle5.rowsB0 kind c
  | 1 => HexagonMiddle5.rowsB1 kind c
  | 2 => HexagonMiddle5.rowsB2 kind c
  | 3 => HexagonMiddle5.rowsB3 kind c
  | 4 => HexagonMiddle5.rowsB4 kind c
  | 5 => HexagonMiddle5.rowsB5 kind c
  | 6 => HexagonMiddle5.rowsB6 kind c
  | 7 => HexagonMiddle5.rowsB7 kind c
  | _ => []

def left0Middle5 (b c : ZMod 8) : Matrix (LeftIndex b c 5) (LeftIndex 5 b c) ℤ :=
  fun r s => ((middleRows 0 b.val c.val).getD (leftPosition b c 5 r) []).getD (leftPosition 5 b c s) 0

def left1Middle5 (b c : ZMod 8) : Matrix (RightIndex b 5 c) (LeftIndex 5 b c) ℤ :=
  fun r s => ((middleRows 1 b.val c.val).getD (rightPosition b 5 c r) []).getD (leftPosition 5 b c s) 0

def right0Middle5 (b c : ZMod 8) : Matrix (RightIndex 5 c b) (LeftIndex 5 b c) ℤ :=
  fun r s => ((middleRows 2 b.val c.val).getD (rightPosition 5 c b r) []).getD (leftPosition 5 b c s) 0

def right1Middle5 (b c : ZMod 8) : Matrix (LeftIndex 5 c b) (LeftIndex 5 b c) ℤ :=
  fun r s => ((middleRows 3 b.val c.val).getD (leftPosition 5 c b r) []).getD (leftPosition 5 b c s) 0

def right2Middle5 (b c : ZMod 8) : Matrix (LeftIndex c 5 b) (LeftIndex 5 b c) ℤ :=
  fun r s => ((middleRows 4 b.val c.val).getD (leftPosition c 5 b r) []).getD (leftPosition 5 b c s) 0

end RMod.BrundanEllis.Stacking.ReferenceCommutor
