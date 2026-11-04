import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows40
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows41
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows42
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows43
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows44
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows45
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows46
import RMod.BrundanEllis.StackingReferenceHexagonMiddleRows47

/-! Intermediate matrices assembled from independently compiled label rows. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def middleRows (kind b c : ℕ) : List (List ℤ) :=
  match b with
  | 0 => HexagonMiddle4.rowsB0 kind c
  | 1 => HexagonMiddle4.rowsB1 kind c
  | 2 => HexagonMiddle4.rowsB2 kind c
  | 3 => HexagonMiddle4.rowsB3 kind c
  | 4 => HexagonMiddle4.rowsB4 kind c
  | 5 => HexagonMiddle4.rowsB5 kind c
  | 6 => HexagonMiddle4.rowsB6 kind c
  | 7 => HexagonMiddle4.rowsB7 kind c
  | _ => []

def left0Middle4 (b c : ZMod 8) : Matrix (LeftIndex b c 4) (LeftIndex 4 b c) ℤ :=
  fun r s => ((middleRows 0 b.val c.val).getD (leftPosition b c 4 r) []).getD (leftPosition 4 b c s) 0

def left1Middle4 (b c : ZMod 8) : Matrix (RightIndex b 4 c) (LeftIndex 4 b c) ℤ :=
  fun r s => ((middleRows 1 b.val c.val).getD (rightPosition b 4 c r) []).getD (leftPosition 4 b c s) 0

def right0Middle4 (b c : ZMod 8) : Matrix (RightIndex 4 c b) (LeftIndex 4 b c) ℤ :=
  fun r s => ((middleRows 2 b.val c.val).getD (rightPosition 4 c b r) []).getD (leftPosition 4 b c s) 0

def right1Middle4 (b c : ZMod 8) : Matrix (LeftIndex 4 c b) (LeftIndex 4 b c) ℤ :=
  fun r s => ((middleRows 3 b.val c.val).getD (leftPosition 4 c b r) []).getD (leftPosition 4 b c s) 0

def right2Middle4 (b c : ZMod 8) : Matrix (LeftIndex c 4 b) (LeftIndex 4 b c) ℤ :=
  fun r s => ((middleRows 4 b.val c.val).getD (leftPosition c 4 b r) []).getD (leftPosition 4 b c s) 0

end RMod.BrundanEllis.Stacking.ReferenceCommutor
