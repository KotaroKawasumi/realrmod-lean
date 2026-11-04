import Superfusion.RMod.Constructive.FusionTableData
import Superfusion.RMod.Constructive.CoordinateCategoryLaws
import Superfusion.GaugeChi.TripleCerts.FuseShadows

/-!
# Finite laws of the raw fusion table

The raw dispatcher reuses the existing `IsFuseZ` certificates.  Unit,
grading, and multiplicativity are transported from the resulting semantic
`realFuse` comparison and its graded algebra-equivalence laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT.FusionTableLaws

open RModCoordinate
open RModCoordinate.FusionTable
open GaugeChi

/-! ## Bridge to the existing certified shadows -/

/-- Replacing a frozen integer shadow by the extensionally equal total
dispatcher preserves its semantic fusion certificate. -/
private theorem entry_isFuseZ_of_eq (a b : ZMod 8)
    (AZ : Fin (((Superfusion.realSize a b).1 + (Superfusion.realSize a b).2) *
        ((Superfusion.realSize a b).1 + (Superfusion.realSize a b).2) *
          realRepDim (a + b).val) →
      Fin (realRepDim a.val * realRepDim b.val) → ℤ)
    (hAZ : IsFuseZ a b AZ)
    (hentry : ∀ f col,
      FusionTable.entry a b f.val col.val = AZ f col) :
    IsFuseZ a b (fun f col => FusionTable.entry a b f.val col.val) := by
  intro f col
  change realFuseMatrix a b f col =
    ((FusionTable.entry a b f.val col.val : ℤ) : ℝ)
  rw [hentry f col]
  exact hAZ f col

/-- The dispatcher certificate at the frozen label pair `(0,0)`. -/
private theorem entry_isFuseZ_0_0 :
    IsFuseZ (0 : ZMod 8) (0 : ZMod 8)
      (fun f col => FusionTable.entry 0 0 f.val col.val) := by
  apply entry_isFuseZ_of_eq 0 0 GaugeChi.TripleCerts.fuseZ_0_0
    GaugeChi.TripleCerts.hfuseZ_0_0
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_0_0 f col

/-- The dispatcher certificate at the frozen label pair `(0,1)`. -/
private theorem entry_isFuseZ_0_1 :
    IsFuseZ (0 : ZMod 8) (1 : ZMod 8)
      (fun f col => FusionTable.entry 0 1 f.val col.val) := by
  apply entry_isFuseZ_of_eq 0 1 GaugeChi.TripleCerts.fuseZ_0_1
    GaugeChi.TripleCerts.hfuseZ_0_1
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_0_1 f col

/-- The dispatcher certificate at the frozen label pair `(0,2)`. -/
private theorem entry_isFuseZ_0_2 :
    IsFuseZ (0 : ZMod 8) (2 : ZMod 8)
      (fun f col => FusionTable.entry 0 2 f.val col.val) := by
  apply entry_isFuseZ_of_eq 0 2 GaugeChi.TripleCerts.fuseZ_0_2
    GaugeChi.TripleCerts.hfuseZ_0_2
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_0_2 f col

/-- The dispatcher certificate at the frozen label pair `(0,3)`. -/
private theorem entry_isFuseZ_0_3 :
    IsFuseZ (0 : ZMod 8) (3 : ZMod 8)
      (fun f col => FusionTable.entry 0 3 f.val col.val) := by
  apply entry_isFuseZ_of_eq 0 3 GaugeChi.TripleCerts.fuseZ_0_3
    GaugeChi.TripleCerts.hfuseZ_0_3
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_0_3 f col

/-- The dispatcher certificate at the frozen label pair `(0,4)`. -/
private theorem entry_isFuseZ_0_4 :
    IsFuseZ (0 : ZMod 8) (4 : ZMod 8)
      (fun f col => FusionTable.entry 0 4 f.val col.val) := by
  apply entry_isFuseZ_of_eq 0 4 GaugeChi.TripleCerts.fuseZ_0_4
    GaugeChi.TripleCerts.hfuseZ_0_4
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_0_4 f col

/-- The dispatcher certificate at the frozen label pair `(0,5)`. -/
private theorem entry_isFuseZ_0_5 :
    IsFuseZ (0 : ZMod 8) (5 : ZMod 8)
      (fun f col => FusionTable.entry 0 5 f.val col.val) := by
  apply entry_isFuseZ_of_eq 0 5 GaugeChi.TripleCerts.fuseZ_0_5
    GaugeChi.TripleCerts.hfuseZ_0_5
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_0_5 f col

/-- The dispatcher certificate at the frozen label pair `(0,6)`. -/
private theorem entry_isFuseZ_0_6 :
    IsFuseZ (0 : ZMod 8) (6 : ZMod 8)
      (fun f col => FusionTable.entry 0 6 f.val col.val) := by
  apply entry_isFuseZ_of_eq 0 6 GaugeChi.TripleCerts.fuseZ_0_6
    GaugeChi.TripleCerts.hfuseZ_0_6
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_0_6 f col

/-- The dispatcher certificate at the frozen label pair `(0,7)`. -/
private theorem entry_isFuseZ_0_7 :
    IsFuseZ (0 : ZMod 8) (7 : ZMod 8)
      (fun f col => FusionTable.entry 0 7 f.val col.val) := by
  apply entry_isFuseZ_of_eq 0 7 GaugeChi.TripleCerts.fuseZ_0_7
    GaugeChi.TripleCerts.hfuseZ_0_7
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_0_7 f col

/-- The dispatcher certificate at the frozen label pair `(1,0)`. -/
private theorem entry_isFuseZ_1_0 :
    IsFuseZ (1 : ZMod 8) (0 : ZMod 8)
      (fun f col => FusionTable.entry 1 0 f.val col.val) := by
  apply entry_isFuseZ_of_eq 1 0 GaugeChi.TripleCerts.fuseZ_1_0
    GaugeChi.TripleCerts.hfuseZ_1_0
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_1_0 f col

/-- The dispatcher certificate at the frozen label pair `(1,1)`. -/
private theorem entry_isFuseZ_1_1 :
    IsFuseZ (1 : ZMod 8) (1 : ZMod 8)
      (fun f col => FusionTable.entry 1 1 f.val col.val) := by
  apply entry_isFuseZ_of_eq 1 1 GaugeChi.TripleCerts.fuseZ_1_1
    GaugeChi.TripleCerts.hfuseZ_1_1
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_1_1 f col

/-- The dispatcher certificate at the frozen label pair `(1,2)`. -/
private theorem entry_isFuseZ_1_2 :
    IsFuseZ (1 : ZMod 8) (2 : ZMod 8)
      (fun f col => FusionTable.entry 1 2 f.val col.val) := by
  apply entry_isFuseZ_of_eq 1 2 GaugeChi.TripleCerts.fuseZ_1_2
    GaugeChi.TripleCerts.hfuseZ_1_2
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_1_2 f col

/-- The dispatcher certificate at the frozen label pair `(1,3)`. -/
private theorem entry_isFuseZ_1_3 :
    IsFuseZ (1 : ZMod 8) (3 : ZMod 8)
      (fun f col => FusionTable.entry 1 3 f.val col.val) := by
  apply entry_isFuseZ_of_eq 1 3 GaugeChi.TripleCerts.fuseZ_1_3
    GaugeChi.TripleCerts.hfuseZ_1_3
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_1_3 f col

/-- The dispatcher certificate at the frozen label pair `(1,4)`. -/
private theorem entry_isFuseZ_1_4 :
    IsFuseZ (1 : ZMod 8) (4 : ZMod 8)
      (fun f col => FusionTable.entry 1 4 f.val col.val) := by
  apply entry_isFuseZ_of_eq 1 4 GaugeChi.TripleCerts.fuseZ_1_4
    GaugeChi.TripleCerts.hfuseZ_1_4
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_1_4 f col

/-- The dispatcher certificate at the frozen label pair `(1,5)`. -/
private theorem entry_isFuseZ_1_5 :
    IsFuseZ (1 : ZMod 8) (5 : ZMod 8)
      (fun f col => FusionTable.entry 1 5 f.val col.val) := by
  apply entry_isFuseZ_of_eq 1 5 GaugeChi.TripleCerts.fuseZ_1_5
    GaugeChi.TripleCerts.hfuseZ_1_5
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_1_5 f col

/-- The dispatcher certificate at the frozen label pair `(1,6)`. -/
private theorem entry_isFuseZ_1_6 :
    IsFuseZ (1 : ZMod 8) (6 : ZMod 8)
      (fun f col => FusionTable.entry 1 6 f.val col.val) := by
  apply entry_isFuseZ_of_eq 1 6 GaugeChi.TripleCerts.fuseZ_1_6
    GaugeChi.TripleCerts.hfuseZ_1_6
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_1_6 f col

/-- The dispatcher certificate at the frozen label pair `(1,7)`. -/
private theorem entry_isFuseZ_1_7 :
    IsFuseZ (1 : ZMod 8) (7 : ZMod 8)
      (fun f col => FusionTable.entry 1 7 f.val col.val) := by
  apply entry_isFuseZ_of_eq 1 7 GaugeChi.TripleCerts.fuseZ_1_7
    GaugeChi.TripleCerts.hfuseZ_1_7
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_1_7 f col

/-- The dispatcher certificate at the frozen label pair `(2,0)`. -/
private theorem entry_isFuseZ_2_0 :
    IsFuseZ (2 : ZMod 8) (0 : ZMod 8)
      (fun f col => FusionTable.entry 2 0 f.val col.val) := by
  apply entry_isFuseZ_of_eq 2 0 GaugeChi.TripleCerts.fuseZ_2_0
    GaugeChi.TripleCerts.hfuseZ_2_0
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_2_0 f col

/-- The dispatcher certificate at the frozen label pair `(2,1)`. -/
private theorem entry_isFuseZ_2_1 :
    IsFuseZ (2 : ZMod 8) (1 : ZMod 8)
      (fun f col => FusionTable.entry 2 1 f.val col.val) := by
  apply entry_isFuseZ_of_eq 2 1 GaugeChi.TripleCerts.fuseZ_2_1
    GaugeChi.TripleCerts.hfuseZ_2_1
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_2_1 f col

/-- The dispatcher certificate at the frozen label pair `(2,2)`. -/
private theorem entry_isFuseZ_2_2 :
    IsFuseZ (2 : ZMod 8) (2 : ZMod 8)
      (fun f col => FusionTable.entry 2 2 f.val col.val) := by
  apply entry_isFuseZ_of_eq 2 2 GaugeChi.TripleCerts.fuseZ_2_2
    GaugeChi.TripleCerts.hfuseZ_2_2
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_2_2 f col

/-- The dispatcher certificate at the frozen label pair `(2,3)`. -/
private theorem entry_isFuseZ_2_3 :
    IsFuseZ (2 : ZMod 8) (3 : ZMod 8)
      (fun f col => FusionTable.entry 2 3 f.val col.val) := by
  apply entry_isFuseZ_of_eq 2 3 GaugeChi.TripleCerts.fuseZ_2_3
    GaugeChi.TripleCerts.hfuseZ_2_3
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_2_3 f col

/-- The dispatcher certificate at the frozen label pair `(2,4)`. -/
private theorem entry_isFuseZ_2_4 :
    IsFuseZ (2 : ZMod 8) (4 : ZMod 8)
      (fun f col => FusionTable.entry 2 4 f.val col.val) := by
  apply entry_isFuseZ_of_eq 2 4 GaugeChi.TripleCerts.fuseZ_2_4
    GaugeChi.TripleCerts.hfuseZ_2_4
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_2_4 f col

/-- The dispatcher certificate at the frozen label pair `(2,5)`. -/
private theorem entry_isFuseZ_2_5 :
    IsFuseZ (2 : ZMod 8) (5 : ZMod 8)
      (fun f col => FusionTable.entry 2 5 f.val col.val) := by
  apply entry_isFuseZ_of_eq 2 5 GaugeChi.TripleCerts.fuseZ_2_5
    GaugeChi.TripleCerts.hfuseZ_2_5
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_2_5 f col

/-- The dispatcher certificate at the frozen label pair `(2,6)`. -/
private theorem entry_isFuseZ_2_6 :
    IsFuseZ (2 : ZMod 8) (6 : ZMod 8)
      (fun f col => FusionTable.entry 2 6 f.val col.val) := by
  apply entry_isFuseZ_of_eq 2 6 GaugeChi.TripleCerts.fuseZ_2_6
    GaugeChi.TripleCerts.hfuseZ_2_6
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_2_6 f col

/-- The dispatcher certificate at the frozen label pair `(2,7)`. -/
private theorem entry_isFuseZ_2_7 :
    IsFuseZ (2 : ZMod 8) (7 : ZMod 8)
      (fun f col => FusionTable.entry 2 7 f.val col.val) := by
  apply entry_isFuseZ_of_eq 2 7 GaugeChi.TripleCerts.fuseZ_2_7
    GaugeChi.TripleCerts.hfuseZ_2_7
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_2_7 f col

/-- The dispatcher certificate at the frozen label pair `(3,0)`. -/
private theorem entry_isFuseZ_3_0 :
    IsFuseZ (3 : ZMod 8) (0 : ZMod 8)
      (fun f col => FusionTable.entry 3 0 f.val col.val) := by
  apply entry_isFuseZ_of_eq 3 0 GaugeChi.TripleCerts.fuseZ_3_0
    GaugeChi.TripleCerts.hfuseZ_3_0
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_3_0 f col

/-- The dispatcher certificate at the frozen label pair `(3,1)`. -/
private theorem entry_isFuseZ_3_1 :
    IsFuseZ (3 : ZMod 8) (1 : ZMod 8)
      (fun f col => FusionTable.entry 3 1 f.val col.val) := by
  apply entry_isFuseZ_of_eq 3 1 GaugeChi.TripleCerts.fuseZ_3_1
    GaugeChi.TripleCerts.hfuseZ_3_1
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_3_1 f col

/-- The dispatcher certificate at the frozen label pair `(3,2)`. -/
private theorem entry_isFuseZ_3_2 :
    IsFuseZ (3 : ZMod 8) (2 : ZMod 8)
      (fun f col => FusionTable.entry 3 2 f.val col.val) := by
  apply entry_isFuseZ_of_eq 3 2 GaugeChi.TripleCerts.fuseZ_3_2
    GaugeChi.TripleCerts.hfuseZ_3_2
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_3_2 f col

/-- The dispatcher certificate at the frozen label pair `(3,3)`. -/
private theorem entry_isFuseZ_3_3 :
    IsFuseZ (3 : ZMod 8) (3 : ZMod 8)
      (fun f col => FusionTable.entry 3 3 f.val col.val) := by
  apply entry_isFuseZ_of_eq 3 3 GaugeChi.TripleCerts.fuseZ_3_3
    GaugeChi.TripleCerts.hfuseZ_3_3
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_3_3 f col

/-- The dispatcher certificate at the frozen label pair `(3,4)`. -/
private theorem entry_isFuseZ_3_4 :
    IsFuseZ (3 : ZMod 8) (4 : ZMod 8)
      (fun f col => FusionTable.entry 3 4 f.val col.val) := by
  apply entry_isFuseZ_of_eq 3 4 GaugeChi.TripleCerts.fuseZ_3_4
    GaugeChi.TripleCerts.hfuseZ_3_4
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_3_4 f col

/-- The dispatcher certificate at the frozen label pair `(3,5)`. -/
private theorem entry_isFuseZ_3_5 :
    IsFuseZ (3 : ZMod 8) (5 : ZMod 8)
      (fun f col => FusionTable.entry 3 5 f.val col.val) := by
  apply entry_isFuseZ_of_eq 3 5 GaugeChi.TripleCerts.fuseZ_3_5
    GaugeChi.TripleCerts.hfuseZ_3_5
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_3_5 f col

/-- The dispatcher certificate at the frozen label pair `(3,6)`. -/
private theorem entry_isFuseZ_3_6 :
    IsFuseZ (3 : ZMod 8) (6 : ZMod 8)
      (fun f col => FusionTable.entry 3 6 f.val col.val) := by
  apply entry_isFuseZ_of_eq 3 6 GaugeChi.TripleCerts.fuseZ_3_6
    GaugeChi.TripleCerts.hfuseZ_3_6
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_3_6 f col

/-- The dispatcher certificate at the frozen label pair `(3,7)`. -/
private theorem entry_isFuseZ_3_7 :
    IsFuseZ (3 : ZMod 8) (7 : ZMod 8)
      (fun f col => FusionTable.entry 3 7 f.val col.val) := by
  apply entry_isFuseZ_of_eq 3 7 GaugeChi.TripleCerts.fuseZ_3_7
    GaugeChi.TripleCerts.hfuseZ_3_7
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_3_7 f col

/-- The dispatcher certificate at the frozen label pair `(4,0)`. -/
private theorem entry_isFuseZ_4_0 :
    IsFuseZ (4 : ZMod 8) (0 : ZMod 8)
      (fun f col => FusionTable.entry 4 0 f.val col.val) := by
  apply entry_isFuseZ_of_eq 4 0 GaugeChi.TripleCerts.fuseZ_4_0
    GaugeChi.TripleCerts.hfuseZ_4_0
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_4_0 f col

/-- The dispatcher certificate at the frozen label pair `(4,1)`. -/
private theorem entry_isFuseZ_4_1 :
    IsFuseZ (4 : ZMod 8) (1 : ZMod 8)
      (fun f col => FusionTable.entry 4 1 f.val col.val) := by
  apply entry_isFuseZ_of_eq 4 1 GaugeChi.TripleCerts.fuseZ_4_1
    GaugeChi.TripleCerts.hfuseZ_4_1
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_4_1 f col

/-- The dispatcher certificate at the frozen label pair `(4,2)`. -/
private theorem entry_isFuseZ_4_2 :
    IsFuseZ (4 : ZMod 8) (2 : ZMod 8)
      (fun f col => FusionTable.entry 4 2 f.val col.val) := by
  apply entry_isFuseZ_of_eq 4 2 GaugeChi.TripleCerts.fuseZ_4_2
    GaugeChi.TripleCerts.hfuseZ_4_2
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_4_2 f col

/-- The dispatcher certificate at the frozen label pair `(4,3)`. -/
private theorem entry_isFuseZ_4_3 :
    IsFuseZ (4 : ZMod 8) (3 : ZMod 8)
      (fun f col => FusionTable.entry 4 3 f.val col.val) := by
  apply entry_isFuseZ_of_eq 4 3 GaugeChi.TripleCerts.fuseZ_4_3
    GaugeChi.TripleCerts.hfuseZ_4_3
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_4_3 f col

/-- The dispatcher certificate at the frozen label pair `(4,4)`. -/
private theorem entry_isFuseZ_4_4 :
    IsFuseZ (4 : ZMod 8) (4 : ZMod 8)
      (fun f col => FusionTable.entry 4 4 f.val col.val) := by
  apply entry_isFuseZ_of_eq 4 4 GaugeChi.TripleCerts.fuseZ_4_4
    GaugeChi.TripleCerts.hfuseZ_4_4
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_4_4 f col

/-- The dispatcher certificate at the frozen label pair `(4,5)`. -/
private theorem entry_isFuseZ_4_5 :
    IsFuseZ (4 : ZMod 8) (5 : ZMod 8)
      (fun f col => FusionTable.entry 4 5 f.val col.val) := by
  apply entry_isFuseZ_of_eq 4 5 GaugeChi.TripleCerts.fuseZ_4_5
    GaugeChi.TripleCerts.hfuseZ_4_5
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_4_5 f col

/-- The dispatcher certificate at the frozen label pair `(4,6)`. -/
private theorem entry_isFuseZ_4_6 :
    IsFuseZ (4 : ZMod 8) (6 : ZMod 8)
      (fun f col => FusionTable.entry 4 6 f.val col.val) := by
  apply entry_isFuseZ_of_eq 4 6 GaugeChi.TripleCerts.fuseZ_4_6
    GaugeChi.TripleCerts.hfuseZ_4_6
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_4_6 f col

/-- The dispatcher certificate at the frozen label pair `(4,7)`. -/
private theorem entry_isFuseZ_4_7 :
    IsFuseZ (4 : ZMod 8) (7 : ZMod 8)
      (fun f col => FusionTable.entry 4 7 f.val col.val) := by
  apply entry_isFuseZ_of_eq 4 7 GaugeChi.TripleCerts.fuseZ_4_7
    GaugeChi.TripleCerts.hfuseZ_4_7
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_4_7 f col

/-- The dispatcher certificate at the frozen label pair `(5,0)`. -/
private theorem entry_isFuseZ_5_0 :
    IsFuseZ (5 : ZMod 8) (0 : ZMod 8)
      (fun f col => FusionTable.entry 5 0 f.val col.val) := by
  apply entry_isFuseZ_of_eq 5 0 GaugeChi.TripleCerts.fuseZ_5_0
    GaugeChi.TripleCerts.hfuseZ_5_0
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_5_0 f col

/-- The dispatcher certificate at the frozen label pair `(5,1)`. -/
private theorem entry_isFuseZ_5_1 :
    IsFuseZ (5 : ZMod 8) (1 : ZMod 8)
      (fun f col => FusionTable.entry 5 1 f.val col.val) := by
  apply entry_isFuseZ_of_eq 5 1 GaugeChi.TripleCerts.fuseZ_5_1
    GaugeChi.TripleCerts.hfuseZ_5_1
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_5_1 f col

/-- The dispatcher certificate at the frozen label pair `(5,2)`. -/
private theorem entry_isFuseZ_5_2 :
    IsFuseZ (5 : ZMod 8) (2 : ZMod 8)
      (fun f col => FusionTable.entry 5 2 f.val col.val) := by
  apply entry_isFuseZ_of_eq 5 2 GaugeChi.TripleCerts.fuseZ_5_2
    GaugeChi.TripleCerts.hfuseZ_5_2
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_5_2 f col

/-- The dispatcher certificate at the frozen label pair `(5,3)`. -/
private theorem entry_isFuseZ_5_3 :
    IsFuseZ (5 : ZMod 8) (3 : ZMod 8)
      (fun f col => FusionTable.entry 5 3 f.val col.val) := by
  apply entry_isFuseZ_of_eq 5 3 GaugeChi.TripleCerts.fuseZ_5_3
    GaugeChi.TripleCerts.hfuseZ_5_3
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_5_3 f col

/-- The dispatcher certificate at the frozen label pair `(5,4)`. -/
private theorem entry_isFuseZ_5_4 :
    IsFuseZ (5 : ZMod 8) (4 : ZMod 8)
      (fun f col => FusionTable.entry 5 4 f.val col.val) := by
  apply entry_isFuseZ_of_eq 5 4 GaugeChi.TripleCerts.fuseZ_5_4
    GaugeChi.TripleCerts.hfuseZ_5_4
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_5_4 f col

/-- The dispatcher certificate at the frozen label pair `(5,5)`. -/
private theorem entry_isFuseZ_5_5 :
    IsFuseZ (5 : ZMod 8) (5 : ZMod 8)
      (fun f col => FusionTable.entry 5 5 f.val col.val) := by
  apply entry_isFuseZ_of_eq 5 5 GaugeChi.TripleCerts.fuseZ_5_5
    GaugeChi.TripleCerts.hfuseZ_5_5
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_5_5 f col

/-- The dispatcher certificate at the frozen label pair `(5,6)`. -/
private theorem entry_isFuseZ_5_6 :
    IsFuseZ (5 : ZMod 8) (6 : ZMod 8)
      (fun f col => FusionTable.entry 5 6 f.val col.val) := by
  apply entry_isFuseZ_of_eq 5 6 GaugeChi.TripleCerts.fuseZ_5_6
    GaugeChi.TripleCerts.hfuseZ_5_6
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_5_6 f col

/-- The dispatcher certificate at the frozen label pair `(5,7)`. -/
private theorem entry_isFuseZ_5_7 :
    IsFuseZ (5 : ZMod 8) (7 : ZMod 8)
      (fun f col => FusionTable.entry 5 7 f.val col.val) := by
  apply entry_isFuseZ_of_eq 5 7 GaugeChi.TripleCerts.fuseZ_5_7
    GaugeChi.TripleCerts.hfuseZ_5_7
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_5_7 f col

/-- The dispatcher certificate at the frozen label pair `(6,0)`. -/
private theorem entry_isFuseZ_6_0 :
    IsFuseZ (6 : ZMod 8) (0 : ZMod 8)
      (fun f col => FusionTable.entry 6 0 f.val col.val) := by
  apply entry_isFuseZ_of_eq 6 0 GaugeChi.TripleCerts.fuseZ_6_0
    GaugeChi.TripleCerts.hfuseZ_6_0
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_6_0 f col

/-- The dispatcher certificate at the frozen label pair `(6,1)`. -/
private theorem entry_isFuseZ_6_1 :
    IsFuseZ (6 : ZMod 8) (1 : ZMod 8)
      (fun f col => FusionTable.entry 6 1 f.val col.val) := by
  apply entry_isFuseZ_of_eq 6 1 GaugeChi.TripleCerts.fuseZ_6_1
    GaugeChi.TripleCerts.hfuseZ_6_1
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_6_1 f col

/-- The dispatcher certificate at the frozen label pair `(6,2)`. -/
private theorem entry_isFuseZ_6_2 :
    IsFuseZ (6 : ZMod 8) (2 : ZMod 8)
      (fun f col => FusionTable.entry 6 2 f.val col.val) := by
  apply entry_isFuseZ_of_eq 6 2 GaugeChi.TripleCerts.fuseZ_6_2
    GaugeChi.TripleCerts.hfuseZ_6_2
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_6_2 f col

/-- The dispatcher certificate at the frozen label pair `(6,3)`. -/
private theorem entry_isFuseZ_6_3 :
    IsFuseZ (6 : ZMod 8) (3 : ZMod 8)
      (fun f col => FusionTable.entry 6 3 f.val col.val) := by
  apply entry_isFuseZ_of_eq 6 3 GaugeChi.TripleCerts.fuseZ_6_3
    GaugeChi.TripleCerts.hfuseZ_6_3
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_6_3 f col

/-- The dispatcher certificate at the frozen label pair `(6,4)`. -/
private theorem entry_isFuseZ_6_4 :
    IsFuseZ (6 : ZMod 8) (4 : ZMod 8)
      (fun f col => FusionTable.entry 6 4 f.val col.val) := by
  apply entry_isFuseZ_of_eq 6 4 GaugeChi.TripleCerts.fuseZ_6_4
    GaugeChi.TripleCerts.hfuseZ_6_4
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_6_4 f col

/-- The dispatcher certificate at the frozen label pair `(6,5)`. -/
private theorem entry_isFuseZ_6_5 :
    IsFuseZ (6 : ZMod 8) (5 : ZMod 8)
      (fun f col => FusionTable.entry 6 5 f.val col.val) := by
  apply entry_isFuseZ_of_eq 6 5 GaugeChi.TripleCerts.fuseZ_6_5
    GaugeChi.TripleCerts.hfuseZ_6_5
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_6_5 f col

/-- The dispatcher certificate at the frozen label pair `(6,6)`. -/
private theorem entry_isFuseZ_6_6 :
    IsFuseZ (6 : ZMod 8) (6 : ZMod 8)
      (fun f col => FusionTable.entry 6 6 f.val col.val) := by
  apply entry_isFuseZ_of_eq 6 6 GaugeChi.TripleCerts.fuseZ_6_6
    GaugeChi.TripleCerts.hfuseZ_6_6
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_6_6 f col

/-- The dispatcher certificate at the frozen label pair `(6,7)`. -/
private theorem entry_isFuseZ_6_7 :
    IsFuseZ (6 : ZMod 8) (7 : ZMod 8)
      (fun f col => FusionTable.entry 6 7 f.val col.val) := by
  apply entry_isFuseZ_of_eq 6 7 GaugeChi.TripleCerts.fuseZ_6_7
    GaugeChi.TripleCerts.hfuseZ_6_7
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_6_7 f col

/-- The dispatcher certificate at the frozen label pair `(7,0)`. -/
private theorem entry_isFuseZ_7_0 :
    IsFuseZ (7 : ZMod 8) (0 : ZMod 8)
      (fun f col => FusionTable.entry 7 0 f.val col.val) := by
  apply entry_isFuseZ_of_eq 7 0 GaugeChi.TripleCerts.fuseZ_7_0
    GaugeChi.TripleCerts.hfuseZ_7_0
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_7_0 f col

/-- The dispatcher certificate at the frozen label pair `(7,1)`. -/
private theorem entry_isFuseZ_7_1 :
    IsFuseZ (7 : ZMod 8) (1 : ZMod 8)
      (fun f col => FusionTable.entry 7 1 f.val col.val) := by
  apply entry_isFuseZ_of_eq 7 1 GaugeChi.TripleCerts.fuseZ_7_1
    GaugeChi.TripleCerts.hfuseZ_7_1
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_7_1 f col

/-- The dispatcher certificate at the frozen label pair `(7,2)`. -/
private theorem entry_isFuseZ_7_2 :
    IsFuseZ (7 : ZMod 8) (2 : ZMod 8)
      (fun f col => FusionTable.entry 7 2 f.val col.val) := by
  apply entry_isFuseZ_of_eq 7 2 GaugeChi.TripleCerts.fuseZ_7_2
    GaugeChi.TripleCerts.hfuseZ_7_2
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_7_2 f col

/-- The dispatcher certificate at the frozen label pair `(7,3)`. -/
private theorem entry_isFuseZ_7_3 :
    IsFuseZ (7 : ZMod 8) (3 : ZMod 8)
      (fun f col => FusionTable.entry 7 3 f.val col.val) := by
  apply entry_isFuseZ_of_eq 7 3 GaugeChi.TripleCerts.fuseZ_7_3
    GaugeChi.TripleCerts.hfuseZ_7_3
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_7_3 f col

/-- The dispatcher certificate at the frozen label pair `(7,4)`. -/
private theorem entry_isFuseZ_7_4 :
    IsFuseZ (7 : ZMod 8) (4 : ZMod 8)
      (fun f col => FusionTable.entry 7 4 f.val col.val) := by
  apply entry_isFuseZ_of_eq 7 4 GaugeChi.TripleCerts.fuseZ_7_4
    GaugeChi.TripleCerts.hfuseZ_7_4
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_7_4 f col

/-- The dispatcher certificate at the frozen label pair `(7,5)`. -/
private theorem entry_isFuseZ_7_5 :
    IsFuseZ (7 : ZMod 8) (5 : ZMod 8)
      (fun f col => FusionTable.entry 7 5 f.val col.val) := by
  apply entry_isFuseZ_of_eq 7 5 GaugeChi.TripleCerts.fuseZ_7_5
    GaugeChi.TripleCerts.hfuseZ_7_5
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_7_5 f col

/-- The dispatcher certificate at the frozen label pair `(7,6)`. -/
private theorem entry_isFuseZ_7_6 :
    IsFuseZ (7 : ZMod 8) (6 : ZMod 8)
      (fun f col => FusionTable.entry 7 6 f.val col.val) := by
  apply entry_isFuseZ_of_eq 7 6 GaugeChi.TripleCerts.fuseZ_7_6
    GaugeChi.TripleCerts.hfuseZ_7_6
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_7_6 f col

/-- The dispatcher certificate at the frozen label pair `(7,7)`. -/
private theorem entry_isFuseZ_7_7 :
    IsFuseZ (7 : ZMod 8) (7 : ZMod 8)
      (fun f col => FusionTable.entry 7 7 f.val col.val) := by
  apply entry_isFuseZ_of_eq 7 7 GaugeChi.TripleCerts.fuseZ_7_7
    GaugeChi.TripleCerts.hfuseZ_7_7
  intro f col
  exact natTable2_apply GaugeChi.TripleCerts.fuseZ_7_7 f col

/-- The total constructive fusion dispatcher is exactly the integer shadow
of the semantic frozen fusion matrix at every pair of genuine labels. -/
theorem entry_isFuseZ (a b : ZMod 8) :
    IsFuseZ a b (fun f col => FusionTable.entry a b f.val col.val) := by
  fin_cases a
  · fin_cases b
    · exact entry_isFuseZ_0_0
    · exact entry_isFuseZ_0_1
    · exact entry_isFuseZ_0_2
    · exact entry_isFuseZ_0_3
    · exact entry_isFuseZ_0_4
    · exact entry_isFuseZ_0_5
    · exact entry_isFuseZ_0_6
    · exact entry_isFuseZ_0_7
  · fin_cases b
    · exact entry_isFuseZ_1_0
    · exact entry_isFuseZ_1_1
    · exact entry_isFuseZ_1_2
    · exact entry_isFuseZ_1_3
    · exact entry_isFuseZ_1_4
    · exact entry_isFuseZ_1_5
    · exact entry_isFuseZ_1_6
    · exact entry_isFuseZ_1_7
  · fin_cases b
    · exact entry_isFuseZ_2_0
    · exact entry_isFuseZ_2_1
    · exact entry_isFuseZ_2_2
    · exact entry_isFuseZ_2_3
    · exact entry_isFuseZ_2_4
    · exact entry_isFuseZ_2_5
    · exact entry_isFuseZ_2_6
    · exact entry_isFuseZ_2_7
  · fin_cases b
    · exact entry_isFuseZ_3_0
    · exact entry_isFuseZ_3_1
    · exact entry_isFuseZ_3_2
    · exact entry_isFuseZ_3_3
    · exact entry_isFuseZ_3_4
    · exact entry_isFuseZ_3_5
    · exact entry_isFuseZ_3_6
    · exact entry_isFuseZ_3_7
  · fin_cases b
    · exact entry_isFuseZ_4_0
    · exact entry_isFuseZ_4_1
    · exact entry_isFuseZ_4_2
    · exact entry_isFuseZ_4_3
    · exact entry_isFuseZ_4_4
    · exact entry_isFuseZ_4_5
    · exact entry_isFuseZ_4_6
    · exact entry_isFuseZ_4_7
  · fin_cases b
    · exact entry_isFuseZ_5_0
    · exact entry_isFuseZ_5_1
    · exact entry_isFuseZ_5_2
    · exact entry_isFuseZ_5_3
    · exact entry_isFuseZ_5_4
    · exact entry_isFuseZ_5_5
    · exact entry_isFuseZ_5_6
    · exact entry_isFuseZ_5_7
  · fin_cases b
    · exact entry_isFuseZ_6_0
    · exact entry_isFuseZ_6_1
    · exact entry_isFuseZ_6_2
    · exact entry_isFuseZ_6_3
    · exact entry_isFuseZ_6_4
    · exact entry_isFuseZ_6_5
    · exact entry_isFuseZ_6_6
    · exact entry_isFuseZ_6_7
  · fin_cases b
    · exact entry_isFuseZ_7_0
    · exact entry_isFuseZ_7_1
    · exact entry_isFuseZ_7_2
    · exact entry_isFuseZ_7_3
    · exact entry_isFuseZ_7_4
    · exact entry_isFuseZ_7_5
    · exact entry_isFuseZ_7_6
    · exact entry_isFuseZ_7_7

private theorem outputPosition_eq_fuseRow_val (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b)
    (g : Fin (realRepDim (a + b).val)) :
    RModCoordinate.FusionTable.outputPosition a b target source g =
      (fuseRow a b
        (RModCoordinate.FusionTable.frameIndex a b target)
        (RModCoordinate.FusionTable.frameIndex a b source) g).val := by
  rw [matrixSuperIndexEquiv_val]
  simp [RModCoordinate.FusionTable.outputPosition,
    RModCoordinate.FusionTable.frameIndex]

private theorem inputPosition_eq_fuseCol_val (a b : ZMod 8)
    (i : Fin (realRepDim a.val)) (j : Fin (realRepDim b.val)) :
    RModCoordinate.FusionTable.inputPosition a b i j =
      (fuseCol a b i j).val :=
  rfl

/-! ## Concrete coefficient laws -/

theorem fusionCoefficient_zero_left (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b) (y : Coeff b) :
    fusionCoefficient a b target source (Coeff.zero a) y =
      Coeff.zero (a + b) := by
  ext g
  simp [fusionCoefficient, Coeff.zero]

theorem fusionCoefficient_zero_right (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b) (x : Coeff a) :
    fusionCoefficient a b target source x (Coeff.zero b) =
      Coeff.zero (a + b) := by
  ext g
  simp [fusionCoefficient, Coeff.zero]

theorem fusionCoefficient_add_left (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b)
    (x x' : Coeff a) (y : Coeff b) :
    fusionCoefficient a b target source (Coeff.add a x x') y =
      Coeff.add (a + b) (fusionCoefficient a b target source x y)
        (fusionCoefficient a b target source x' y) := by
  ext g
  simp only [fusionCoefficient, Coeff.add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fusionCoefficient_add_right (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b)
    (x : Coeff a) (y y' : Coeff b) :
    fusionCoefficient a b target source x (Coeff.add b y y') =
      Coeff.add (a + b) (fusionCoefficient a b target source x y)
        (fusionCoefficient a b target source x y') := by
  ext g
  simp only [fusionCoefficient, Coeff.add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fusionCoefficient_smul_left (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b) (r : ℝ)
    (x : Coeff a) (y : Coeff b) :
    fusionCoefficient a b target source (Coeff.smul a r x) y =
      Coeff.smul (a + b) r (fusionCoefficient a b target source x y) := by
  ext g
  simp only [fusionCoefficient, Coeff.smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fusionCoefficient_smul_right (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b) (r : ℝ)
    (x : Coeff a) (y : Coeff b) :
    fusionCoefficient a b target source x (Coeff.smul b r y) =
      Coeff.smul (a + b) r (fusionCoefficient a b target source x y) := by
  ext g
  simp only [fusionCoefficient, Coeff.smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ## Semantic multiplicativity bridge

Only this law module mentions the semantic fusion equivalence.  The pure
tensor below is defined locally from the universal tensor map; in particular
the raw data does not depend on a shifted or normalized tensor construction.
-/

open TensorProduct GradedTensorProduct

/-- The unshifted pure tensor, bundled as a bilinear map for the concrete
`realRep` algebras. -/
noncomputable def semanticPureTensor (a b : ZMod 8) :
    (realRep a).carrier →ₗ[ℝ] (realRep b).carrier →ₗ[ℝ]
      ((realRep a).gtensor (realRep b)).carrier :=
  (TensorProduct.mk ℝ (realRep a).carrier (realRep b).carrier).compr₂
    (GradedTensorProduct.of ℝ
      (realRep a).grading (realRep b).grading).toLinearMap

@[simp]
theorem semanticPureTensor_apply (a b : ZMod 8)
    (x : (realRep a).carrier) (y : (realRep b).carrier) :
    semanticPureTensor a b x y =
      GradedTensorProduct.tmul
        (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ x y :=
  rfl

/-- Apply the semantic fusion equivalence after forming an unshifted pure
tensor. -/
noncomputable def semanticFusionMatrix (a b : ZMod 8) :
    (realRep a).carrier →ₗ[ℝ] (realRep b).carrier →ₗ[ℝ]
      Matrix (Fin (Superfusion.realSize a b).1 ⊕
          Fin (Superfusion.realSize a b).2)
        (Fin (Superfusion.realSize a b).1 ⊕
          Fin (Superfusion.realSize a b).2)
        (realRep (a + b)).carrier :=
  (semanticPureTensor a b).compr₂
    (realFuse a b).toAlgEquiv.toLinearMap

@[simp]
theorem semanticFusionMatrix_apply (a b : ZMod 8)
    (x : (realRep a).carrier) (y : (realRep b).carrier) :
    semanticFusionMatrix a b x y =
      (realFuse a b).toAlgEquiv (semanticPureTensor a b x y) :=
  rfl

/-- The `(target,source)` entry of the semantic fusion matrix. -/
noncomputable def semanticFusionEntry (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b) :
    (realRep a).carrier →ₗ[ℝ] (realRep b).carrier →ₗ[ℝ]
      (realRep (a + b)).carrier :=
  (semanticFusionMatrix a b).compr₂
    (Matrix.entryLinearMap ℝ (realRep (a + b)).carrier
      (RModCoordinate.FusionTable.frameIndex a b target)
      (RModCoordinate.FusionTable.frameIndex a b source))

@[simp]
theorem semanticFusionEntry_apply (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b)
    (x : (realRep a).carrier) (y : (realRep b).carrier) :
    semanticFusionEntry a b target source x y =
      semanticFusionMatrix a b x y
        (RModCoordinate.FusionTable.frameIndex a b target)
        (RModCoordinate.FusionTable.frameIndex a b source) :=
  rfl

theorem semantic_fusionCoefficient_eq_matrix_sum
    (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b)
    (x : Coeff a) (y : Coeff b) :
    Coeff.semantic (a + b) (fusionCoefficient a b target source x y) =
      ∑ g : Fin (realRepDim (a + b).val),
        (∑ i : Fin (realRepDim a.val),
          ∑ j : Fin (realRepDim b.val),
            realFuseMatrix a b
                (fuseRow a b
                  (RModCoordinate.FusionTable.frameIndex a b target)
                  (RModCoordinate.FusionTable.frameIndex a b source) g)
                (fuseCol a b i j) * x i * y j) •
          realRepBasis (a + b) g := by
  classical
  simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply,
    fusionCoefficient]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [outputPosition_eq_fuseRow_val, inputPosition_eq_fuseCol_val,
    entry_isFuseZ a b
    (fuseRow a b
      (RModCoordinate.FusionTable.frameIndex a b target)
      (RModCoordinate.FusionTable.frameIndex a b source) g)
    (fuseCol a b i j)]

/-- Interpreting one raw coefficient gives the corresponding entry of
`realFuse` on the unshifted pure tensor. -/
theorem semantic_fusionCoefficient_eq_fusion_sum
    (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b)
    (x : Coeff a) (y : Coeff b) :
    Coeff.semantic (a + b) (fusionCoefficient a b target source x y) =
      ∑ i : Fin (realRepDim a.val),
        ∑ j : Fin (realRepDim b.val),
          (x i * y j) •
            (realFuse a b).toAlgEquiv
              (GradedTensorProduct.tmul
                (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
                (realRepBasis a i) (realRepBasis b j))
              (RModCoordinate.FusionTable.frameIndex a b target)
              (RModCoordinate.FusionTable.frameIndex a b source) := by
  rw [semantic_fusionCoefficient_eq_matrix_sum]
  simp_rw [realFuse_tmul_entry]
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  ring

@[simp]
theorem semanticFusionEntry_basis (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b)
    (i : Fin (realRepDim a.val)) (j : Fin (realRepDim b.val)) :
    semanticFusionEntry a b target source
        (realRepBasis a i) (realRepBasis b j) =
      (realFuse a b).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
          (realRepBasis a i) (realRepBasis b j))
        (RModCoordinate.FusionTable.frameIndex a b target)
        (RModCoordinate.FusionTable.frameIndex a b source) :=
  rfl

/-- Full semantic comparison for the raw fusion coefficient. -/
theorem semantic_fusionCoefficient_eq_semanticEntry
    (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b)
    (x : Coeff a) (y : Coeff b) :
    Coeff.semantic (a + b) (fusionCoefficient a b target source x y) =
      semanticFusionEntry a b target source
        (Coeff.semantic a x) (Coeff.semantic b y) := by
  classical
  rw [semantic_fusionCoefficient_eq_fusion_sum]
  calc
    (∑ i : Fin (realRepDim a.val),
        ∑ j : Fin (realRepDim b.val),
          (x i * y j) •
            (realFuse a b).toAlgEquiv
              (GradedTensorProduct.tmul
                (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
                (realRepBasis a i) (realRepBasis b j))
              (RModCoordinate.FusionTable.frameIndex a b target)
              (RModCoordinate.FusionTable.frameIndex a b source)) =
        ∑ i : Fin (realRepDim a.val),
          ∑ j : Fin (realRepDim b.val),
            (x i * y j) •
              semanticFusionEntry a b target source
                (realRepBasis a i) (realRepBasis b j) := by
      rfl
    _ = semanticFusionEntry a b target source
          (Coeff.semantic a x) (Coeff.semantic b y) := by
      simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply,
        map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, mul_comm]

/-! ## Unit and grading from the existing semantic certificate -/

@[simp]
theorem semanticPureTensor_one_one (a b : ZMod 8) :
    semanticPureTensor a b (1 : (realRep a).carrier)
        (1 : (realRep b).carrier) = 1 := by
  change GradedTensorProduct.of ℝ
      (realRep a).grading (realRep b).grading
      ((1 : (realRep a).carrier) ⊗ₜ[ℝ] (1 : (realRep b).carrier)) = 1
  rw [← Algebra.TensorProduct.one_def, GradedTensorProduct.of_one]

@[simp]
theorem semanticFusionMatrix_one_one (a b : ZMod 8) :
    semanticFusionMatrix a b 1 1 = 1 := by
  rw [semanticFusionMatrix_apply, semanticPureTensor_one_one]
  exact map_one (realFuse a b).toAlgEquiv

@[simp]
theorem semanticFusionEntry_one_one (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b) :
    semanticFusionEntry a b target source 1 1 =
      if RModCoordinate.FusionTable.frameIndex a b target =
          RModCoordinate.FusionTable.frameIndex a b source then 1 else 0 := by
  rw [semanticFusionEntry_apply, semanticFusionMatrix_one_one]
  exact Matrix.one_apply

/-- The unit law follows from `map_one` for the certified semantic fusion
equivalence. -/
theorem fusionCoefficient_one (a b : ZMod 8)
    (target source : RModCoordinate.FusionTable.Index a b) :
    fusionCoefficient a b target source (Coeff.one a) (Coeff.one b) =
      if target = source then Coeff.one (a + b) else Coeff.zero (a + b) := by
  apply (Coeff.semantic (a + b)).injective
  rw [semantic_fusionCoefficient_eq_semanticEntry,
    Coeff.semantic_one, Coeff.semantic_one,
    semanticFusionEntry_one_one]
  by_cases h : target = source
  · subst target
    simp [Coeff.semantic_one]
  · have hf : RModCoordinate.FusionTable.frameIndex a b target ≠
        RModCoordinate.FusionTable.frameIndex a b source := by
      intro he
      exact h (finSumFinEquiv.symm.injective he)
    simp [h, hf, Coeff.semantic_zero]

/-- Coordinate support implies semantic homogeneity. -/
private theorem semantic_mem_of_memGrade (a : ZMod 8) (d : ZMod 2)
    (x : Coeff a) (hx : Coeff.MemGrade a d x) :
    Coeff.semantic a x ∈ (realRep a).grading d := by
  classical
  simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : realRepBasisParity a i = d
  · exact Submodule.smul_mem _ _ (hi ▸ realRepBasis_mem a i)
  · rw [hx i hi, zero_smul]
    exact Submodule.zero_mem _

private theorem zmod2_eq_add_one_of_ne (p d : ZMod 2) (h : p ≠ d) :
    p = d + 1 := by
  rcases zmod2_cases p with hp | hp <;>
    rcases zmod2_cases d with hd | hd <;>
    subst p <;> subst d <;> simp_all [Coeff.add_self_eq_zero]

/-- The canonical homogeneous basis detects coordinate support. -/
private theorem semantic_mem_iff_memGrade (a : ZMod 8) (d : ZMod 2)
    (x : Coeff a) :
    Coeff.semantic a x ∈ (realRep a).grading d ↔
      Coeff.MemGrade a d x := by
  constructor
  · intro hx
    let xd : Coeff a := Coeff.component a d x
    let xo : Coeff a := Coeff.component a (d + 1) x
    have hxd : Coeff.semantic a xd ∈ (realRep a).grading d :=
      semantic_mem_of_memGrade a d xd (Coeff.component_memGrade a d x)
    have hxo' : Coeff.semantic a xo ∈ (realRep a).grading (d + 1) :=
      semantic_mem_of_memGrade a (d + 1) xo
        (Coeff.component_memGrade a (d + 1) x)
    have hsplit : Coeff.add a xd xo = x :=
      Coeff.component_complement a d x
    have hsem : Coeff.semantic a xd + Coeff.semantic a xo =
        Coeff.semantic a x := by
      rw [← Coeff.semantic_add, hsplit]
    have hxo : Coeff.semantic a xo ∈ (realRep a).grading d := by
      have heq : Coeff.semantic a xo =
          Coeff.semantic a x - Coeff.semantic a xd := by
        rw [← hsem]
        abel
      rw [heq]
      exact Submodule.sub_mem _ hx hxd
    have hzero : Coeff.semantic a xo = 0 := by
      rcases zmod2_cases d with hd | hd <;> subst d
      · exact (isCompl_grades (realRep a).grading).disjoint.le_bot
          ⟨hxo, hxo'⟩
      · exact (isCompl_grades (realRep a).grading).disjoint.symm.le_bot
          ⟨hxo, hxo'⟩
    have hxo0 : xo = Coeff.zero a := by
      apply (Coeff.semantic a).injective
      rw [hzero, Coeff.semantic_zero]
    intro i hi
    have hp : realRepBasisParity a i = d + 1 :=
      zmod2_eq_add_one_of_ne _ _ hi
    have hcoord := congrFun hxo0 i
    simpa [xo, Coeff.component, hp, Coeff.zero] using hcoord
  · exact semantic_mem_of_memGrade a d x

private theorem indexParity_eq_sumParity (a b : ZMod 8)
    (r : RModCoordinate.FusionTable.Index a b) :
    RModCoordinate.FusionTable.indexParity a b r =
      sumParity (Superfusion.realSize a b).1 (Superfusion.realSize a b).2
        (RModCoordinate.FusionTable.frameIndex a b r) := by
  rcases hframe : RModCoordinate.FusionTable.frameIndex a b r with u | u
  · have hr : r = finSumFinEquiv (Sum.inl u) := by
      calc
        r = finSumFinEquiv
            (RModCoordinate.FusionTable.frameIndex a b r) :=
          (finSumFinEquiv.apply_symm_apply r).symm
        _ = finSumFinEquiv (Sum.inl u) := congrArg finSumFinEquiv hframe
    rw [hr]
    simp [RModCoordinate.FusionTable.indexParity,
      sumParity]
  · have hr : r = finSumFinEquiv (Sum.inr u) := by
      calc
        r = finSumFinEquiv
            (RModCoordinate.FusionTable.frameIndex a b r) :=
          (finSumFinEquiv.apply_symm_apply r).symm
        _ = finSumFinEquiv (Sum.inr u) := congrArg finSumFinEquiv hframe
    rw [hr]
    simp [RModCoordinate.FusionTable.indexParity,
      sumParity]

private theorem semanticFusionMatrix_mem (a b : ZMod 8) (i j : ZMod 2)
    {x : Coeff a} {y : Coeff b}
    (hx : Coeff.MemGrade a i x) (hy : Coeff.MemGrade b j y) :
    semanticFusionMatrix a b (Coeff.semantic a x) (Coeff.semantic b y) ∈
      matrixGradingA
        (sumParity (Superfusion.realSize a b).1
          (Superfusion.realSize a b).2)
        (realRep (a + b)).grading (i + j) := by
  have hk : semanticPureTensor a b
        (Coeff.semantic a x) (Coeff.semantic b y) ∈
      tensorGrading (realRep a).grading (realRep b).grading (i + j) := by
    rw [semanticPureTensor_apply]
    exact tmul_mem_tensorGrading (realRep a).grading (realRep b).grading
      (semantic_mem_of_memGrade a i x hx)
      (semantic_mem_of_memGrade b j y hy)
  change (realFuse a b).toAlgEquiv
      (semanticPureTensor a b
        (Coeff.semantic a x) (Coeff.semantic b y)) ∈
    ((realRep (a + b)).matrixSuper
      (Superfusion.realSize a b).1
      (Superfusion.realSize a b).2).grading (i + j)
  rw [← (realFuse a b).map_grading (i + j)]
  exact Submodule.mem_map_of_mem hk

/-- Grading of raw fusion coefficients follows from the certified semantic
fusion map and its checkerboard matrix grading. -/
theorem fusionCoefficient_memGrade (a b : ZMod 8) (i j : ZMod 2)
    (target source : RModCoordinate.FusionTable.Index a b)
    {x : Coeff a} {y : Coeff b}
    (hx : Coeff.MemGrade a i x) (hy : Coeff.MemGrade b j y) :
    Coeff.MemGrade (a + b)
      (i + j + RModCoordinate.FusionTable.indexParity a b target +
        RModCoordinate.FusionTable.indexParity a b source)
      (fusionCoefficient a b target source x y) := by
  apply (semantic_mem_iff_memGrade (a + b) _ _).mp
  rw [semantic_fusionCoefficient_eq_semanticEntry]
  have hmatrix := semanticFusionMatrix_mem a b i j hx hy
  have hentry :=
    (mem_matrixGradingA
      (sumParity (Superfusion.realSize a b).1
        (Superfusion.realSize a b).2)
      (realRep (a + b)).grading).mp hmatrix
    (RModCoordinate.FusionTable.frameIndex a b target)
    (RModCoordinate.FusionTable.frameIndex a b source)
  simpa only [indexParity_eq_sumParity, semanticFusionEntry_apply] using hentry

/-- Unshifted pure tensors obey the super interchange sign. -/
private theorem semanticPureTensor_mul (a b : ZMod 8) (i j : ZMod 2)
    {x x' : (realRep a).carrier} {y y' : (realRep b).carrier}
    (hx' : x' ∈ (realRep a).grading i)
    (hy : y ∈ (realRep b).grading j) :
    semanticPureTensor a b x y * semanticPureTensor a b x' y' =
      ((sgn (j * i) : ℤˣ) : ℤ) •
        semanticPureTensor a b (x * x') (y * y') := by
  change
    GradedTensorProduct.tmul
          (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ x y *
        GradedTensorProduct.tmul
          (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ x' y' =
      ((sgn (j * i) : ℤˣ) : ℤ) •
        GradedTensorProduct.tmul
          (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
          (x * x') (y * y')
  have h := GradedTensorProduct.tmul_coe_mul_coe_tmul
    (realRep a).grading (realRep b).grading
    x (⟨y, hy⟩ : (realRep b).grading j)
      (⟨x', hx'⟩ : (realRep a).grading i) y'
  rw [← sgn_eq_neg_one_uzpow, Units.smul_def] at h
  exact h

theorem semanticFusionMatrix_mul (a b : ZMod 8) (i j : ZMod 2)
    {x x' : (realRep a).carrier} {y y' : (realRep b).carrier}
    (hx' : x' ∈ (realRep a).grading i)
    (hy : y ∈ (realRep b).grading j) :
    semanticFusionMatrix a b x y * semanticFusionMatrix a b x' y' =
      ((sgn (j * i) : ℤˣ) : ℤ) •
        semanticFusionMatrix a b (x * x') (y * y') := by
  change
    (realFuse a b).toAlgEquiv (semanticPureTensor a b x y) *
        (realFuse a b).toAlgEquiv (semanticPureTensor a b x' y') =
      ((sgn (j * i) : ℤˣ) : ℤ) •
        (realFuse a b).toAlgEquiv
          (semanticPureTensor a b (x * x') (y * y'))
  rw [← map_mul, semanticPureTensor_mul a b i j hx' hy, map_zsmul]

/-- Entrywise semantic super interchange, reindexed by the raw finite frame. -/
theorem semanticFusionEntry_comp (a b : ZMod 8) (i j : ZMod 2)
    {x x' : (realRep a).carrier} {y y' : (realRep b).carrier}
    (hx' : x' ∈ (realRep a).grading i)
    (hy : y ∈ (realRep b).grading j)
    (target source : RModCoordinate.FusionTable.Index a b) :
    (∑ middle : RModCoordinate.FusionTable.Index a b,
        semanticFusionEntry a b target middle x y *
          semanticFusionEntry a b middle source x' y') =
      ((sgn (j * i) : ℤˣ) : ℤ) •
        semanticFusionEntry a b target source (x * x') (y * y') := by
  let M : Matrix
      (Fin (Superfusion.realSize a b).1 ⊕ Fin (Superfusion.realSize a b).2)
      (Fin (Superfusion.realSize a b).1 ⊕ Fin (Superfusion.realSize a b).2)
      (realRep (a + b)).carrier := semanticFusionMatrix a b x y
  let M' : Matrix
      (Fin (Superfusion.realSize a b).1 ⊕ Fin (Superfusion.realSize a b).2)
      (Fin (Superfusion.realSize a b).1 ⊕ Fin (Superfusion.realSize a b).2)
      (realRep (a + b)).carrier := semanticFusionMatrix a b x' y'
  have h := congrArg
    (fun N : Matrix
        (Fin (Superfusion.realSize a b).1 ⊕ Fin (Superfusion.realSize a b).2)
        (Fin (Superfusion.realSize a b).1 ⊕ Fin (Superfusion.realSize a b).2)
        (realRep (a + b)).carrier =>
      N (RModCoordinate.FusionTable.frameIndex a b target)
        (RModCoordinate.FusionTable.frameIndex a b source))
    (semanticFusionMatrix_mul a b i j
      (x := x) (x' := x') (y := y) (y' := y') hx' hy)
  rw [Matrix.mul_apply] at h
  have hreindex :
      (∑ middle : RModCoordinate.FusionTable.Index a b,
          M (RModCoordinate.FusionTable.frameIndex a b target)
              (RModCoordinate.FusionTable.frameIndex a b middle) *
            M' (RModCoordinate.FusionTable.frameIndex a b middle)
              (RModCoordinate.FusionTable.frameIndex a b source)) =
        ∑ middle : (Fin (Superfusion.realSize a b).1 ⊕
            Fin (Superfusion.realSize a b).2),
          M (RModCoordinate.FusionTable.frameIndex a b target) middle *
            M' middle
              (RModCoordinate.FusionTable.frameIndex a b source) := by
    simpa only [RModCoordinate.FusionTable.frameIndex] using
      (Equiv.sum_comp
        (finSumFinEquiv.symm : RModCoordinate.FusionTable.Index a b ≃
          (Fin (Superfusion.realSize a b).1 ⊕
            Fin (Superfusion.realSize a b).2))
        (fun middle =>
          M (RModCoordinate.FusionTable.frameIndex a b target) middle *
            M' middle
              (RModCoordinate.FusionTable.frameIndex a b source)))
  change (∑ middle : RModCoordinate.FusionTable.Index a b,
      M (RModCoordinate.FusionTable.frameIndex a b target)
          (RModCoordinate.FusionTable.frameIndex a b middle) *
        M' (RModCoordinate.FusionTable.frameIndex a b middle)
          (RModCoordinate.FusionTable.frameIndex a b source)) = _
  rw [hreindex]
  simpa only [M, M', Matrix.smul_apply, semanticFusionEntry_apply] using h

/-- Multiplicativity of the raw coefficient matrix.  The sign is kept in
the canonical integer-unit form here; the concrete bundle law may rewrite
its real cast to the public parity-sign function. -/
theorem fusionCoefficient_mul (a b : ZMod 8) (i j : ZMod 2)
    (target source : RModCoordinate.FusionTable.Index a b)
    {x x' : Coeff a} {y y' : Coeff b}
    (hy : Coeff.MemGrade b j y) (hx' : Coeff.MemGrade a i x') :
    (∑ middle : RModCoordinate.FusionTable.Index a b,
        Coeff.mul (a + b)
          (fusionCoefficient a b target middle x y)
          (fusionCoefficient a b middle source x' y')) =
      Coeff.smul (a + b) ((((sgn (j * i) : ℤˣ) : ℤ) : ℝ))
        (fusionCoefficient a b target source
          (Coeff.mul a x x') (Coeff.mul b y y')) := by
  classical
  apply (Coeff.semantic (a + b)).injective
  rw [map_sum, Coeff.semantic_smul]
  simp_rw [Coeff.semantic_mul,
    semantic_fusionCoefficient_eq_semanticEntry]
  rw [semanticFusionEntry_comp a b i j
    (semantic_mem_of_memGrade a i x' hx')
    (semantic_mem_of_memGrade b j y hy)]
  rw [Coeff.semantic_mul, Coeff.semantic_mul]
  rw [Int.cast_smul_eq_zsmul]

end Superfusion.RMod.RawDCT.FusionTableLaws
