import Superfusion.GaugeChi.TripleCerts.FuseShadows
import Superfusion.RMod.Constructive.CoefficientData
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Data-only raw fusion table

This module wraps the 64 pre-existing certified integer shadows directly.
It adds only a total dispatcher, the finite frame arithmetic used by raw C,
and the executable coefficient kernel; there is no second numerical table.
-/

set_option autoImplicit false

namespace Superfusion

namespace RModCoordinate
namespace FusionTable

open GaugeChi

/-- Total natural-label dispatcher for all 64 raw fusion matrices. -/
def entryAux : ℕ → ℕ → ℕ → ℕ → ℤ
  | 0, 0 => natTable2 _ GaugeChi.TripleCerts.fuseZ_0_0
  | 0, 1 => natTable2 _ GaugeChi.TripleCerts.fuseZ_0_1
  | 0, 2 => natTable2 _ GaugeChi.TripleCerts.fuseZ_0_2
  | 0, 3 => natTable2 _ GaugeChi.TripleCerts.fuseZ_0_3
  | 0, 4 => natTable2 _ GaugeChi.TripleCerts.fuseZ_0_4
  | 0, 5 => natTable2 _ GaugeChi.TripleCerts.fuseZ_0_5
  | 0, 6 => natTable2 _ GaugeChi.TripleCerts.fuseZ_0_6
  | 0, 7 => natTable2 _ GaugeChi.TripleCerts.fuseZ_0_7
  | 1, 0 => natTable2 _ GaugeChi.TripleCerts.fuseZ_1_0
  | 1, 1 => natTable2 _ GaugeChi.TripleCerts.fuseZ_1_1
  | 1, 2 => natTable2 _ GaugeChi.TripleCerts.fuseZ_1_2
  | 1, 3 => natTable2 _ GaugeChi.TripleCerts.fuseZ_1_3
  | 1, 4 => natTable2 _ GaugeChi.TripleCerts.fuseZ_1_4
  | 1, 5 => natTable2 _ GaugeChi.TripleCerts.fuseZ_1_5
  | 1, 6 => natTable2 _ GaugeChi.TripleCerts.fuseZ_1_6
  | 1, 7 => natTable2 _ GaugeChi.TripleCerts.fuseZ_1_7
  | 2, 0 => natTable2 _ GaugeChi.TripleCerts.fuseZ_2_0
  | 2, 1 => natTable2 _ GaugeChi.TripleCerts.fuseZ_2_1
  | 2, 2 => natTable2 _ GaugeChi.TripleCerts.fuseZ_2_2
  | 2, 3 => natTable2 _ GaugeChi.TripleCerts.fuseZ_2_3
  | 2, 4 => natTable2 _ GaugeChi.TripleCerts.fuseZ_2_4
  | 2, 5 => natTable2 _ GaugeChi.TripleCerts.fuseZ_2_5
  | 2, 6 => natTable2 _ GaugeChi.TripleCerts.fuseZ_2_6
  | 2, 7 => natTable2 _ GaugeChi.TripleCerts.fuseZ_2_7
  | 3, 0 => natTable2 _ GaugeChi.TripleCerts.fuseZ_3_0
  | 3, 1 => natTable2 _ GaugeChi.TripleCerts.fuseZ_3_1
  | 3, 2 => natTable2 _ GaugeChi.TripleCerts.fuseZ_3_2
  | 3, 3 => natTable2 _ GaugeChi.TripleCerts.fuseZ_3_3
  | 3, 4 => natTable2 _ GaugeChi.TripleCerts.fuseZ_3_4
  | 3, 5 => natTable2 _ GaugeChi.TripleCerts.fuseZ_3_5
  | 3, 6 => natTable2 _ GaugeChi.TripleCerts.fuseZ_3_6
  | 3, 7 => natTable2 _ GaugeChi.TripleCerts.fuseZ_3_7
  | 4, 0 => natTable2 _ GaugeChi.TripleCerts.fuseZ_4_0
  | 4, 1 => natTable2 _ GaugeChi.TripleCerts.fuseZ_4_1
  | 4, 2 => natTable2 _ GaugeChi.TripleCerts.fuseZ_4_2
  | 4, 3 => natTable2 _ GaugeChi.TripleCerts.fuseZ_4_3
  | 4, 4 => natTable2 _ GaugeChi.TripleCerts.fuseZ_4_4
  | 4, 5 => natTable2 _ GaugeChi.TripleCerts.fuseZ_4_5
  | 4, 6 => natTable2 _ GaugeChi.TripleCerts.fuseZ_4_6
  | 4, 7 => natTable2 _ GaugeChi.TripleCerts.fuseZ_4_7
  | 5, 0 => natTable2 _ GaugeChi.TripleCerts.fuseZ_5_0
  | 5, 1 => natTable2 _ GaugeChi.TripleCerts.fuseZ_5_1
  | 5, 2 => natTable2 _ GaugeChi.TripleCerts.fuseZ_5_2
  | 5, 3 => natTable2 _ GaugeChi.TripleCerts.fuseZ_5_3
  | 5, 4 => natTable2 _ GaugeChi.TripleCerts.fuseZ_5_4
  | 5, 5 => natTable2 _ GaugeChi.TripleCerts.fuseZ_5_5
  | 5, 6 => natTable2 _ GaugeChi.TripleCerts.fuseZ_5_6
  | 5, 7 => natTable2 _ GaugeChi.TripleCerts.fuseZ_5_7
  | 6, 0 => natTable2 _ GaugeChi.TripleCerts.fuseZ_6_0
  | 6, 1 => natTable2 _ GaugeChi.TripleCerts.fuseZ_6_1
  | 6, 2 => natTable2 _ GaugeChi.TripleCerts.fuseZ_6_2
  | 6, 3 => natTable2 _ GaugeChi.TripleCerts.fuseZ_6_3
  | 6, 4 => natTable2 _ GaugeChi.TripleCerts.fuseZ_6_4
  | 6, 5 => natTable2 _ GaugeChi.TripleCerts.fuseZ_6_5
  | 6, 6 => natTable2 _ GaugeChi.TripleCerts.fuseZ_6_6
  | 6, 7 => natTable2 _ GaugeChi.TripleCerts.fuseZ_6_7
  | 7, 0 => natTable2 _ GaugeChi.TripleCerts.fuseZ_7_0
  | 7, 1 => natTable2 _ GaugeChi.TripleCerts.fuseZ_7_1
  | 7, 2 => natTable2 _ GaugeChi.TripleCerts.fuseZ_7_2
  | 7, 3 => natTable2 _ GaugeChi.TripleCerts.fuseZ_7_3
  | 7, 4 => natTable2 _ GaugeChi.TripleCerts.fuseZ_7_4
  | 7, 5 => natTable2 _ GaugeChi.TripleCerts.fuseZ_7_5
  | 7, 6 => natTable2 _ GaugeChi.TripleCerts.fuseZ_7_6
  | 7, 7 => natTable2 _ GaugeChi.TripleCerts.fuseZ_7_7
  | _, _ => fun _ _ => 0

def entry (a b : ZMod 8) (row column : ℕ) : ℤ :=
  entryAux a.val b.val row column

/-- Canonical row index of the `p|q` fusion frame. -/
abbrev Index (a b : ZMod 8) : Type :=
  Fin ((realSize a b).1 + (realSize a b).2)

/-- Convert the flat even-first index into the semantic sum frame. -/
def frameIndex (a b : ZMod 8) (r : Index a b) :
    Fin (realSize a b).1 ⊕ Fin (realSize a b).2 :=
  finSumFinEquiv.symm r

/-- Unshifted parity of a fusion-frame row. -/
def indexParity (a b : ZMod 8) (r : Index a b) : ZMod 2 :=
  if r.val < (realSize a b).1 then 0 else 1

/-- Flatten `(target,source,basis)` in the frozen row-major convention. -/
def outputPosition (a b : ZMod 8) (target source : Index a b)
    (g : Fin (realRepDim (a + b).val)) : ℕ :=
  g.val + realRepDim (a + b).val *
    (source.val + ((realSize a b).1 + (realSize a b).2) * target.val)

/-- Flatten a pair of input basis indices in product-major convention. -/
def inputPosition (a b : ZMod 8) (i : Fin (realRepDim a.val))
    (j : Fin (realRepDim b.val)) : ℕ :=
  j.val + realRepDim b.val * i.val

/-- `(target,source)` coefficient of the raw fusion image of `x ⊗ y`.

This is executable data: it uses the existing integer shadow and finite
coordinate vectors.  Its comparison with `realFuse` belongs to the separate
law module. -/
def fusionCoefficient (a b : ZMod 8)
    (target source : Index a b) (x : Coeff a) (y : Coeff b) :
    Coeff (a + b) := fun g =>
  ∑ i : Fin (realRepDim a.val),
    ∑ j : Fin (realRepDim b.val),
      (entry a b (outputPosition a b target source g)
          (inputPosition a b i j) : ℝ) * x i * y j

/-! Closed reduction controls. -/

example : entry 0 0 0 0 = 1 := rfl

example : indexParity 1 3
    (⟨0, by change 0 < 2; omega⟩ : Index 1 3) = 0 := rfl

example : indexParity 1 3
    (⟨1, by change 1 < 2; omega⟩ : Index 1 3) = 1 := rfl

end FusionTable
end RModCoordinate
end Superfusion
