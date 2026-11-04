import Superfusion.RMod.RawDCT.RealComputableNuBeta

/-!
# Saved unit-face values of the real scalar cochain

This file is the small table bridge used by the concrete coordinate unitors.
It selectively preserves the unit-face lemmas from the earlier constructive
development.  In particular, these are lookups in the already frozen
three-variable `beta` table; they do not recompute a fourfold connector or a
pentagon certificate.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT.RealUnitFaceTable

open RawDCT

/-! ## Executable scalar on the left-unit face -/

/-- The stored dyadic scalar at `(0,0,c)`. -/
def leftScalarDyadic (c : ZMod 8) : DyadicUnit :=
  GaugeChi.realLeanBetaTable
    (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 0)
    (Multiplicative.ofAdd c)

/-- On the middle-unit face the frozen `beta` table depends only on the last
label.  This is the saved finite-table proof from the constructive unitor
development. -/
theorem beta_middle_unit (a c : ZMod 8) :
    GaugeChi.realLeanBetaTable
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd 0)
        (Multiplicative.ofAdd c) =
      leftScalarDyadic c := by
  fin_cases a <;> fin_cases c <;> decide +kernel

/-- The third unit face of the frozen `beta` table is normalized.  This is
the corresponding saved finite-table proof. -/
theorem beta_right_unit (a b : ZMod 8) :
    GaugeChi.realLeanBetaTable
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd 0) = 1 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

end Superfusion.RMod.FromRawDCT.RealUnitFaceTable
