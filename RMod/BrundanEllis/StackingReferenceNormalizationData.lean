import RMod.BrundanEllis.StackingReferenceCommutorData
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar normalization of the concrete exchange maps. The table records
signs and powers of sqrt(2), retaining the half-integral powers required by
the reference. Coherence of these choices is a separate proof obligation. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

def normalizationNegative (a b : ZMod 8) : Bool :=
  ([false, true, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, true] : List Bool).getD (8 * a.val + b.val) false

def normalizationExponent (a b : ZMod 8) : ℤ :=
  ([0, 10, 10, 12, 10, 16, 12, 6, -10, -1, -2, 5, 6, 13, 10, 5, -10, -2, 0, 4, 4, 10, 8, 4, -12, -5, -4, -3, 2, 7, 6, 3, -10, -6, -4, -2, 0, 4, 4, 2, -16, -13, -10, -7, -4, -3, 2, 1, -12, -10, -8, -6, -4, -2, 0, -2, -6, -5, -4, -3, -2, -1, -2, -1] : List ℤ).getD (8 * a.val + b.val) 0

noncomputable def normalizingScalar (a b : ZMod 8) : ℝ :=
  (if normalizationNegative a b then -1 else 1) *
    (Real.sqrt 2) ^ normalizationExponent a b

/-- A genuinely fractional scale occurs on a unit face. -/
example : normalizationExponent 1 0 = -10 := rfl

/-- A different face requires multiplication by a positive integral power. -/
example : normalizationExponent 1 4 = 6 := rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
