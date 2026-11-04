import RMod.Classification.Proofs.Parity
import Superfusion.Conventions
import Mathlib.Tactic.Ring

/-!
# Scalar powers for signed naturality

The real-valued parity power is the value of the existing unit-valued
sign homomorphism. Its addition and cancellation laws therefore follow
from the established sign calculation.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem parity_power_eq_sgn (a : ZMod 2) :
    (-1 : ℝ) ^ a.val = ((Superfusion.sgn a : ℝˣ) : ℝ) := by
  rcases parity_cases a with h | h <;> subst a <;>
    simp [Superfusion.sgn, ZMod.val_one]

theorem parity_power_add (a b : ZMod 2) :
    (-1 : ℝ) ^ (a + b).val = (-1 : ℝ) ^ a.val * (-1 : ℝ) ^ b.val := by
  simp only [parity_power_eq_sgn, Superfusion.sgn_add, Units.val_mul]

theorem parity_power_mul_self (a : ZMod 2) :
    (-1 : ℝ) ^ a.val * (-1 : ℝ) ^ a.val = 1 := by
  rw [parity_power_eq_sgn, ← Units.val_mul, Superfusion.sgn_mul_self', Units.val_one]

theorem koszul_power_add_right (a b c : ZMod 2) :
    (-1 : ℝ) ^ (a * (b + c)).val = (-1 : ℝ) ^ (a * b).val * (-1 : ℝ) ^ (a * c).val := by
  rw [mul_add, parity_power_add]

theorem koszul_power_cancel (a b c : ZMod 2) :
    (-1 : ℝ) ^ (a * c).val * (-1 : ℝ) ^ (a * (b + c)).val = (-1 : ℝ) ^ (a * b).val := by
  rw [koszul_power_add_right]
  calc
    _ = (-1 : ℝ) ^ (a * b).val * ((-1 : ℝ) ^ (a * c).val * (-1 : ℝ) ^ (a * c).val) := by ring
    _ = _ := by rw [parity_power_mul_self, mul_one]

end RMod.Classification
