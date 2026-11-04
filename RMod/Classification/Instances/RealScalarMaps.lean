import RMod.Classification.Abstract.Parameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Magnitude, logarithm and sign of real units

Mathlib's absolute-value homomorphism and exponential are lifted to units.
The sign is their multiplicative quotient. These maps let the signed
pentagon be treated by homomorphisms, without a new scalar structure.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def unitMagnitude : ℝˣ →* ℝˣ := Units.map (absHom : ℝ →*₀ ℝ).toMonoidHom

noncomputable def unitExp : Multiplicative ℝ →* ℝˣ := Real.expMonoidHom.toHomUnits

noncomputable def unitLog : ℝˣ →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (Real.log (x : ℝ))
  map_one' := Real.log_one
  map_mul' x y := Real.log_mul (Units.ne_zero x) (Units.ne_zero y)

noncomputable def unitSign : ℝˣ →* ℝˣ := (MonoidHom.id ℝˣ) / unitMagnitude

@[simp]
theorem unitMagnitude_val (x : ℝˣ) : (unitMagnitude x : ℝ) = |(x : ℝ)| := rfl

@[simp]
theorem unitExp_val (x : ℝ) : (unitExp (Multiplicative.ofAdd x) : ℝ) = Real.exp x := rfl

@[simp]
theorem unitExp_unitLog (x : ℝˣ) : unitExp (unitLog x) = unitMagnitude x := by
  apply Units.ext
  exact Real.exp_log_eq_abs (Units.ne_zero x)

theorem unitSign_eq_div (x : ℝˣ) : unitSign x = x / unitMagnitude x := rfl

@[simp]
theorem unitSign_val (x : ℝˣ) : (unitSign x : ℝ) = (x : ℝ) / |(x : ℝ)| := by
  rw [unitSign_eq_div, Units.val_div_eq_div_val, unitMagnitude_val]

/-- Every real unit has one of the two genuine signs. -/
theorem unitSign_cases (x : ℝˣ) : unitSign x = 1 ∨ unitSign x = -1 := by
  rcases lt_or_gt_of_ne (Units.ne_zero x) with hneg | hpos
  · right
    apply Units.ext
    rw [unitSign_val]
    change (x : ℝ) / |(x : ℝ)| = -1
    rw [abs_of_neg hneg, div_neg, div_self (Units.ne_zero x)]
  · left
    apply Units.ext
    rw [unitSign_val]
    change (x : ℝ) / |(x : ℝ)| = 1
    rw [abs_of_pos hpos, div_self (Units.ne_zero x)]

@[simp]
theorem unitSign_realSign (a : ZMod 2) : unitSign (realSign a) = realSign a := by
  unfold realSign
  split_ifs
  · exact map_one unitSign
  · apply Units.ext
    rw [unitSign_val]
    change (-1 : ℝ) / |(-1 : ℝ)| = -1
    norm_num

@[simp]
theorem unitLog_realSign (a : ZMod 2) : unitLog (realSign a) = 1 := by
  change Real.log ((realSign a : ℝˣ) : ℝ) = 0
  unfold realSign
  split_ifs <;> simp

/-! Two checks distinguish the sign from the positive size. -/

example : unitSign (Units.mk0 (2 : ℝ) (by norm_num)) = 1 := by
  apply Units.ext
  rw [unitSign_val]
  change (2 : ℝ) / |2| = 1
  norm_num

example : unitSign (Units.mk0 (-2 : ℝ) (by norm_num)) = -1 := by
  apply Units.ext
  rw [unitSign_val]
  change (-2 : ℝ) / |-2| = -1
  norm_num

end RMod.Classification
