import RMod.Classification.Abstract.Parameters

/-!
# Scalar normalization follows from its middle case and the pentagon

The pentagon at `(1,1,g,h)` makes `omega(1,g,h)` idempotent;
the pentagon at `(g,h,1,1)` does the same for `omega(g,h,1)`.
These are real units, so cancellation makes both equal to one. Thus
reconstruction needs only its transported triangle for the middle case.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (t : TwistData)
  (hν : t.nu 1 1 = 0)
  (hm : ∀ g h, t.omega g 1 h = 1)
  (hp : ∀ g h k l, t.omega h k l * t.omega g (h * k) l * t.omega g h k =
    realSign (t.nu g h * t.nu k l) * (t.omega (g * h) k l * t.omega g h (k * l)))

include hν hm hp

theorem omega_one_left_of_middle_pentagon (g h : t.group) : t.omega 1 g h = 1 := by
  have he := hp 1 1 g h
  simp only [one_mul, hm, hν, zero_mul, realSign, ite_true, mul_one] at he
  exact mul_right_cancel (he.trans (one_mul (t.omega 1 g h)).symm)

theorem omega_one_right_of_middle_pentagon (g h : t.group) : t.omega g h 1 = 1 := by
  have he := hp g h 1 1
  simp only [one_mul, mul_one, hm, hν, mul_zero, realSign, ite_true] at he
  exact mul_right_cancel (he.trans (one_mul (t.omega g h 1)).symm)

end RMod.Classification
