/-
Superfusion: Lean 4 formalization of
"Weakly pointed fusion and superfusion categories over the real and complex
numbers: classification, stacking, and spin bordism" (Kawasumi, 2026).

This file: global sign conventions.

The paper's Appendix A fixes sign conventions (C1)–(C11), (C4′) once and for
all.  Every Koszul-sign manipulation in this project must route through the
`sgn` function of this file and cite the relevant convention in a docstring.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.Tactic

namespace Superfusion

/-- A commutative group with a distinguished 2-torsion element `sign`, the
target of the `(-1)^…` twists of Gu–Wen supercohomology.  Instances include
`Rˣ` for a commutative ring `R` (with `sign = -1`) and discrete certificate
groups such as `Multiplicative (ZMod 2 × ℤ)` encoding `± 2^ℤ`. -/
class GroupSign (M : Type*) [CommGroup M] where
  sign : M
  sign_mul_self : sign * sign = 1

export GroupSign (sign sign_mul_self)

/-- The units of a commutative ring carry the sign `-1`. -/
instance (R : Type*) [CommRing R] : GroupSign Rˣ where
  sign := -1
  sign_mul_self := by simp

@[simp] theorem units_sign_eq {R : Type*} [CommRing R] :
    (GroupSign.sign : Rˣ) = -1 := rfl

variable {M : Type*} [CommGroup M] [GroupSign M]

/-- `sgn i` is `(-1)^i` for a parity `i : ZMod 2`, valued in `M`. -/
def sgn (i : ZMod 2) : M := if i = 0 then 1 else sign

@[simp] theorem sgn_zero : (sgn 0 : M) = 1 := rfl

@[simp] theorem sgn_one : (sgn 1 : M) = sign := rfl

/-- Case analysis on parities (public: used across the project). -/
theorem zmod2_cases : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide

private theorem zmod2_sub_eq_add : ∀ i j : ZMod 2, i - j = i + j := by decide

private theorem zmod2_neg_eq : ∀ i : ZMod 2, -i = i := by decide

private theorem zmod2_one_add_one : (1 + 1 : ZMod 2) = 0 := by decide

/-- `sgn` is additive-to-multiplicative: `(-1)^(i+j) = (-1)^i * (-1)^j`. -/
theorem sgn_add (i j : ZMod 2) : (sgn (i + j) : M) = sgn i * sgn j := by
  rcases zmod2_cases i with hi | hi <;> rcases zmod2_cases j with hj | hj <;>
    simp [hi, hj, sgn, sign_mul_self, zmod2_one_add_one]

@[simp] theorem sgn_mul_self' (i : ZMod 2) : (sgn i : M) * sgn i = 1 := by
  rcases zmod2_cases i with hi | hi <;> simp [hi, sgn, sign_mul_self]

@[simp] theorem sgn_inv (i : ZMod 2) : (sgn i : M)⁻¹ = sgn i :=
  inv_eq_of_mul_eq_one_right (sgn_mul_self' i)

/-- Cancellation in right-associated products (the shape produced by
associativity-normalizing `simp`). -/
@[simp] theorem sgn_mul_sgn_mul (i : ZMod 2) (x : M) :
    (sgn i : M) * (sgn i * x) = x := by
  rw [← mul_assoc, sgn_mul_self', one_mul]

/-- Subtraction of parities is addition (characteristic 2). -/
theorem sgn_sub (i j : ZMod 2) : (sgn (i - j) : M) = sgn i * sgn j := by
  rw [zmod2_sub_eq_add, sgn_add]

theorem sgn_neg (i : ZMod 2) : (sgn (-i) : M) = sgn i := by
  rw [zmod2_neg_eq]

/-- `sgn` as a monoid hom from `Multiplicative (ZMod 2)`. -/
def sgnHom : Multiplicative (ZMod 2) →* M where
  toFun i := sgn i.toAdd
  map_one' := sgn_zero
  map_mul' i j := sgn_add i.toAdd j.toAdd

/-- In `ℤˣ`, our sign map agrees with mathlib's `ZMod 2`-power of `-1`
(`Mathlib.Data.ZMod.IntUnitsPower`), so the simp sets of
`GradedTensorProduct` and friends apply to `sgn`-statements. -/
theorem sgn_eq_neg_one_uzpow (i : ZMod 2) : (sgn i : ℤˣ) = (-1 : ℤˣ) ^ i := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · simp [sgn]
  · rw [show (1 : ZMod 2) = ((1 : ℕ) : ZMod 2) from by norm_num, uzpow_natCast]
    simp [sgn]

end Superfusion
