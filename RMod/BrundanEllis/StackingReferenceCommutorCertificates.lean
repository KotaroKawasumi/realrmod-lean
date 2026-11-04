import RMod.BrundanEllis.StackingReferenceCommutorData

/-! Finite integer certificates for the exchange matrices. Ordinary Lean kernel
reduction checks these closed identities. Scalar extension and inversion of the
positive integer scale are handled by algebra in the subsequent laws module. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

theorem denominator_pos (a b : ZMod 8) : 0 < denominator a b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- Two-sided inverse numerators, verified in integers. -/
theorem inverse_numerator (a b : ZMod 8) :
    inverseNumeratorZ a b * forwardZ a b = (denominator a b : ℤ) • 1 ∧
      forwardZ a b * inverseNumeratorZ a b = (denominator a b : ℤ) • 1 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- Both maps have the required homogeneous support. -/
theorem matrix_parityZ (a b : ZMod 8) :
    (∀ r s, forwardZ a b r s ≠ 0 → parity b a r = parity a b s + degree a b) ∧
    (∀ r s, inverseNumeratorZ a b r s ≠ 0 → parity a b r = parity b a s + degree a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- The first input action intertwines with its reversed slot. -/
theorem left_naturalityZ (a b : ZMod 8) :
    ∀ k, forwardZ a b * leftActionZ a b k =
      ((-1 : ℤ) ^ (degree a b * Superfusion.realRepBasisParity a k).val) •
        (rightActionZ b a k * forwardZ a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- The second input action intertwines as well. -/
theorem right_naturalityZ (a b : ZMod 8) :
    ∀ k, forwardZ a b * rightActionZ a b k =
      ((-1 : ℤ) ^ (degree a b * Superfusion.realRepBasisParity b k).val) •
        (leftActionZ b a k * forwardZ a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor
