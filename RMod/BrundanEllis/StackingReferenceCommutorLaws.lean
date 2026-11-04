import RMod.BrundanEllis.StackingReferenceCommutorCertificates

/-! Algebraic interpretation of the finite integer certificates. In particular,
the inverse denominator is proved nonzero before it is inverted. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

/-- Extension of scalars turns the stored inverse numerator into an inverse. -/
theorem inverse_forward (a b : ZMod 8) :
    inverse a b * forward a b = 1 ∧ forward a b * inverse a b = 1 := by
  have hd : (denominator a b : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (denominator_pos a b)
  have hL : (inverseNumeratorZ a b).map ((↑) : ℤ → ℚ) *
      (forwardZ a b).map ((↑) : ℤ → ℚ) = (denominator a b : ℚ) • 1 := by
    ext i j
    have h := congrArg ((↑) : ℤ → ℚ)
      (congrFun (congrFun (inverse_numerator a b).1 i) j)
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, apply_ite] using h
  have hR : (forwardZ a b).map ((↑) : ℤ → ℚ) *
      (inverseNumeratorZ a b).map ((↑) : ℤ → ℚ) = (denominator a b : ℚ) • 1 := by
    ext i j
    have h := congrArg ((↑) : ℤ → ℚ)
      (congrFun (congrFun (inverse_numerator a b).2 i) j)
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, apply_ite] using h
  constructor
  · rw [inverse, forward, Matrix.smul_mul, hL, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · rw [inverse, forward, Matrix.mul_smul, hR, smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- Scalar extension and the nonzero inverse scale preserve homogeneous support. -/
theorem matrix_parity (a b : ZMod 8) :
    (∀ r s, forward a b r s ≠ 0 → parity b a r = parity a b s + degree a b) ∧
    (∀ r s, inverse a b r s ≠ 0 → parity a b r = parity b a s + degree a b) := by
  constructor
  · intro r s h
    apply (matrix_parityZ a b).1 r s
    intro hz
    exact h (by simp [forward, hz])
  · intro r s h
    apply (matrix_parityZ a b).2 r s
    intro hz
    exact h (by simp [inverse, Matrix.smul_apply, hz])

/-- First-slot naturality after extension from integers to rationals. -/
theorem left_naturality (a b : ZMod 8) (k : Fin (Superfusion.realRepDim a.val)) :
    forward a b * leftAction a b k =
      ((-1 : ℚ) ^ (degree a b * Superfusion.realRepBasisParity a k).val) •
        (rightAction b a k * forward a b) := by
  ext i j
  have h := congrArg ((↑) : ℤ → ℚ) (congrFun (congrFun (left_naturalityZ a b k) i) j)
  simpa [forward, leftAction, rightAction, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] using h

/-- Second-slot naturality after the same extension of scalars. -/
theorem right_naturality (a b : ZMod 8) (k : Fin (Superfusion.realRepDim b.val)) :
    forward a b * rightAction a b k =
      ((-1 : ℚ) ^ (degree a b * Superfusion.realRepBasisParity b k).val) •
        (leftAction b a k * forward a b) := by
  ext i j
  have h := congrArg ((↑) : ℤ → ℚ) (congrFun (congrFun (right_naturalityZ a b k) i) j)
  simpa [forward, leftAction, rightAction, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] using h

end RMod.BrundanEllis.Stacking.ReferenceCommutor
