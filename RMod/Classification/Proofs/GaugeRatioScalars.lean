import RMod.Classification.Proofs.GaugeRatioSigns

/-!
# From raw binary ratios to the prescribed omega gauge equation

The ratio of inverse tensorator comparisons inverts each beta. The four
normalizer signs supply precisely the discrepancy between outer-first
deletions on the source and target. The remaining two crossings are the
cup-product sign in the public classification statement.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem realSign_add (a b : ZMod 2) : realSign (a + b) = realSign a * realSign b := by
  apply Units.ext
  simp only [Units.val_mul, realSign_coe, parity_power_add]

theorem realSign_mul_self (a : ZMod 2) : realSign a * realSign a = 1 := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_one, realSign_coe, parity_power_mul_self]

theorem realSign_inv (a : ZMod 2) : (realSign a)⁻¹ = realSign a :=
  inv_eq_of_mul_eq_one_right (realSign_mul_self a)

theorem gaugeComparisonRatio_coboundary (r₁ r₂ r₃ r₄ : ℝˣ) (q₁ q₂ q₃ q₄ : ZMod 2) :
    ((r₂⁻¹ * realSign q₂) * (r₁⁻¹ * realSign q₁)) *
      ((r₃⁻¹ * realSign q₃) * (r₄⁻¹ * realSign q₄))⁻¹ =
      (r₃ * r₄) * (r₁ * r₂)⁻¹ * realSign (q₁ + q₂ + q₃ + q₄) := by
  simp only [mul_inv_rev, inv_inv, realSign_inv, realSign_add]
  ac_rfl

theorem gaugeComparisonRatio_omega (a b c d e f n m r s n' m' r' s' : ZMod 2)
    (hs : n + m = r + s)
    (h₁ : (a + b) + n' = n + d) (h₂ : (d + c) + m' = m + f)
    (h₃ : (b + c) + r' = r + e) (h₄ : (a + e) + s' = s + f)
    (r₁ r₂ r₃ r₄ omega omega' : ℝˣ)
    (hw : omega' = omega * (r₃ * r₄) * (r₁ * r₂)⁻¹ *
      realSign (n * m + r * s + n' * m' + r' * s' + a * r + c * n')) :
    omega' = omega *
      ((r₂⁻¹ * realSign (d * c + (d + c) * m' + f * m)) *
        (r₁⁻¹ * realSign (a * b + (a + b) * n' + d * n))) *
      ((r₃⁻¹ * realSign (b * c + (b + c) * r' + e * r)) *
        (r₄⁻¹ * realSign (a * e + (a + e) * s' + f * s)))⁻¹ * realSign (n' * c + a * r) := by
  rw [mul_assoc omega, gaugeComparisonRatio_coboundary,
    mul_assoc omega, mul_assoc ((r₃ * r₄) * (r₁ * r₂)⁻¹),
    ← realSign_add, gaugeComparisonRatio_sign a b c d e f n m r s n' m' r' s' hs h₁ h₂ h₃ h₄]
  have he : n * m + r * s + n' * m' + r' * s' + (n' * c + a * r) =
      n * m + r * s + n' * m' + r' * s' + a * r + c * n' := by ring
  rw [he]
  simpa only [mul_assoc] using hw

end RMod.Classification
