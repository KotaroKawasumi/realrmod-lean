import RMod.Classification.Proofs.GaugeRatioScalars

/-!
# Solving the faithful triple coefficient equation

All comparison coefficients are units. Move the left binary coefficients
and the target deletion sign across the equation. Since parity signs are
self-inverse, their contributions add to the raw omega exponent.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem gaugeRawRatio_of_coherence
    (n m r s n' m' r' s' a c : ZMod 2) (r₁ r₂ r₃ r₄ omega omega' : ℝˣ)
    (he : (omega'.val * (-1 : ℝ) ^ (n' * m' + r' * s').val) *
        (r₂.val * r₁.val * (-1 : ℝ) ^ (c * n').val) =
      (r₄.val * r₃.val * (-1 : ℝ) ^ (a * r).val) *
        (omega.val * (-1 : ℝ) ^ (n * m + r * s).val)) :
    omega' = omega * (r₃ * r₄) * (r₁ * r₂)⁻¹ *
      realSign (n * m + r * s + n' * m' + r' * s' + a * r + c * n') := by
  have hu : (omega' * realSign (n' * m' + r' * s')) * (r₂ * r₁ * realSign (c * n')) =
      (r₄ * r₃ * realSign (a * r)) * (omega * realSign (n * m + r * s)) := by
    apply Units.ext
    simpa only [Units.val_mul, realSign_coe] using he
  calc
    omega' = ((r₄ * r₃ * realSign (a * r)) * (omega * realSign (n * m + r * s))) *
        (realSign (n' * m' + r' * s') * (r₂ * r₁ * realSign (c * n')))⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).mpr
      simpa only [mul_assoc] using hu
    _ = _ := by
      simp only [mul_inv_rev, realSign_inv, realSign_add]
      ac_rfl

end RMod.Classification
