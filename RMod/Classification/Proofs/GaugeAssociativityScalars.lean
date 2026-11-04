import RMod.Classification.Proofs.WeightedPentagon
import RMod.Classification.Proofs.ParityPowers

/-!
# The two triple-route signs give the prescribed gauge exponent

The two binary parity equations cancel the auxiliary component parities.
The remaining exponent is exactly nu-prime cup lambda plus lambda cup
nu, with the order fixed in the manuscript and the public interface.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem gaugeTriple_sign (a b c d e n r n' r' : ZMod 2)
    (h₁ : (a + b) + n' = n + d) (h₂ : (b + c) + r' = r + e) :
    (a * b + d * c + c * n) + (b * c + a * e + a * r') = n' * c + a * r := by
  have hn := congrArg (fun x => (a + b) + x) h₁
  have hr := congrArg (fun x => (b + c) + x) h₂
  simp only [CharTwo.add_cancel_left] at hn hr
  rw [hn, hr]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem gaugeTriple_scalar (a b c d e n r n' r' : ZMod 2)
    (h₁ : (a + b) + n' = n + d) (h₂ : (b + c) + r' = r + e)
    (beta₁ beta₂ beta₃ beta₄ omega omega' : ℝˣ)
    (hw : omega' = omega * (beta₂ * beta₁) * (beta₃ * beta₄)⁻¹ * realSign (n' * c + a * r)) :
    omega.val * (beta₁.val * beta₂.val * (-1 : ℝ) ^ (a * b + d * c + c * n).val) =
      (beta₃.val * beta₄.val * (-1 : ℝ) ^ (b * c + a * e + a * r').val) * omega'.val := by
  have he : omega' * (beta₃ * beta₄) = omega * (beta₂ * beta₁) * realSign (n' * c + a * r) := by
    calc
      _ = (omega * (beta₂ * beta₁)) * ((beta₃ * beta₄)⁻¹ * (beta₃ * beta₄)) *
          realSign (n' * c + a * r) := by rw [hw]; ac_rfl
      _ = _ := by rw [inv_mul_cancel, mul_one]
  have hv := congrArg Units.val he
  simp only [Units.val_mul, realSign_coe] at hv
  have hs : (-1 : ℝ) ^ (n' * c + a * r).val * (-1 : ℝ) ^ (b * c + a * e + a * r').val =
      (-1 : ℝ) ^ (a * b + d * c + c * n).val := by
    rw [← gaugeTriple_sign a b c d e n r n' r' h₁ h₂,
      parity_power_add, mul_assoc, parity_power_mul_self, mul_one]
  calc
    _ = (omega.val * (beta₂.val * beta₁.val)) *
        ((-1 : ℝ) ^ (n' * c + a * r).val * (-1 : ℝ) ^ (b * c + a * e + a * r').val) := by
      rw [hs]
      ring
    _ = (omega'.val * (beta₃.val * beta₄.val)) * (-1 : ℝ) ^ (b * c + a * e + a * r').val := by
      rw [hv]
      ring
    _ = _ := by ring

end RMod.Classification
