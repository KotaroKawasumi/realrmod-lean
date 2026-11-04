import RMod.Classification.Abstract.Parameters
import RMod.Classification.Proofs.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Admissibility and the duality scalar

The scalar required by the second snake identity follows from the
four-variable pentagon at `(g⁻¹,g,g⁻¹,g)`. These statements concern actual
real units, without a finite sign checker or native evaluation.
-/

set_option autoImplicit false

namespace RMod.Classification

namespace TwistLaws

variable {d : TwistData} (h : TwistLaws d)

include h

/-- The two normalizers have the same total parity, by the actual cocycle
equation. This discharges the equality parameter in `localAssociator`. -/
theorem normalizer_parity (g h' k : d.group) :
    d.nu g h' + d.nu (g * h') k = d.nu h' k + d.nu g (h' * k) := by
  have hc := h.cocycle g h' k
  have hsum : (d.nu g h' + d.nu (g * h') k) +
      (d.nu h' k + d.nu g (h' * k)) = 0 := by
    calc
      _ = d.nu h' k + d.nu (g * h') k + d.nu g (h' * k) + d.nu g h' := by abel
      _ = 0 := hc
  have he := congrArg (fun x => x + (d.nu h' k + d.nu g (h' * k))) hsum
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at he
  exact he

/-- Left- and right-inverse binary parity shifts agree. -/
theorem inverse_parity (g : d.group) : d.nu g g⁻¹ = d.nu g⁻¹ g := by
  have he := h.normalizer_parity g g⁻¹ g
  simpa only [mul_inv_cancel, inv_mul_cancel, h.nu_one_left, h.nu_one_right, add_zero] using he

/-- The scalar relation needed for the second snake; checking just the
first snake would not establish this independent consequence. -/
theorem snake_scalar (g : d.group) :
    d.omega g⁻¹ g g⁻¹ * d.omega g g⁻¹ g =
      realSign (d.nu g g⁻¹) := by
  have he := h.pentagon g g⁻¹ g g⁻¹
  have hs : d.nu g g⁻¹ * d.nu g g⁻¹ = d.nu g g⁻¹ := by
    rcases parity_cases (d.nu g g⁻¹) with hz | ho
    · rw [hz, zero_mul]
    · rw [ho, one_mul]
  simpa only [inv_mul_cancel, mul_inv_cancel, h.omega_one₁, h.omega_one₂,
    h.omega_one₃, mul_one, hs] using he

/-- The real obstruction on an involution is substantive: a normalized
binary odd shift at `(g,g)` cannot satisfy the scalar pentagon. -/
theorem involution_parity_zero (g : d.group) (hg : g * g = 1) :
    d.nu g g = 0 := by
  rcases parity_cases (d.nu g g) with hz | ho
  · exact hz
  · have he := h.pentagon g g g g
    simp only [hg, h.omega_one₁, h.omega_one₂, h.omega_one₃, ho,
      mul_one, realSign, if_neg one_ne_zero] at he
    have hv := congrArg (fun x : ℝˣ => x.val) he
    change (d.omega g g g).val * (d.omega g g g).val = -1 at hv
    have hn := mul_self_nonneg (d.omega g g g).val
    rw [hv] at hn
    norm_num at hn

end TwistLaws
end RMod.Classification
