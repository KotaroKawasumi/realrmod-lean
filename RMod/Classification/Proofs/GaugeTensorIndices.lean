import RMod.Classification.Abstract.Parameters
import Mathlib.Algebra.CharP.Two

/-!
# The forced indices and parity total in a gauge tensor block

The inverse group isomorphism carries the target complementary degree
to the source complementary degree. The binary gauge equation equates
the two ordered words of right parity factors used by the tensorator.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem gaugeComplementaryIndex {s t : TwistData} (d : GaugeData s t) (k l : t.group) :
    d.phi.symm (l⁻¹ * k) = (d.phi.symm l)⁻¹ * d.phi.symm k := by
  rw [map_mul, map_inv]

theorem gaugeParityTotal {s t : TwistData} (d : GaugeData s t)
    (hν : ∀ g h, t.nu (d.phi g) (d.phi h) = s.nu g h + d.lam h + d.lam (g * h) + d.lam g)
    (g h : s.group) :
    (d.lam g + d.lam h) + t.nu (d.phi g) (d.phi h) = s.nu g h + d.lam (g * h) := by
  rw [hν]
  calc
    _ = (s.nu g h + d.lam (g * h)) + (d.lam g + d.lam g) + (d.lam h + d.lam h) := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, add_zero]

theorem gaugeIndexedParityTotal {s t : TwistData} (d : GaugeData s t)
    (hν : ∀ g h, t.nu (d.phi g) (d.phi h) = s.nu g h + d.lam h + d.lam (g * h) + d.lam g)
    (k l : t.group) :
    (d.lam (d.phi.symm l) + d.lam (d.phi.symm (l⁻¹ * k))) + t.nu l (l⁻¹ * k) =
      s.nu (d.phi.symm l) (d.phi.symm (l⁻¹ * k)) + d.lam (d.phi.symm k) := by
  have h := gaugeParityTotal d hν (d.phi.symm l) (d.phi.symm (l⁻¹ * k))
  simpa only [d.phi.apply_symm_apply, ← map_mul, mul_inv_cancel_left] using h

end RMod.Classification
