import RMod.Classification.Proofs.GaugeTensorIndices

/-!
# Gauge indices for a pair of specified target degrees

The second degree is retained explicitly. The source convolution still
uses the original output degree phi-inverse(g h), so its complementary
index and the output parity factor both retain their prescribed types.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem gaugeProductComplement {s t : TwistData} (d : GaugeData s t) (g h : t.group) :
    d.phi.symm h = (d.phi.symm g)⁻¹ * d.phi.symm (g * h) := by
  rw [map_mul, inv_mul_cancel_left]

theorem gaugeProductParityTotal {s t : TwistData} (d : GaugeData s t)
    (hν : ∀ g h, t.nu (d.phi g) (d.phi h) = s.nu g h + d.lam h + d.lam (g * h) + d.lam g)
    (g h : t.group) :
    (d.lam (d.phi.symm g) + d.lam (d.phi.symm h)) + t.nu g h =
      s.nu (d.phi.symm g) (d.phi.symm h) + d.lam (d.phi.symm (g * h)) := by
  simpa only [d.phi.apply_symm_apply, map_mul] using
    gaugeParityTotal d hν (d.phi.symm g) (d.phi.symm h)

end RMod.Classification
