import RMod.Classification.Proofs.Parameters

/-! # The source parity cocycle in target product coordinates -/

set_option autoImplicit false

namespace RMod.Classification

theorem gaugeSourceNormalizerParity (s t : Twist) (d : GaugeData s.data t.data) (g h k : t.data.group) :
    s.data.nu (d.phi.symm g) (d.phi.symm h) + s.data.nu (d.phi.symm (g * h)) (d.phi.symm k) =
      s.data.nu (d.phi.symm h) (d.phi.symm k) + s.data.nu (d.phi.symm g) (d.phi.symm (h * k)) := by
  simpa only [map_mul] using s.laws.normalizer_parity (d.phi.symm g) (d.phi.symm h) (d.phi.symm k)

end RMod.Classification
