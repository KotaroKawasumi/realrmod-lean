import RMod.Classification.Proofs.GaugeIndexedScalarCoherence
import RMod.Classification.Proofs.GaugeRawRatioScalars
import RMod.Classification.Proofs.EquivalenceGaugeData
import RMod.Classification.Proofs.GaugeTensorIndices

/-!
# Every monoidal equivalence forces the omega gauge equation

Evaluate the actual triple coherence on the chosen nonzero simple in
each group component. Faithfulness removes the common evaluation map.
The four binary ratios give the coboundary, and their verified normalizer
signs give precisely the cup-product sign in the public gauge law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem equivalenceGaugeRatio_raw_omega (g h k : s.data.group) :
    let phi := equivalenceGaugePhi C hC s t E
    let lam := equivalenceGaugeLambda C hC s t E
    let r := equivalenceGaugeRatio C hC s t E
    t.data.omega (phi g) (phi h) (phi k) =
      s.data.omega g h k * (r h k * r g (h * k)) * (r g h * r (g * h) k)⁻¹ *
        realSign (s.data.nu g h * s.data.nu (g * h) k + s.data.nu h k * s.data.nu g (h * k) +
          t.data.nu (phi g) (phi h) * t.data.nu (phi (g * h)) (phi k) +
          t.data.nu (phi h) (phi k) * t.data.nu (phi g) (phi (h * k)) +
          lam g * s.data.nu h k + lam k * t.data.nu (phi g) (phi h)) := by
  let A := (twistedPullback C hC s).toWeaklyPointedSuperfusion
  let X := spanGenerator A (pullbackDegreeSimple C hC s g).data.object
  let Y := spanGenerator A (pullbackDegreeSimple C hC s h).data.object
  let Z := spanGenerator A (pullbackDegreeSimple C hC s k).data.object
  have he := equivalenceIndexedComparison_scalar_coherence C hC s t E g h k (g * h) (h * k)
    ((g * h) * k) rfl rfl rfl (mul_assoc g h k).symm X Y Z
    (simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws (pullbackDegreeSimple_coordinate C hC s g))
    (simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws (pullbackDegreeSimple_coordinate C hC s h))
    (simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws (pullbackDegreeSimple_coordinate C hC s k))
  exact gaugeRawRatio_of_coherence _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he

theorem equivalenceUnnormalizedGaugeData_omega (g h k : s.data.group) :
    let d := equivalenceUnnormalizedGaugeData C hC s t E
    t.data.omega (d.phi g) (d.phi h) (d.phi k) =
      s.data.omega g h k * (d.beta (g * h) k * d.beta g h) *
        (d.beta h k * d.beta g (h * k))⁻¹ *
        realSign (t.data.nu (d.phi g) (d.phi h) * d.lam k + d.lam g * s.data.nu h k) := by
  let d := equivalenceUnnormalizedGaugeData C hC s t E
  have hn := gaugeParityTotal d (equivalenceUnnormalizedGaugeData_nu C hC s t E)
  have h₂ := hn (g * h) k
  have h₄ := hn g (h * k)
  rw [← mul_assoc] at h₄
  have he := gaugeComparisonRatio_omega
    (d.lam g) (d.lam h) (d.lam k) (d.lam (g * h)) (d.lam (h * k)) (d.lam ((g * h) * k))
    (s.data.nu g h) (s.data.nu (g * h) k) (s.data.nu h k) (s.data.nu g (h * k))
    (t.data.nu (d.phi g) (d.phi h)) (t.data.nu (d.phi (g * h)) (d.phi k))
    (t.data.nu (d.phi h) (d.phi k)) (t.data.nu (d.phi g) (d.phi (h * k)))
    (s.laws.normalizer_parity g h k) (hn g h) h₂ (hn h k) h₄
    (equivalenceGaugeRatio C hC s t E g h) (equivalenceGaugeRatio C hC s t E (g * h) k)
    (equivalenceGaugeRatio C hC s t E h k) (equivalenceGaugeRatio C hC s t E g (h * k))
    (s.data.omega g h k) (t.data.omega (d.phi g) (d.phi h) (d.phi k))
    (equivalenceGaugeRatio_raw_omega C hC s t E g h k)
  simpa only [d, equivalenceUnnormalizedGaugeData, mul_assoc] using he

end RMod.Classification
