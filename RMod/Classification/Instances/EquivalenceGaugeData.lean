import RMod.Classification.Instances.EquivalenceGaugeRatio

/-!
# Gauge parameters extracted from an arbitrary equivalence

The binary ratio concerns an inverse tensorator and homogeneous component
comparisons. Invert that ratio and insert the sign of the prescribed
right-factor normalizer to obtain beta. Its common unit value will be
removed after proving the associativity equation.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def equivalenceUnnormalizedGaugeData
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) : GaugeData s.data t.data where
  phi := equivalenceGaugePhi C hC s t E
  lam := equivalenceGaugeLambda C hC s t E
  beta g h := (equivalenceGaugeRatio C hC s t E g h)⁻¹ *
    realSign (equivalenceGaugeLambda C hC s t E g * equivalenceGaugeLambda C hC s t E h +
      (equivalenceGaugeLambda C hC s t E g + equivalenceGaugeLambda C hC s t E h) *
        t.data.nu (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h) +
      equivalenceGaugeLambda C hC s t E (g * h) * s.data.nu g h)

end RMod.Classification
